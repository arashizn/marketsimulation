#!/usr/bin/env python3
"""Market Simulation - 投资银行模拟交易系统 (纯标准库, 无需安装依赖)

运行:  python server.py [端口]      默认 8000, 管理员密码默认 admin
"""
import csv
import copy
import io
import json
import math
import os
import random
import secrets
import socket
import sys
import threading
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse

ROOT = os.path.dirname(os.path.abspath(__file__))
DATA_DIR = os.environ.get("DATA_DIR") or os.path.join(ROOT, "data")
STATE_FILE = os.path.join(DATA_DIR, "state.json")
UNDO_FILE = os.path.join(DATA_DIR, "undo.json")
LOCK = threading.RLock()
FAILS = {}  # 登录失败记录 ip -> [时间戳]
MAX_FAILS, FAIL_WINDOW = 8, 300  # 5 分钟内最多失败 8 次
SESSIONS = {}  # token -> {role, team, name}

DEFAULT_CONFIG = dict(
    title="投资银行模拟交易 Market Simulation",
    initial_cash=100_000_000, total_weeks=8, fee_rate=0.001,
    max_single=0.30, max_stock_total=0.80, max_gold=0.40, max_bond=0.70, min_cash=0.05,
    cash_rate=0.01, bond_yield=0.04,
    debt_max=0.50, cp_max=0.20, lend_max=0.50,
    rate_min=0.01, rate_max=0.20, durations=[1, 2, 4], liq_penalty=0.02,
    self_join=True,
    w_ret=30, w_risk=15, w_liq=10, w_credit=10, w_report=10, w_accounting=25,
    accounting_enabled=True, accounting_lock_trade=False,
)

# id, 名称, 类型, 行业, 模拟基准价(HKD, 仅用于生成演示价格, 可在后台改)
DEFAULT_ASSETS = [
    ("0005.HK", "汇丰控股 HSBC", "stock", "金融", 100),
    ("1299.HK", "友邦保险 AIA", "stock", "金融", 65),
    ("0388.HK", "香港交易所 HKEX", "stock", "金融", 380),
    ("2318.HK", "中国平安 Ping An", "stock", "金融", 50),
    ("0700.HK", "腾讯控股 Tencent", "stock", "科技", 520),
    ("9988.HK", "阿里巴巴 Alibaba", "stock", "科技", 120),
    ("3690.HK", "美团 Meituan", "stock", "科技", 130),
    ("1810.HK", "小米集团 Xiaomi", "stock", "科技", 55),
    ("9618.HK", "京东集团 JD", "stock", "科技", 140),
    ("9999.HK", "网易 NetEase", "stock", "科技", 190),
    ("0001.HK", "长和 CK Hutchison", "stock", "地产公用", 42),
    ("0002.HK", "中电控股 CLP", "stock", "地产公用", 60),
    ("0823.HK", "领展房产基金 Link REIT", "stock", "地产公用", 38),
    ("0016.HK", "新鸿基地产 SHKP", "stock", "地产公用", 100),
    ("1876.HK", "百威亚太 Budweiser APAC", "stock", "消费医药", 9),
    ("2269.HK", "药明生物 WuXi Bio", "stock", "消费医药", 28),
    ("2020.HK", "安踏体育 ANTA", "stock", "消费医药", 90),
    ("0291.HK", "华润啤酒 CR Beer", "stock", "消费医药", 28),
    ("0883.HK", "中国海洋石油 CNOOC", "stock", "能源", 20),
    ("0857.HK", "中国石油 PetroChina", "stock", "能源", 7),
    ("GOLD", "黄金 Gold (HKD/盎司)", "gold", "商品", 25000),
    ("TBOND", "国债 T-Bond (票息按年化收益累计)", "bond", "固定收益", 100),
]
VOL = {"stock": 0.05, "gold": 0.02, "bond": 0.0}


class ApiError(Exception):
    pass


# ----------------------------------------------------------------- 状态
def new_state():
    S = dict(
        config=copy.deepcopy(DEFAULT_CONFIG), admin_password="admin",
        assets=[dict(id=i, name=n, type=t, sector=s, base=b, enabled=True) for i, n, t, s, b in DEFAULT_ASSETS],
        prices={}, teams={}, loans=[], week=1, finished=False, seq=0,
        events=[],  # 老师每周发布的事件卡 {week, text}
    )
    generate_prices(S, seed=42)
    return S


def save():
    os.makedirs(DATA_DIR, exist_ok=True)
    tmp = STATE_FILE + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(S, f, ensure_ascii=False)
    os.replace(tmp, STATE_FILE)


def load():
    if os.path.exists(STATE_FILE):
        with open(STATE_FILE, encoding="utf-8") as f:
            st = json.load(f)
        for k, v in DEFAULT_CONFIG.items():
            st["config"].setdefault(k, v)
        st.setdefault("events", [])
        for t in st["teams"].values():
            t.setdefault("acct_classes", {})
            t.setdefault("accounting", {})
            t.setdefault("facts", {})
        return st
    return new_state()


def nid(prefix):
    S["seq"] += 1
    return f"{prefix}{S['seq']}"


def amap():
    return {a["id"]: a for a in S["assets"]}


# ----------------------------------------------------------------- 价格
def ensure_bond(st):
    c = st["config"]
    for a in st["assets"]:
        if a["type"] == "bond":
            for w in range(0, c["total_weeks"] + 1):
                p = st["prices"].setdefault(str(w), {})
                if a["id"] not in p:
                    p[a["id"]] = round(a["base"] * (1 + c["bond_yield"] / 52) ** w, 4)


def generate_prices(st, seed=None):
    rnd = random.Random(seed)
    n = st["config"]["total_weeks"]
    st["prices"] = {}
    cur = {a["id"]: float(a["base"]) for a in st["assets"]}
    for w in range(0, n + 1):
        market = rnd.gauss(0.002, 0.025)
        row = {}
        for a in st["assets"]:
            if a["type"] == "bond":
                continue
            if w > 0:
                v = VOL[a["type"]]
                beta = 0.8 if a["type"] == "stock" else -0.1
                cur[a["id"]] *= max(0.5, 1 + beta * market + rnd.gauss(0, v))
            row[a["id"]] = round(cur[a["id"]], 3 if cur[a["id"]] < 10 else 2)
        st["prices"][str(w)] = row
    ensure_bond(st)


def price_at(st, aid, w):
    for k in range(w, -1, -1):
        p = st["prices"].get(str(k), {}).get(aid)
        if p:
            return p
    for a in st["assets"]:
        if a["id"] == aid:
            return a["base"]
    return 0.0


def import_csv(st, text):
    rows = list(csv.reader(io.StringIO(text.strip())))
    if len(rows) < 2:
        raise ApiError("CSV 至少需要表头和一行数据")
    hdr = [h.strip() for h in rows[0]]
    ids = {a["id"] for a in st["assets"]}
    cnt = 0
    for r in rows[1:]:
        if not r or not r[0].strip():
            continue
        try:
            w = int(float(r[0]))
        except ValueError:
            raise ApiError(f"周次无法识别: {r[0]}")
        for h, v in zip(hdr[1:], r[1:]):
            if h in ids and v.strip():
                try:
                    p = float(v)
                except ValueError:
                    raise ApiError(f"价格无法识别: {h} 第{w}周 = {v}")
                if p <= 0:
                    raise ApiError(f"价格必须为正: {h} 第{w}周")
                st["prices"].setdefault(str(w), {})[h] = p
                cnt += 1
    return cnt


# ----------------------------------------------------------------- 账户估值
def accrued(l, w):
    elapsed = min(max(w - l["start"], 0), l["weeks"])
    return l["principal"] * l["rate"] * elapsed / 52


def acct(t, w):
    am = amap()
    v = {"stock": 0.0, "gold": 0.0, "bond": 0.0}
    for aid, q in t["holdings"].items():
        if q and aid in am:
            v[am[aid]["type"]] += q * price_at(S, aid, w)
    recv = pay = 0.0
    for l in S["loans"]:
        if l["status"] != "active":
            continue
        val = l["principal"] + accrued(l, w)
        if l["lender"] == t["id"]:
            recv += val
        if l["borrower"] == t["id"]:
            pay += val
    nav = t["cash"] + sum(v.values()) + recv - pay
    return dict(nav=nav, cash=t["cash"], stock=v["stock"], gold=v["gold"], bond=v["bond"], recv=recv, pay=pay)


def new_team(name, code=None, members=None):
    c = S["config"]
    tid = nid("T")
    t = dict(id=tid, name=name, code=code or secrets.token_hex(3).upper(), members=members or [],
             cash=float(c["initial_cash"]), holdings={}, cost={}, orders=[], reports={},
             acct_classes={}, accounting={}, facts={}, defaults=0, forced=0, hist=[])
    t["hist"].append(dict(week=max(S["week"] - 1, 0), **acct(t, max(S["week"] - 1, 0))))
    S["teams"][tid] = t
    return t


# ----------------------------------------------------------------- 交易规则
def limits_violation(t, aid, w):
    """在当前(已应用买入后的)持仓下检查限制, 返回违规说明或 None."""
    c = S["config"]
    a = acct(t, w)
    nav = a["nav"]
    if nav <= 0:
        return "净资产不为正"
    am = amap()
    typ = am[aid]["type"]
    val = t["holdings"].get(aid, 0) * price_at(S, aid, w)
    if a["cash"] / nav < c["min_cash"] - 1e-9:
        return f"现金占比将低于 {c['min_cash']:.0%}"
    if typ == "stock":
        if val / nav > c["max_single"] + 1e-9:
            return f"单只股票将超过净资产 {c['max_single']:.0%}"
        if a["stock"] / nav > c["max_stock_total"] + 1e-9:
            return f"股票总仓位将超过净资产 {c['max_stock_total']:.0%}"
    if typ == "gold" and a["gold"] / nav > c["max_gold"] + 1e-9:
        return f"黄金将超过净资产 {c['max_gold']:.0%}"
    if typ == "bond" and a["bond"] / nav > c["max_bond"] + 1e-9:
        return f"国债将超过净资产 {c['max_bond']:.0%}"
    return None


def exec_sell(t, o, w):
    p = price_at(S, o["asset"], w)
    have = t["holdings"].get(o["asset"], 0)
    if o["qty"] > have:
        return reject(o, f"持仓不足 (持有 {have})")
    fee = o["qty"] * p * S["config"]["fee_rate"]
    t["cash"] += o["qty"] * p - fee
    t["holdings"][o["asset"]] = have - o["qty"]
    fill(o, p, fee)


def exec_buy(t, o, w):
    p = price_at(S, o["asset"], w)
    fee = o["qty"] * p * S["config"]["fee_rate"]
    cost = o["qty"] * p + fee
    if cost > t["cash"] + 1e-9:
        return reject(o, f"现金不足 (需 {cost:,.0f}, 有 {t['cash']:,.0f})")
    old_q, old_c = t["holdings"].get(o["asset"], 0), t["cost"].get(o["asset"], 0)
    t["cash"] -= cost
    t["holdings"][o["asset"]] = old_q + o["qty"]
    viol = limits_violation(t, o["asset"], w)
    if viol:  # 回滚
        t["cash"] += cost
        t["holdings"][o["asset"]] = old_q
        return reject(o, viol)
    t["cost"][o["asset"]] = (old_q * old_c + o["qty"] * p) / (old_q + o["qty"])
    fill(o, p, fee)


def reject(o, note):
    o["status"], o["note"] = "rejected", note


def fill(o, p, fee):
    o["status"], o["price"], o["fee"] = "filled", p, fee


def force_liquidate(t, need, w):
    """卖出资产筹集 need 现金 (含手续费和罚金), 返回是否已有足够现金."""
    c = S["config"]
    am = amap()
    eff = 1 - c["fee_rate"] - c["liq_penalty"]
    order = {"bond": 0, "gold": 1, "stock": 2}
    items = [(aid, q) for aid, q in t["holdings"].items() if q > 0 and aid in am]
    items.sort(key=lambda x: (order[am[x[0]]["type"]], -x[1] * price_at(S, x[0], w)))
    t["forced"] += 1
    for aid, q in items:
        if t["cash"] >= need:
            break
        p = price_at(S, aid, w)
        k = min(q, math.ceil((need - t["cash"]) / (p * eff)))
        t["cash"] += k * p * eff
        t["facts"].setdefault(str(w), {}).setdefault("liq", []).append(
            dict(asset=aid, qty=k, price=p, fee=k * p * c["fee_rate"], penalty=k * p * c["liq_penalty"]))
        t["holdings"][aid] = q - k
    return t["cash"] >= need - 1e-6


def settle_week():
    c = S["config"]
    w = S["week"]
    if S["finished"]:
        raise ApiError("游戏已结束")
    ensure_bond(S)
    missing = [a["id"] for a in S["assets"] if a["enabled"] and not S["prices"].get(str(w), {}).get(a["id"])]
    if missing:
        raise ApiError(f"第 {w} 周缺少价格: {', '.join(missing[:6])}{'...' if len(missing) > 6 else ''}")
    os.makedirs(DATA_DIR, exist_ok=True)
    with open(UNDO_FILE, "w", encoding="utf-8") as f:
        json.dump(S, f, ensure_ascii=False)
    teams = list(S["teams"].values())
    for t in teams:  # 现金利息
        interest = t["cash"] * c["cash_rate"] / 52
        t["cash"] += interest
        t["facts"].setdefault(str(w), {})["interest"] = interest
    for t in teams:  # 先卖
        for o in t["orders"]:
            if o["week"] == w and o["status"] == "pending" and o["side"] == "sell":
                exec_sell(t, o, w)
    for l in S["loans"]:  # 还款
        if l["status"] == "pending":
            l["status"] = "expired"
        if l["status"] == "active" and l["due"] <= w:
            b, k = S["teams"][l["borrower"]], S["teams"][l["lender"]]
            due = l["principal"] + l["principal"] * l["rate"] * l["weeks"] / 52
            if b["cash"] < due - 1e-6:
                force_liquidate(b, due, w)
            pay = min(b["cash"], due)
            b["cash"] -= pay
            k["cash"] += pay
            l["paid"] = pay
            if pay < due - 1e-6:
                l["status"], l["loss"] = "defaulted", due - pay
                b["defaults"] += 1
            else:
                l["status"] = "repaid"
    for t in teams:  # 后买
        for o in t["orders"]:
            if o["week"] == w and o["status"] == "pending" and o["side"] == "buy":
                exec_buy(t, o, w)
    for t in teams:
        t["hist"].append(dict(week=w, **acct(t, w)))
    if w >= c["total_weeks"]:
        S["finished"] = True
    else:
        S["week"] = w + 1


def undo_settle():
    global S
    if not os.path.exists(UNDO_FILE):
        raise ApiError("没有可撤销的结算")
    with open(UNDO_FILE, encoding="utf-8") as f:
        S = json.load(f)
    os.remove(UNDO_FILE)


def reset_game(full=False):
    keep = S["teams"]
    S["week"], S["finished"], S["loans"] = 1, False, []
    S["teams"] = {}
    if os.path.exists(UNDO_FILE):
        os.remove(UNDO_FILE)
    if not full:
        for t in keep.values():
            nt = new_team(t["name"], t["code"], t["members"])
            S["teams"].pop(nt["id"])
            nt["id"] = t["id"]
            S["teams"][t["id"]] = nt


# ----------------------------------------------------------------- 借贷
def loan_check(l):
    c = S["config"]
    w = max(S["week"] - 1, 0)
    b, k = S["teams"][l["borrower"]], S["teams"][l["lender"]]
    ab, ak = acct(b, w), acct(k, w)
    p = l["principal"]
    if k["cash"] < p:
        return "出借方现金不足"
    if ak["nav"] <= 0 or (k["cash"] - p) / ak["nav"] < c["min_cash"] - 1e-9:
        return f"放款后出借方现金将低于净资产 {c['min_cash']:.0%}"
    if ab["nav"] <= 0 or (ab["pay"] + p) > c["debt_max"] * ab["nav"] + 1e-6:
        return f"借款方总负债将超过其净资产 {c['debt_max']:.0%}"
    act = [x for x in S["loans"] if x["status"] == "active" and x["lender"] == k["id"]]
    if sum(x["principal"] for x in act if x["borrower"] == b["id"]) + p > c["cp_max"] * ak["nav"] + 1e-6:
        return f"对同一借款方放贷将超过出借方净资产 {c['cp_max']:.0%}"
    if sum(x["principal"] for x in act) + p > c["lend_max"] * ak["nav"] + 1e-6:
        return f"总放贷将超过出借方净资产 {c['lend_max']:.0%}"
    return None


# ----------------------------------------------------------------- 评分
def scoreboard():
    c = S["config"]
    rows = []
    for t in S["teams"].values():
        h = t["hist"]
        navs = [x["nav"] for x in h]
        init = navs[0] if navs else c["initial_cash"]
        cur = navs[-1] if navs else init
        rets = [navs[i] / navs[i - 1] - 1 for i in range(1, len(navs)) if navs[i - 1] > 0]
        peak, mdd = 0, 0
        for n in navs:
            peak = max(peak, n)
            if peak > 0:
                mdd = max(mdd, (peak - n) / peak)
        vol = 0.0
        if len(rets) > 1:
            m = sum(rets) / len(rets)
            vol = math.sqrt(sum((r - m) ** 2 for r in rets) / (len(rets) - 1))
        low = sum(1 for x in h if x["week"] >= 1 and x["nav"] > 0 and x["cash"] / x["nav"] < c["min_cash"] - 1e-9)
        settled = max(len(h) - 1, 0)
        grades = [r.get("grade") for r in t["reports"].values() if r.get("grade") is not None]
        agr = [r.get("grade") for r in t["accounting"].values() if r.get("grade") is not None]
        rows.append(dict(
            id=t["id"], name=t["name"], nav=cur, ret=cur / init - 1 if init else 0, mdd=mdd, vol=vol,
            defaults=t["defaults"], forced=t["forced"], low_cash=low, settled=settled,
            s_risk=0.5 * 100 * (1 - min(mdd / 0.2, 1)) + 0.5 * 100 * (1 - min(vol / 0.05, 1)),
            s_liq=max(0, 100 - 20 * low - 25 * t["forced"]),
            s_credit=max(0, 100 - 50 * t["defaults"]),
            s_report=sum(grades) / max(settled, 1) if grades else 0,
            s_accounting=sum(agr) / max(settled, 1) if agr else 0,
        ))
    if rows:
        lo, hi = min(r["ret"] for r in rows), max(r["ret"] for r in rows)
        for r in rows:
            r["s_ret"] = 50 if hi - lo < 1e-12 else 100 * (r["ret"] - lo) / (hi - lo)
            ws = [c["w_ret"], c["w_risk"], c["w_liq"], c["w_credit"], c["w_report"],
                  c["w_accounting"] if c["accounting_enabled"] else 0]
            sc = [r["s_ret"], r["s_risk"], r["s_liq"], r["s_credit"], r["s_report"], r["s_accounting"]]
            r["score"] = sum(a * b for a, b in zip(ws, sc)) / max(sum(ws), 1e-9)
    rows.sort(key=lambda r: -r["nav"])
    for i, r in enumerate(rows):
        r["rank"] = i + 1
    return rows


# ----------------------------------------------------------------- 视图
def team_view(t):
    d = {k: t[k] for k in ("id", "name", "code", "members", "cash", "holdings", "cost", "orders", "reports",
                           "defaults", "forced", "hist")}
    d["acct_classes"] = t["acct_classes"]
    d["accounting"] = {w: {k: v for k, v in r.items() if k not in ("journals", "statements", "closing")}
                       for w, r in t["accounting"].items()}
    d["acct"] = acct(t, max(S["week"] - 1, 0) if not S["finished"] else S["config"]["total_weeks"])
    d["loans"] = [l for l in S["loans"] if t["id"] in (l["lender"], l["borrower"])]
    return d


def build_state(sess):
    c = S["config"]
    admin = sess["role"] == "admin"
    upto = c["total_weeks"] if (admin or S["finished"]) else S["week"] - 1
    prices = {k: v for k, v in S["prices"].items() if int(k) <= upto}
    cfg = dict(c)
    out = dict(config=cfg, assets=S["assets"], prices=prices, week=S["week"], finished=S["finished"],
               events=[e for e in S["events"] if admin or e["week"] <= S["week"]],
               board=scoreboard() if (admin or any(len(t["hist"]) > 1 for t in S["teams"].values())) else [],
               team_names={t["id"]: t["name"] for t in S["teams"].values()},
               role=sess["role"], can_undo=os.path.exists(UNDO_FILE))
    if admin:
        out["teams"] = {tid: team_view(t) for tid, t in S["teams"].items()}
        out["loans"] = S["loans"]
        out["missing_price"] = [a["id"] for a in S["assets"] if a["enabled"] and
                                a["type"] != "bond" and not S["prices"].get(str(S["week"]), {}).get(a["id"])]
    else:
        t = S["teams"].get(sess["team"])
        if not t:
            raise ApiError("小组已被删除, 请重新登录")
        out["me"] = team_view(t)
        out["user"] = sess["name"]
    return out


# ----------------------------------------------------------------- API
def need_team(sess):
    if sess["role"] != "team":
        raise ApiError("需要小组身份")
    return S["teams"][sess["team"]]


def num(body, key, lo=None, hi=None):
    try:
        v = float(body.get(key))
    except (TypeError, ValueError):
        raise ApiError(f"参数 {key} 必须是数字")
    if lo is not None and v < lo or hi is not None and v > hi:
        raise ApiError(f"参数 {key} 超出范围")
    return v


def check_rate(ip):
    now = time.time()
    FAILS[ip] = [x for x in FAILS.get(ip, []) if now - x < FAIL_WINDOW]
    if len(FAILS[ip]) >= MAX_FAILS:
        raise ApiError("登录失败次数过多, 请 5 分钟后再试")


def api_login(sess, b, ip="-"):
    check_rate(ip)
    try:
        return _login(b)
    except ApiError:
        FAILS.setdefault(ip, []).append(time.time())
        raise


def _login(b):
    if b.get("admin"):
        if not secrets.compare_digest(str(b.get("password", "")), str(S["admin_password"])):
            raise ApiError("管理员密码错误")
        tok = secrets.token_urlsafe(16)
        SESSIONS[tok] = dict(role="admin", name="admin")
        return dict(token=tok, role="admin")
    code = str(b.get("code", "")).strip().upper()
    name = str(b.get("name", "")).strip()[:30]
    for t in S["teams"].values():
        if t["code"].upper() == code and code:
            if not name:
                raise ApiError("请输入你的姓名")
            if name not in t["members"]:
                if not S["config"]["self_join"] and t["members"]:
                    raise ApiError("你不在该小组名单中, 请联系老师")
                t["members"].append(name)
                save()
            tok = secrets.token_urlsafe(16)
            SESSIONS[tok] = dict(role="team", team=t["id"], name=name)
            return dict(token=tok, role="team")
    raise ApiError("小组口令不正确")


def api_order(sess, b):
    t = need_team(sess)
    if S["finished"]:
        raise ApiError("游戏已结束")
    c = S["config"]
    if c["accounting_enabled"] and c["accounting_lock_trade"] and S["week"] - 1 >= first_acct_week(t)             and not t["accounting"].get(str(S["week"] - 1), {}).get("closing"):
        raise ApiError("请先提交上一周的会计结账")
    am = amap()
    aid, side = b.get("asset"), b.get("side")
    if aid not in am or not am[aid]["enabled"]:
        raise ApiError("资产不可交易")
    if side not in ("buy", "sell"):
        raise ApiError("方向错误")
    qty = int(num(b, "qty", 1))
    pend = [o for o in t["orders"] if o["week"] == S["week"] and o["status"] == "pending"]
    if len(pend) >= 200:
        raise ApiError("订单过多")
    if side == "sell":
        reserved = sum(o["qty"] for o in pend if o["asset"] == aid and o["side"] == "sell")
        if qty + reserved > t["holdings"].get(aid, 0):
            raise ApiError("卖出数量超过持仓")
    t["orders"].append(dict(id=nid("O"), week=S["week"], asset=aid, side=side, qty=qty, status="pending", by=sess["name"]))
    return {}


def api_order_cancel(sess, b):
    t = need_team(sess)
    for o in t["orders"]:
        if o["id"] == b.get("id") and o["status"] == "pending" and o["week"] == S["week"]:
            t["orders"].remove(o)
            return {}
    raise ApiError("订单不存在")


def api_loan_propose(sess, b):
    t = need_team(sess)
    c = S["config"]
    if S["finished"]:
        raise ApiError("游戏已结束")
    other = S["teams"].get(b.get("counterparty"))
    if not other or other["id"] == t["id"]:
        raise ApiError("对手方无效")
    mode = b.get("mode")
    if mode not in ("lend", "borrow"):
        raise ApiError("类型错误")
    weeks = int(num(b, "weeks"))
    if weeks not in c["durations"]:
        raise ApiError(f"期限必须是 {c['durations']} 周之一")
    if S["week"] + weeks > c["total_weeks"]:
        raise ApiError("贷款将在游戏结束后到期, 请缩短期限")
    rate = num(b, "rate", c["rate_min"], c["rate_max"])
    principal = num(b, "principal", 1)
    l = dict(id=nid("L"), lender=t["id"] if mode == "lend" else other["id"],
             borrower=other["id"] if mode == "lend" else t["id"], principal=round(principal, 2),
             rate=rate, weeks=weeks, proposer=t["id"], status="pending", start=None, due=None, week=S["week"])
    S["loans"].append(l)
    return {}


def api_loan_respond(sess, b):
    t = need_team(sess)
    l = next((x for x in S["loans"] if x["id"] == b.get("id")), None)
    if not l or l["status"] != "pending":
        raise ApiError("贷款申请不存在或已处理")
    if S["finished"]:
        raise ApiError("游戏已结束")
    action = b.get("action")
    if action == "cancel":
        if l["proposer"] != t["id"]:
            raise ApiError("只有发起方可以撤销")
        l["status"] = "cancelled"
        return {}
    if t["id"] not in (l["lender"], l["borrower"]) or l["proposer"] == t["id"]:
        raise ApiError("只有对手方可以回应")
    if action == "reject":
        l["status"] = "rejected"
        return {}
    err = loan_check(l)
    if err:
        raise ApiError(err)
    k, bo = S["teams"][l["lender"]], S["teams"][l["borrower"]]
    k["cash"] -= l["principal"]
    bo["cash"] += l["principal"]
    l["status"], l["start"], l["due"] = "active", S["week"], S["week"] + l["weeks"]
    return {}


def api_report(sess, b):
    t = need_team(sess)
    text = str(b.get("text", "")).strip()[:3000]
    r = t["reports"].setdefault(str(S["week"]), {})
    r["text"], r["by"] = text, sess["name"]
    return {}


def admin_only(fn):
    def w(sess, b):
        if sess["role"] != "admin":
            raise ApiError("需要管理员权限")
        return fn(sess, b)
    return w


@admin_only
def a_config(sess, b):
    c = S["config"]
    for k, v in b.get("config", {}).items():
        if k not in DEFAULT_CONFIG:
            continue
        d = DEFAULT_CONFIG[k]
        if isinstance(d, bool):
            c[k] = bool(v)
        elif isinstance(d, list):
            c[k] = sorted({int(x) for x in v if int(x) > 0}) or d
        elif isinstance(d, str):
            c[k] = str(v)[:100]
        elif isinstance(d, (int, float)):
            c[k] = float(v) if isinstance(d, float) else int(float(v))
    pw = b.get("admin_password")
    if pw:
        S["admin_password"] = str(pw)
    ensure_bond(S)
    return {}


@admin_only
def a_team_save(sess, b):
    name = str(b.get("name", "")).strip()[:40]
    if not name:
        raise ApiError("请输入小组名称")
    members = [m.strip() for m in b.get("members", []) if m.strip()]
    if b.get("id"):
        t = S["teams"][b["id"]]
        t["name"], t["members"] = name, members
        if b.get("code"):
            t["code"] = str(b["code"]).strip().upper()
    else:
        new_team(name, (b.get("code") or "").strip().upper() or None, members)
    return {}


@admin_only
def a_team_batch(sess, b):
    n = int(num(b, "count", 1, 100))
    prefix = str(b.get("prefix") or "第")
    start = len(S["teams"])
    for i in range(n):
        new_team(f"{prefix}{start + i + 1}组" if prefix == "第" else f"{prefix}{start + i + 1}")
    return {}


@admin_only
def a_team_delete(sess, b):
    tid = b.get("id")
    if any(l["status"] == "active" and tid in (l["lender"], l["borrower"]) for l in S["loans"]):
        raise ApiError("该小组存在未结清贷款, 不能删除")
    S["teams"].pop(tid, None)
    S["loans"] = [l for l in S["loans"] if tid not in (l["lender"], l["borrower"])]
    return {}


@admin_only
def a_asset_save(sess, b):
    aid = str(b.get("id", "")).strip()
    if not aid or b.get("type") not in ("stock", "gold", "bond"):
        raise ApiError("资产代码或类型无效")
    base = num(b, "base", 0.0001)
    a = amap().get(aid)
    if not a:
        a = dict(id=aid)
        S["assets"].append(a)
    a.update(name=str(b.get("name") or aid), type=b["type"], sector=str(b.get("sector") or ""),
             base=base, enabled=bool(b.get("enabled", True)))
    ensure_bond(S)
    return {}


@admin_only
def a_prices(sess, b):
    mode = b.get("mode")
    if mode == "csv":
        return dict(count=import_csv(S, b.get("text", "")))
    if mode == "generate":
        generate_prices(S, seed=int(b["seed"]) if str(b.get("seed", "")).strip() else None)
    elif mode == "week":
        w = str(int(num(b, "week", 0, S["config"]["total_weeks"])))
        for aid, v in b.get("prices", {}).items():
            if aid in amap() and str(v).strip():
                p = float(v)
                if p <= 0:
                    raise ApiError(f"{aid} 价格必须为正")
                S["prices"].setdefault(w, {})[aid] = p
    else:
        raise ApiError("未知模式")
    return {}


@admin_only
def a_settle(sess, b):
    settle_week()
    return {}


@admin_only
def a_undo(sess, b):
    undo_settle()
    return {}


@admin_only
def a_reset(sess, b):
    reset_game(bool(b.get("full")))
    return {}


@admin_only
def a_grade(sess, b):
    t = S["teams"][b["team"]]
    r = t["reports"].setdefault(str(int(b["week"])), {})
    g = b.get("grade")
    r["grade"] = None if g in (None, "") else num(b, "grade", 0, 100)
    r["comment"] = str(b.get("comment", ""))[:500]
    return {}


@admin_only
def a_event(sess, b):
    text = str(b.get("text", "")).strip()[:500]
    w = int(num(b, "week", 1))
    S["events"] = [e for e in S["events"] if e["week"] != w]
    if text:
        S["events"].append(dict(week=w, text=text))
    return {}


# ----------------------------------------------------------------- 会计结账
CLASS_ACC = dict(FVTPL="交易性金融资产", FVOCI="FVOCI金融资产", AC="摊余成本金融资产", INVENTORY="存货-黄金")
ALLOW_ACC = dict(AC="金融资产减值准备", INVENTORY="存货跌价准备")
PL_ACCS = ("利息收入", "投资收益", "公允价值变动损益", "交易费用", "利息费用", "信用减值损失",
           "资产减值损失", "强制清算损失", "债务核销利得")
CLASS_NAMES = dict(FVTPL="FVTPL 交易性(公允价值变动计入损益)", FVOCI="FVOCI 可供出售/持有待售(变动计入其他综合收益)",
                   AC="AC 摊余成本/持有至到期", INVENTORY="INVENTORY 存货(成本与可变现净值孰低)")


def allowed_accounting_classes(a):
    return {"stock": ["FVTPL", "FVOCI"], "gold": ["FVTPL", "INVENTORY"], "bond": ["FVTPL", "FVOCI", "AC"]}.get(a["type"], ["FVTPL"])


def _amt(v, label):
    try:
        x = float(v or 0)
    except (TypeError, ValueError):
        raise ApiError(f"{label}必须是数字")
    if x < 0 or x != x:
        raise ApiError(f"{label}不能为负")
    return x


def first_acct_week(t):
    return t["hist"][0]["week"] + 1


def generate_accounting(t, week, decisions):
    """逐周重放: 以上周结账快照为期初, 用本周成交/贷款/强平记录 + 学生判断生成分录与报表."""
    w = int(week)
    am = amap()
    if w < first_acct_week(t) or not any(h["week"] == w for h in t["hist"]):
        raise ApiError("该周尚未结算, 不能做会计结账")
    dd = decisions if isinstance(decisions, dict) else {}
    dcls, dimp, decl = (dd.get(k) if isinstance(dd.get(k), dict) else {} for k in ("classes", "impair", "ecl"))
    if w > first_acct_week(t):
        prev = t["accounting"].get(str(w - 1), {})
        if not prev.get("closing"):
            raise ApiError(f"请先完成并提交第 {w - 1} 周会计结账")
        cl = prev["closing"]
        led, pos, lallow = dict(cl["ledger"]), copy.deepcopy(cl["positions"]), dict(cl["loan_allow"])
    else:
        init = t["hist"][0]["nav"]
        led, pos, lallow = {"现金": init, "实收资本": -init}, {}, {}
    oci_open = -led.get("其他综合收益", 0.0)
    open_qty = {k: p["qty"] for k, p in pos.items()}
    pl, oci, journals, warnings = {}, {}, [], []
    fa = t["facts"].get(str(w), {})
    P = lambda aid: price_at(S, aid, w)
    nm = lambda aid: am.get(aid, {}).get("name", aid)

    def je(summary, lines, asset=None):
        ls = [(l[0], round(l[1], 2), l[2] if len(l) > 2 else None) for l in lines if abs(l[1]) >= 0.005]
        if not ls:
            return
        ls.sort(key=lambda x: x[1] < 0)
        for a, x, tag in ls:
            if a in PL_ACCS:
                pl[a] = pl.get(a, 0.0) + x
            else:
                led[a] = led.get(a, 0.0) + x
            if a == "其他综合收益":
                oci[tag or "其他"] = oci.get(tag or "其他", 0.0) - x
        journals.append(dict(week=w, summary=summary, asset=asset,
                             lines=[dict(drcr="Dr" if x > 0 else "Cr", account=a, amount=abs(x)) for a, x, _ in ls]))

    def plugged(lines, acct):
        return lines + [(acct, -sum(round(l[1], 2) for l in lines))]

    # 1 现金利息
    if "interest" in fa:
        je("现金利息收入", [("现金", fa["interest"]), ("利息收入", -fa["interest"])])
    else:
        warnings.append("缺少本周现金利息记录(旧数据), 现金核对可能不符")

    # 2 AC 债券摊销(价格按票息累计 -> 利息收入)
    for aid, p in pos.items():
        if p["qty"] > 0 and p["cls"] == "AC" and am.get(aid, {}).get("type") == "bond":
            d = p["qty"] * (P(aid) - price_at(S, aid, w - 1))
            p["cost"] += d
            je(f"{nm(aid)} 摊余成本摊销确认利息", [(CLASS_ACC["AC"], d), ("利息收入", -d)], aid)

    # 3 贷款发放 / 借入
    loans = [l for l in S["loans"] if l["status"] in ("active", "repaid", "defaulted") and t["id"] in (l["lender"], l["borrower"])]

    def cpn(l):
        oid = l["borrower"] if l["lender"] == t["id"] else l["lender"]
        return S["teams"][oid]["name"] if oid in S["teams"] else "(已删除)"

    for l in loans:
        if l["start"] == w:
            if l["lender"] == t["id"]:
                je(f"向{cpn(l)}发放贷款 {l['id']}", [("贷款及应收款项", l["principal"]), ("现金", -l["principal"])])
            else:
                je(f"从{cpn(l)}借入款项 {l['id']}", [("现金", l["principal"]), ("短期借款", -l["principal"])])

    def do_sell(aid, q, price, fee, pen, forced, label):
        p = pos.get(aid)
        if not p or p["qty"] <= 0:
            warnings.append(f"{nm(aid)}: 卖出记录找不到对应持仓, 已忽略")
            return
        q = min(q, p["qty"])
        r = q / p["qty"]
        cp, fp, ap, rp = (p[k] * r for k in ("cost", "fv", "allow", "rec"))
        acc, cls = CLASS_ACC[p["cls"]], p["cls"]
        L = [("现金", q * price - fee - pen)]
        if forced or cls == "FVTPL":
            L.append(("交易费用", fee))
        if forced:
            L.append(("强制清算损失", pen))
        if cls == "FVTPL":
            L.append((acc, -(cp + fp)))
        elif cls == "FVOCI":
            L += [(acc, -(cp + fp)), ("其他综合收益", fp + rp, "处置转出")]
        else:
            L += [(acc, -cp), (ALLOW_ACC[cls], ap)]
        je(f"{label} {nm(aid)} {q:,.0f} 股 @ {price:,.2f} ({cls})", plugged(L, "投资收益"), aid)
        p["qty"] -= q
        for k, v in (("cost", cp), ("fv", fp), ("allow", ap), ("rec", rp)):
            p[k] -= v
        if p["qty"] <= 1e-9:
            p.update(qty=0, cost=0, fv=0, allow=0, rec=0)

    # 4 本周卖出
    for o in t["orders"]:
        if o["week"] == w and o["status"] == "filled" and o["side"] == "sell":
            do_sell(o["asset"], o["qty"], o["price"], o["fee"], 0, False, "卖出")

    # 5 贷款利息计提(权责发生制)
    for l in loans:
        if l["start"] < w <= l["due"]:
            i = l["principal"] * l["rate"] / 52
            if l["lender"] == t["id"]:
                je(f"计提对{cpn(l)}贷款利息 {l['id']}", [("应收利息", i), ("利息收入", -i)])
            else:
                je(f"计提应付{cpn(l)}利息 {l['id']}", [("利息费用", i), ("应付利息", -i)])

    # 6 强制清算
    for x in fa.get("liq", []):
        do_sell(x["asset"], x["qty"], x["price"], x["fee"], x["penalty"], True, "强制清算卖出")

    # 7 贷款到期还款 / 违约
    for l in loans:
        if l["due"] == w and l["status"] in ("repaid", "defaulted"):
            P0, i, paid = l["principal"], l["principal"] * l["rate"] * l["weeks"] / 52, l.get("paid", 0.0)
            if l["lender"] == t["id"]:
                al = lallow.pop(l["id"], 0.0)
                L = [("现金", paid), ("贷款损失准备", al), ("贷款及应收款项", -P0), ("应收利息", -i)]
                je(f"{cpn(l)}{'还款' if l['status'] == 'repaid' else '违约, 收回部分款项并核销坏账'} {l['id']}", plugged(L, "信用减值损失"))
            else:
                L = [("短期借款", P0), ("应付利息", i), ("现金", -paid)]
                je(f"向{cpn(l)}{'偿还借款' if l['status'] == 'repaid' else '违约, 债务按系统规则核销'} {l['id']}", plugged(L, "债务核销利得"))

    # 8 本周买入
    for o in t["orders"]:
        if not (o["week"] == w and o["status"] == "filled" and o["side"] == "buy"):
            continue
        aid = o["asset"]
        p = pos.get(aid)
        if not p or p["qty"] <= 0:
            d = dcls.get(aid) if isinstance(dcls.get(aid), dict) else {}
            cls = d.get("cls")
            if cls not in CLASS_ACC:
                cls = (t["acct_classes"].get(aid) or {}).get("class", "FVTPL")
                warnings.append(f"{nm(aid)}: 未选择会计分类, 暂按 {cls} 处理")
            p = pos[aid] = dict(qty=0, cls=cls, cost=0.0, fv=0.0, allow=0.0, rec=0.0)
            if not str(d.get("reason", "")).strip():
                warnings.append(f"{nm(aid)}: 未填写分类理由")
            a = am.get(aid)
            if a and cls not in allowed_accounting_classes(a):
                hint = "股票没有固定本金和利息现金流, 通常不能按摊余成本计量" if a["type"] == "stock" and cls == "AC" else ""
                warnings.append(f"{nm(aid)}: {a['type']} 通常不适用 {cls}(建议 {'/'.join(allowed_accounting_classes(a))}) {hint}".strip())
        cls, gross = p["cls"], o["qty"] * o["price"]
        if cls == "FVTPL":
            L = [(CLASS_ACC[cls], gross), ("交易费用", o["fee"]), ("现金", -(gross + o["fee"]))]
            p["cost"] += gross
        else:
            L = [(CLASS_ACC[cls], gross + o["fee"]), ("现金", -(gross + o["fee"]))]
            p["cost"] += gross + o["fee"]
        p["qty"] += o["qty"]
        je(f"买入 {nm(aid)} {o['qty']:,.0f} 股 @ {o['price']:,.2f} ({cls})", L, aid)

    # 9 期末公允价值变动
    for aid, p in pos.items():
        if p["qty"] <= 0:
            continue
        if p["cls"] in ("FVTPL", "FVOCI"):
            target = p["qty"] * P(aid) - p["cost"]
            d = target - p["fv"]
            if p["cls"] == "FVTPL":
                je(f"{nm(aid)} 公允价值变动", [(CLASS_ACC["FVTPL"], d), ("公允价值变动损益", -d)], aid)
            else:
                je(f"{nm(aid)} 公允价值变动(计入其他综合收益)", [(CLASS_ACC["FVOCI"], d), ("其他综合收益", -d, "公允价值变动")], aid)
            p["fv"] = target
        elif p["cls"] == "AC" and am.get(aid, {}).get("type") != "bond":
            warnings.append(f"{nm(aid)}: 按摊余成本计量, 不确认市价变动(与系统净资产会有差异)")

    # 10 学生的减值判断 (先收集表单上下文, 再处理)
    ctx_assets = []
    for aid, p in pos.items():
        a = am.get(aid, {})
        bought = sum(o["qty"] for o in t["orders"] if o["week"] == w and o["status"] == "filled" and o["side"] == "buy" and o["asset"] == aid)
        sold = sum(o["qty"] for o in t["orders"] if o["week"] == w and o["status"] == "filled" and o["side"] == "sell" and o["asset"] == aid) \
            + sum(x["qty"] for x in fa.get("liq", []) if x["asset"] == aid)
        if p["qty"] <= 0 and not bought and not sold:
            continue
        mv = p["qty"] * P(aid)
        ctx_assets.append(dict(id=aid, name=a.get("name", aid), type=a.get("type"), qty_open=open_qty.get(aid, 0), bought=bought, sold=sold,
                               qty=p["qty"], cls=p["cls"], locked=open_qty.get(aid, 0) > 0, allowed=allowed_accounting_classes(a) if a else [],
                               price=P(aid), cost=p["cost"] - p["allow"], carrying=p["cost"] + p["fv"] - p["allow"] - p["rec"], mv=mv,
                               unrealized=mv - (p["cost"] - p["allow"]), allow=p["allow"]))
    for aid, d in dimp.items():
        d = d if isinstance(d, dict) else {}
        amt = _amt(d.get("amount"), f"{nm(aid)} 减值金额")
        if amt < 0.005:
            continue
        p = pos.get(aid)
        if not p or p["qty"] <= 0:
            warnings.append(f"{nm(aid)}: 期末无持仓, 减值已忽略")
            continue
        if not str(d.get("reason", "")).strip():
            warnings.append(f"{nm(aid)}: 未填写减值理由")
        mv = p["qty"] * P(aid)
        loss = max(0.0, (p["cost"] - p["allow"]) - mv)
        if amt > loss + 0.5:
            warnings.append(f"{nm(aid)}: 计提 {amt:,.0f} 超过未实现损失 {loss:,.0f}, 请确认依据")
        cls = p["cls"]
        if cls == "FVTPL":
            warnings.append(f"{nm(aid)}: FVTPL 的价格下跌已通过公允价值变动计入损益, 不再单独计提减值, 已忽略")
        elif cls == "FVOCI":
            je(f"{nm(aid)} 减值: 累计其他综合收益损失转入损益", [("资产减值损失", amt), ("其他综合收益", -amt, "减值转出")], aid)
            p["rec"] += amt
        elif cls == "AC":
            je(f"{nm(aid)} 计提减值准备", [("信用减值损失", amt), (ALLOW_ACC["AC"], -amt)], aid)
            p["allow"] += amt
        else:
            je(f"{nm(aid)} 计提存货跌价准备", [("资产减值损失", amt), (ALLOW_ACC["INVENTORY"], -amt)], aid)
            p["allow"] += amt

    # 11 贷款信用损失
    ctx_loans = []
    for l in loans:
        if l["lender"] == t["id"] and l["start"] <= w < l["due"]:
            ctx_loans.append(dict(id=l["id"], cp=cpn(l), principal=l["principal"], rate=l["rate"], start=l["start"], due=l["due"],
                                  accrued=l["principal"] * l["rate"] * (w - l["start"]) / 52, allow=lallow.get(l["id"], 0.0)))
    open_ids = {x["id"] for x in ctx_loans}
    for lid, d in decl.items():
        d = d if isinstance(d, dict) else {}
        amt = _amt(d.get("amount"), f"贷款 {lid} 信用损失")
        if amt < 0.005:
            continue
        if lid not in open_ids:
            warnings.append(f"贷款 {lid}: 不是本周末未到期的放款, 信用损失已忽略")
            continue
        l = next(x for x in loans if x["id"] == lid)
        if lallow.get(lid, 0) + amt > l["principal"] + 0.5:
            warnings.append(f"贷款 {lid}: 累计信用损失超过本金")
        if not str(d.get("reason", "")).strip():
            warnings.append(f"贷款 {lid}: 未填写信用损失判断依据")
        je(f"贷款 {lid} 计提预期信用损失", [("信用减值损失", amt), ("贷款损失准备", -amt)])
        lallow[lid] = lallow.get(lid, 0.0) + amt

    # 12 结转损益 + 校验
    profit = -sum(pl.values())
    led["留存收益"] = led.get("留存收益", 0.0) - profit
    if abs(sum(led.values())) > 0.05:
        warnings.append(f"试算不平衡 {sum(led.values()):,.2f} (系统异常, 请告知老师)")
    hw = next(h for h in t["hist"] if h["week"] == w)
    if abs(led.get("现金", 0.0) - hw["cash"]) > 1:
        warnings.append(f"会计现金 {led.get('现金', 0):,.0f} 与系统现金 {hw['cash']:,.0f} 不一致")

    g = lambda k: led.get(k, 0.0)
    nz = lambda items: [[n, round(v, 2)] for n, v in items if abs(v) >= 0.005]
    assets = nz([("现金", g("现金")), ("交易性金融资产", g("交易性金融资产")), ("FVOCI金融资产", g("FVOCI金融资产")),
                 ("摊余成本金融资产", g("摊余成本金融资产")), ("存货-黄金", g("存货-黄金")),
                 ("减: 金融资产减值准备", g("金融资产减值准备")), ("减: 存货跌价准备", g("存货跌价准备")),
                 ("贷款及应收款项", g("贷款及应收款项")), ("应收利息", g("应收利息")), ("减: 贷款损失准备", g("贷款损失准备"))])
    liabs = nz([("短期借款", -g("短期借款")), ("应付利息", -g("应付利息"))])
    eq = nz([("实收资本", -g("实收资本")), ("留存收益", -g("留存收益")), ("其他综合收益", -g("其他综合收益") + 0.0)])
    ta, tl, te = (sum(x[1] for x in z) for z in (assets, liabs, eq))
    inc = nz([(a, -pl.get(a, 0.0)) for a in PL_ACCS])
    oci_items = nz(list(oci.items()))
    statements = dict(
        balance_sheet=dict(assets=assets, liabilities=liabs, equity=eq, total_assets=round(ta, 2),
                           total_liabilities=round(tl, 2), total_equity=round(te, 2)),
        income_statement=dict(items=inc, net_profit=round(profit, 2)),
        oci_statement=dict(items=oci_items, total=round(sum(x[1] for x in oci_items), 2), opening=round(oci_open, 2),
                           closing=round(-g("其他综合收益"), 2) + 0.0),
        recon=dict(system_nav=hw["nav"], book_equity=round(te, 2), diff=round(hw["nav"] - te, 2)))
    closing = dict(ledger={k: round(v, 4) for k, v in led.items()}, positions=pos, loan_allow=lallow)
    return dict(journals=journals, statements=statements, warnings=warnings,
                ctx=dict(week=w, assets=ctx_assets, loans=ctx_loans, classes=CLASS_NAMES), closing=closing)


def api_acct_preview(sess, b):
    t = need_team(sess)
    r = generate_accounting(t, b.get("week"), b.get("decisions"))
    r.pop("closing")
    return r


def api_acct_submit(sess, b):
    t = need_team(sess)
    if not S["config"]["accounting_enabled"]:
        raise ApiError("会计结账功能未开启")
    w = int(b.get("week"))
    old = t["accounting"].get(str(w), {})
    if old.get("closing") and old.get("grade") is not None:
        raise ApiError("该周已评分, 不能修改 (请联系老师退回)")
    if t["accounting"].get(str(w + 1), {}).get("closing"):
        raise ApiError("下一周已提交, 不能修改本周 (请联系老师退回)")
    dec = b.get("decisions") if isinstance(b.get("decisions"), dict) else {}
    r = generate_accounting(t, w, dec)
    cl = dec.get("classes") if isinstance(dec.get("classes"), dict) else {}
    for aid, p in r["closing"]["positions"].items():
        if p["qty"] > 0:
            prev = t["acct_classes"].get(aid, {})
            d = cl.get(aid) if isinstance(cl.get(aid), dict) else {}
            same = prev.get("class") == p["cls"]
            t["acct_classes"][aid] = {"class": p["cls"], "reason": str(d.get("reason") or (prev.get("reason", "") if same else ""))[:300],
                                      "set_week": prev.get("set_week", w) if same else w}
    t["accounting"][str(w)] = dict(status="submitted", decisions=dec, notes=str(b.get("notes", ""))[:3000], journals=r["journals"],
                                   statements=r["statements"], warnings=r["warnings"], closing=r["closing"],
                                   submitted_by=sess["name"], grade=None, comment="")
    return {}


def api_acct_get(sess, b):
    t = S["teams"][b["team"]] if sess["role"] == "admin" else need_team(sess)
    rec = t["accounting"].get(str(int(b["week"])))
    return {k: v for k, v in rec.items() if k != "closing"} if rec else {}


def a_acct_grade(sess, b):
    if sess["role"] != "admin":
        raise ApiError("需要管理员权限")
    t = S["teams"][b["team"]]
    w = int(b["week"])
    rec = t["accounting"].get(str(w))
    if not rec:
        raise ApiError("该组该周没有会计结账记录")
    if b.get("action") == "return":
        if t["accounting"].get(str(w + 1), {}).get("closing"):
            raise ApiError("该组下一周已提交, 请先退回下一周")
        rec.update(status="returned", grade=None, comment=str(b.get("comment", ""))[:500])
        rec.pop("closing", None)
        return {}
    if not rec.get("closing"):
        raise ApiError("该周作业已被退回, 尚未重新提交")
    g = b.get("grade")
    rec["grade"] = None if g in (None, "") else num(b, "grade", 0, 100)
    rec["comment"] = str(b.get("comment", ""))[:500]
    return {}


POST = {
    "/api/order": api_order, "/api/order/cancel": api_order_cancel,
    "/api/loan/propose": api_loan_propose, "/api/loan/respond": api_loan_respond,
    "/api/report": api_report,
    "/api/admin/config": a_config, "/api/admin/team": a_team_save, "/api/admin/teams/batch": a_team_batch,
    "/api/admin/team/delete": a_team_delete, "/api/admin/asset": a_asset_save, "/api/admin/prices": a_prices,
    "/api/admin/settle": a_settle, "/api/admin/undo": a_undo, "/api/admin/reset": a_reset,
    "/api/admin/grade": a_grade, "/api/admin/event": a_event,
    "/api/accounting/preview": api_acct_preview, "/api/accounting/submit": api_acct_submit,
    "/api/accounting/get": api_acct_get, "/api/admin/accounting/grade": a_acct_grade,
}


class Handler(BaseHTTPRequestHandler):
    def log_message(self, *a):
        pass

    def send(self, code, body, ctype="application/json; charset=utf-8"):
        if not isinstance(body, bytes):
            body = json.dumps(body, ensure_ascii=False).encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)

    def client_ip(self):
        fwd = self.headers.get("X-Forwarded-For", "")  # 部署在 Render 等反向代理后面时取真实 IP
        return fwd.split(",")[0].strip() if fwd else self.client_address[0]

    def session(self):
        return SESSIONS.get(self.headers.get("X-Token", ""))

    def do_GET(self):
        path = urlparse(self.path).path
        if path in ("/", "/index.html"):
            with open(os.path.join(ROOT, "index.html"), "rb") as f:
                return self.send(200, f.read(), "text/html; charset=utf-8")
        if path == "/api/state":
            sess = self.session()
            if not sess:
                return self.send(401, dict(error="未登录"))
            with LOCK:
                try:
                    return self.send(200, build_state(sess))
                except ApiError as e:
                    return self.send(401, dict(error=str(e)))
        self.send(404, dict(error="not found"))

    def do_POST(self):
        path = urlparse(self.path).path
        try:
            n = int(self.headers.get("Content-Length") or 0)
            body = json.loads(self.rfile.read(n) or b"{}")
            with LOCK:
                if path == "/api/login":
                    res = api_login(None, body, self.client_ip())
                else:
                    sess = self.session()
                    if not sess:
                        return self.send(401, dict(error="未登录"))
                    fn = POST.get(path)
                    if not fn:
                        return self.send(404, dict(error="not found"))
                    res = fn(sess, body)
                save()
            self.send(200, res)
        except ApiError as e:
            self.send(400, dict(error=str(e)))
        except (KeyError, ValueError, TypeError) as e:
            self.send(400, dict(error=f"请求参数有误: {e}"))


def lan_ip():
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("8.8.8.8", 80))
        ip = s.getsockname()[0]
        s.close()
        return ip
    except OSError:
        return "127.0.0.1"


S = load()
if os.environ.get("ADMIN_PASSWORD"):  # 部署时用环境变量设置, 每次启动覆盖
    S["admin_password"] = os.environ["ADMIN_PASSWORD"]
if not S["teams"]:  # 没有任何小组时: 预置 1 个小组, 口令 GROUP1
    new_team("第1组", "GROUP1")

if __name__ == "__main__":
    port = int(sys.argv[1]) if len(sys.argv) > 1 else int(os.environ.get("PORT", 8000))
    with LOCK:
        save()
    print(f"Market Simulation 已启动\n  本机:   http://localhost:{port}\n  局域网: http://{lan_ip()}:{port}  (学生用这个地址)")
    print(f"  数据文件: {STATE_FILE}")
    if not os.environ.get("ADMIN_PASSWORD"):
        print(f"  管理员密码: {S['admin_password']}")
    ThreadingHTTPServer(("0.0.0.0", port), Handler).serve_forever()
