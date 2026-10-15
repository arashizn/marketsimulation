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
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse

ROOT = os.path.dirname(os.path.abspath(__file__))
DATA_DIR = os.path.join(ROOT, "data")
STATE_FILE = os.path.join(DATA_DIR, "state.json")
UNDO_FILE = os.path.join(DATA_DIR, "undo.json")
LOCK = threading.RLock()
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
    d["accounting"] = {w: {k: v for k, v in r.items() if k not in ("journals", "statements", "positions", "loans")}
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


def api_login(sess, b):
    if b.get("admin"):
        if b.get("password") != S["admin_password"]:
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
    if c["accounting_enabled"] and c["accounting_lock_trade"] and S["week"] > 1:
        if t["accounting"].get(str(S["week"] - 1), {}).get("status") not in ("submitted",)                 and t["accounting"].get(str(S["week"] - 1), {}).get("grade") is None:
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


POST = {
    "/api/order": api_order, "/api/order/cancel": api_order_cancel,
    "/api/loan/propose": api_loan_propose, "/api/loan/respond": api_loan_respond,
    "/api/report": api_report,
    "/api/admin/config": a_config, "/api/admin/team": a_team_save, "/api/admin/teams/batch": a_team_batch,
    "/api/admin/team/delete": a_team_delete, "/api/admin/asset": a_asset_save, "/api/admin/prices": a_prices,
    "/api/admin/settle": a_settle, "/api/admin/undo": a_undo, "/api/admin/reset": a_reset,
    "/api/admin/grade": a_grade, "/api/admin/event": a_event,
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
                    res = api_login(None, body)
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

if __name__ == "__main__":
    port = int(sys.argv[1]) if len(sys.argv) > 1 else 8000
    with LOCK:
        save()
    print(f"Market Simulation 已启动\n  本机:   http://localhost:{port}\n  局域网: http://{lan_ip()}:{port}  (学生用这个地址)")
    print(f"  管理员密码: {S['admin_password']}   数据文件: {STATE_FILE}")
    ThreadingHTTPServer(("0.0.0.0", port), Handler).serve_forever()
