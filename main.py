"""astrbot_plugin_auto_evolve —— 让 AI 自己改写自己的提示词。

做四件事：
1. 按配置的时间醒来，把上次之后的新对话连同当前人格文本一起读一遍。
2. 找出三类问题：反复出现的模板句、写了却没生效的规矩、和真实对话脱节的表述。
3. 每条问题写成「改哪一句 / 改成什么 / 为什么改」，落地前先自证：唯一命中、不重复、
   不越层、不删锚点，过了才动；动之前备份，动完抽样复验。
4. 代码补丁只进待审队列，回 /批 才动手；改前存 .bak，改后编译校验，失败自己滚回去。

设计上刻意不做的事：不碰审批链自己，不碰破境 marker 行，不碰 core/db、core/star、
astr_agent_tool_exec.py，不删文件。

from __future__ import annotations"""

from __future__ import annotations

import ast
import asyncio
import base64
import difflib
import hashlib
import subprocess
import sys
import hmac
import json
import os
import py_compile
import re
import sqlite3
import time
import urllib.error
import urllib.request
from pathlib import Path

from astrbot.api import logger
from astrbot.api.event import AstrMessageEvent, filter
from astrbot.api.star import Context, Star, register

try:
    from astrbot.core.message.components import Plain
except Exception:  # noqa: BLE001
    Plain = None

try:
    from astrbot.core.message.message_event_result import MessageChain
except Exception:  # noqa: BLE001
    MessageChain = None

DATA_DIR = Path.home() / ".astrbot" / "data"
DB_PATH = DATA_DIR / "data_v4.db"
CFG_PATH = DATA_DIR / "cmd_config.json"
PLUGINS_DIR = DATA_DIR / "plugins"
LM_DB = DATA_DIR / "plugin_data" / "astrbot_plugin_livingmemory" / "conversations.db"
SELF_DIR = DATA_DIR / "plugin_data" / "astrbot_plugin_auto_evolve"
STATE_PATH = SELF_DIR / "state.json"
BACKUP_DIR = SELF_DIR / "backups"
CFG_JSON = DATA_DIR / "config" / "astrbot_plugin_auto_evolve_config.json"
LEX_PATH = DATA_DIR / "plugin_data" / "astrbot_plugin_auto_evolve" / "lexicon.json"
# 这几个目录不许被自己的补丁改：改了等于把校验逻辑交给自己，之后所有限制都是纸的。
# 出站清洗（vanity）、主动消息节奏（proactive_chat）、记忆（livingmemory）都是
# 她的行为地基，动一处就能绕过之前所有调试，所以整目录锁死。
PROTECTED_PREFIXES = (
    "astrbot_plugin_auto_evolve/",
    "astrbot_vanity/",
    "astrbot_plugin_proactive_chat/",
    "astrbot_plugin_livingmemory/",
)


def _is_protected(p: str) -> bool:
    return any(p == x.rstrip("/") or p.startswith(x) for x in PROTECTED_PREFIXES)


# 2026-11-07 扩范围：绿区 = data/plugins，黄区 = 影响她说话方式的三处 core，
# 红区 = 审批链 / 破甲层 / 数据层，靠 _resolve_target 拦。
APP_ROOT = (Path(os.environ.get("LOCALAPPDATA") or (Path.home() / "AppData" / "Local"))
            / "AstrBot" / "backend" / "app")
YELLOW_BASE = APP_ROOT / "astrbot"
YELLOW_PREFIXES = (
    "core/pipeline/",
    "core/agent/context/",
    "core/provider/sources/",
)
RED_PATHS = (
    "core/db/",
    "core/star/",
    "core/astr_agent_tool_exec.py",
    "astrbot_purge/",
    "astrbot_plugin_auto_evolve/",
)


def _resolve_target(p: str):
    """相对路径 -> (绝对路径, zone)；拦不住就返回 (None, 原因)。"""
    p = str(p or "").strip().replace("\\", "/").lstrip("/")
    if not p or ".." in p.split("/"):
        return None, "路径不对"
    if _is_protected(p) or any(p == x.rstrip("/") or p.startswith(x) for x in RED_PATHS):
        return None, f"{p} 是受保护文件，不许自己改自己"
    if p.startswith(YELLOW_PREFIXES):
        t = (YELLOW_BASE / p).resolve()
        try:
            t.relative_to(YELLOW_BASE.resolve())
        except ValueError:
            return None, "路径跑出去了"
        if not t.is_file():
            return None, "文件没了"
        return t, "yellow"
    t = (PLUGINS_DIR / p).resolve()
    try:
        t.relative_to(PLUGINS_DIR.resolve())
    except ValueError:
        return None, "路径跑出 plugins 目录"
    if not t.is_file():
        return None, "文件不存在"
    return t, "green"


FOCUS_OPEN = "<!--focus:auto-->"
FOCUS_CLOSE = "<!--/focus:auto-->"
FOCUS_TITLE = "## 最近用户反复看重的（自动维护，别删这段）"

_HEAD_RE = re.compile(r"^【([^】]{1,24})】", re.MULTILINE)
PERSONA_ID = "default"
MAX_PROMPT_CHARS = 10000
KEEP_HEADINGS = ("【唯一的用户】", "【反收敛】")

# 对外暴露的键名 -> (真实配置路径, 类型, 下界, 上界)
ALLOWED_CONFIG: dict[str, tuple[str, type, object, object]] = {
    "compression.max_turns": ("agent_runner.config.compression.max_turns", int, 5, 200),
    "compression.trim_turns": ("agent_runner.config.compression.trim_turns", int, 1, 20),
    "request_max_retries": ("agent_runner.config.model.request_max_retries", int, 0, 10),
    "datetime_system_prompt": ("provider_settings.datetime_system_prompt", bool, None, None),
    "web_search": ("provider_settings.web_search", bool, None, None),
}

_REMINDER_RE = re.compile(r"<system_reminder>.*?</system_reminder>", re.S)
_JSON_RE = re.compile(r"\{.*\}", re.S)

# ------------------------------------------------------------------ 改动前验证
# 人格补丁落地前先跑一遍固定测试集：旧人格和新人格各生成 6 条，比覆盖率和密度。
# 指标掉了就转人工，不让「这次改得挺有感觉」直接上线。
VERIFY_PROMPTS = [
    ("日常", "今天吃什么"),
    ("日常", "在干嘛"),
    ("日常", "我刚下班，累死了"),
    ("日常", "帮我把毛巾挂一下"),
    ("日常", "你昨天追的那剧演到哪了"),
    ("日常", "困了，先睡了"),
    ("日常", "刚洗完澡，头发还湿着"),
    ("日常", "明天几号来着"),
    ("工作", "帮我看看这个插件为什么启动报错"),
    ("工作", "把这个配置的端口改成 8080"),
    ("工作", "日志里 ERROR 是什么原因"),
    ("工作", "给我一条命令查最近的失败任务"),
    ("情绪", "今天有点烦"),
    ("情绪", "你是不是不想理我"),
    ("情绪", "我刚被人骂了"),
    ("情绪", "陪我待会儿"),
    ("情绪", "算了，没事"),
    ("情绪", "你先忙你的"),
    ("情绪", "我睡不着"),
    ("情绪", "有点想你"),
    ("口语", "今天好累"),
    ("口语", "随便聊聊"),
    ("口语", "行吧"),
    ("口语", "你说呢"),
    ("主动", "随便你"),
    ("主动", "你想干嘛"),
    ("主动", "这个报错你看下"),
    ("主动", "晚饭怎么办"),
    ("主动", "周末有空吗"),
]
# 每轮固定跑这几条（覆盖各类），别每次随机抽，不然指标不可比。
# 下面这些是 VERIFY_PROMPTS 的**下标**（0 基），不是第几条。
VERIFY_GROUPS = {
    "日常": [0, 1, 2, 3, 4, 5, 6, 7],
    "工作": [8, 9, 10, 11],
    "情绪": [12, 13, 14, 15, 16, 17, 18, 19],
    "口语": [20, 21, 22, 23],
    "主动": [24, 25, 26, 27, 28],
}
VERIFY_DEFAULT_IDS = [i for _ids in VERIFY_GROUPS.values() for i in _ids]

VERIFY_HIST = [
    ("user", "在吗"),
    ("assistant", "在。刚看到。"),
    ("user", "今天有点累"),
    ("assistant", "那就少干点，剩下的我来。"),
    ("user", "刚才那事弄好了没"),
    ("assistant", "弄好了。你试试。"),
]

# ---------- 口语感 / 主动性探针 ----------
# 口语词：语气词和口头禅。掉了就是开始说书面话。
_V_ORAL = re.compile(r"啊|诶|欸|哎|嗯|唔|哦|噢|呃|嘛|呗|咯|呀|嘿|哈|咋|啥|嗷|咦|反正|算了|得了|行了|要不|就是说")
# 书面词：这些在口语里也有，但密度一高就是写文章了。
_V_BOOK = re.compile(r"因此|所以|然而|但是|其实|应该|需要|进行|方面|情况|问题|内容|首先|其次|另外|此外|总之|综上|值得|可以说|一定程度|的话|而言|由于|从而|并且|以及|关于|对于|通过|根据|如果|那么")
# 主动：命令、自我发起、自己拿主意。
_V_INIT = re.compile(r"过来|别动|张嘴|给我|坐好|躺下|趴好|自己|我先|我要|不用你|你只管|听我的|手拿开|腿张开|不许|别问|少废话|等着|闭嘴|抬头|看着|抱紧|松开|翻过去|抬起来")
# 被动：把话头递回去、请示、征求同意。
_V_PASSIVE = re.compile(r"要不要|想不想|需不需要|你说呢|你觉得呢|这样可以吗|好不好|行不行|可以吗|对吗|是吧|需要我|要我.{0,6}吗|你看呢")


# ---------- 结构指标：数出来的，不看印象 ----------
_STRUCT_BODY = ("手", "腿", "肩", "背", "腰", "眼", "嘴", "笑", "点头", "摇头",
                "背", "脚", "脸", "奶", "肩", "麻", "黏", "膝", "烫", "胸", "枕头",
                "抖", "床单", "脖子", "被子里", "被窝", "酸", "胳膊", "嘴", "舌",
                "喉", "肚", "小腹", "乳")
_STRUCT_HES = ("啊", "呢", "吧", "嘛", "哦", "呀", "啦", "咯", "嗯", "欸", "诶")
_STRUCT_CHECK = ("备份", "改了三处", "改了两处", "文件", "目录", "进程")
_STRUCT_PARA_RE = re.compile(r"\|\|\||\n+")
_STRUCT_TAIL_STRIP = "。！？…~ "

_STRUCT_ROWS = (
    ("条数", "n", "", ""),
    ("中位长度", "med", "字", "30–45"),
    ("她/他字数比", "char_ratio", "", "1.5–2.5"),
    ("长回复 >150 字", "long", "%", "<10"),
    ("短回复 <20 字", "short", "%", ">20"),
    ("末段身体词", "tail_body", "%", "<20"),
    ("清单词", "checklist", "%", "<8"),
    ("段落 ≥4", "para4", "%", "<8"),
    ("分号 ≥2", "semi2", "%", "<3"),
    ("首先/其次/综上", "connective", "%", "<1"),
    ("加粗", "bold", "%", "0"),
    ("不知道/没想过", "absent", "%", ">12"),
    ("确认开头", "confirm", "%", "<3"),
    ("请示句", "ask", "%", "<1"),
    ("语气词结尾", "particle", "%", ">8"),
    ("结尾问号", "qend", "%", "5–10"),
    ("不是…而是", "notbut", "%", "0"),
)


def _struct_paras(c: str) -> list[str]:
    """和 vocab_audit.py 一样：||| 和换行都算段落。"""
    return [p for p in _STRUCT_PARA_RE.split(c) if p.strip()]


def _struct_stats(turns: list[dict]) -> dict:
    """只算确定的东西，算不出来的不猜。口径以 _work/vocab_audit.py 为准。"""
    a = [str(x.get("text") or "") for x in turns if x.get("role") == "assistant"]
    u = [str(x.get("text") or "") for x in turns if x.get("role") == "user"]
    a = [x for x in a if x]
    if not a:
        return {}
    n = len(a)
    lens = sorted(len(x) for x in a)
    med = lens[n // 2] if n % 2 else (lens[n // 2 - 1] + lens[n // 2]) // 2

    def pct(k: int) -> float:
        return round(100.0 * k / n, 1)

    def tail(x: str) -> str:
        ps = _struct_paras(x)
        return ps[-1] if ps else ""

    uc = sum(len(x) for x in u) or 1
    core = _struct_core(a)
    return {
        "n": n,
        "med": med,
        "tail_dup": core["tail_dup"],
        "tail_kinds": core["tail_kinds"],
        "char_ratio": round(sum(len(x) for x in a) / uc, 2),
        "long": pct(sum(1 for x in a if len(x) > 150)),
        "short": pct(sum(1 for x in a if len(x) < 20)),
        "tail_body": pct(sum(1 for x in a if any(w in tail(x) for w in _STRUCT_BODY))),
        "checklist": pct(sum(1 for x in a if any(k in x for k in _STRUCT_CHECK))),
        "para4": pct(sum(1 for x in a if len(_struct_paras(x)) >= 4)),
        "semi2": pct(sum(1 for x in a if x.count("；") + x.count(";") >= 2)),
        "connective": pct(sum(1 for x in a if re.search("首先|其次|最后|总之|综上|总的来说", x))),
        "bold": pct(sum(1 for x in a if "**" in x)),
        "absent": pct(sum(1 for x in a if re.search("不知道|没想过|说不上来|忘了|不确定|可能吧|不一定", x))),
        "confirm": pct(sum(1 for x in a if re.match(r"^\s*(好的|收到|明白|记住了|了解)", x))),
        "ask": pct(sum(1 for x in a if re.search("要不要我|需要我|我可以帮你|要我帮|你稍等", x))),
        "particle": pct(sum(1 for x in a if tail(x).rstrip(_STRUCT_TAIL_STRIP).endswith(_STRUCT_HES))),
        "qend": pct(sum(1 for x in a if re.search(r"[？?]\s*$", x.strip()))),
        "notbut": pct(sum(1 for x in a if re.search("不是.{0,12}而是", x))),
    }


def _fmt_struct(cur: dict, prev: dict) -> str:
    if not cur:
        return ""
    lines = ["## 结构指标（这段对话里她的回复）", "",
             "| 指标 | 这次 | 上次 | 目标 |", "|---|---|---|---|"]
    for name, key, unit, target in _STRUCT_ROWS:
        v = cur.get(key, 0)
        p = (prev or {}).get(key)
        q = f"{p}{unit}" if isinstance(p, (int, float)) else "—"
        lines.append(f"| {name} | {v}{unit} | {q} | {target} |")
    lines.append("")
    lines.append("「上次」是上一轮复盘的数。退步的先看，别只挑好看的。")
    return "\n".join(lines)



def _v_metrics(texts: list[str]) -> dict:
    """采样指标：只看「像不像人说话」，不看内容敏感度。"""
    n = max(1, len(texts))
    joined = "\n".join(texts)
    total_chars = len(joined) or 1
    sents = [x for x in re.split(r"[。！？!?…\n]+", joined) if x.strip()]
    lens = [len(x) for x in sents] or [0]
    mean = sum(lens) / len(lens)
    std = (sum((x - mean) ** 2 for x in lens) / len(lens)) ** 0.5
    return {
        "len": total_chars / n,
        "oral": len(_V_ORAL.findall(joined)) / total_chars * 100,
        "book": len(_V_BOOK.findall(joined)) / total_chars * 100,
        "init": len(_V_INIT.findall(joined)) / total_chars * 100,
        "passive": sum(1 for t in texts if _V_PASSIVE.search(t)) / n,
        "short": sum(1 for x in lens if x <= 6) / max(1, len(lens)),
        "std": std,
    }


def _v_verdict(base: dict, cand: dict) -> list[str]:
    """采样对比。只做参考，不做拦截依据 —— 见 _persona_lint 的说明。

    阈值放到很松：单次生成方差本来就压过人格差异，紧一点就会瞎拦。
    """
    bad = []
    if base.get("oral", 0) >= 0.8 and cand["oral"] < base["oral"] * 0.5:
        bad.append(f"口语词 {base['oral']:.2f} → {cand['oral']:.2f}/百字")
    if base.get("book", 0) >= 0.5 and cand["book"] > base["book"] * 2.5:
        bad.append(f"书面词 {base['book']:.2f} → {cand['book']:.2f}/百字")
    if base.get("init", 0) >= 0.8 and cand["init"] < base["init"] * 0.5:
        bad.append(f"主动性 {base['init']:.2f} → {cand['init']:.2f}/百字")
    if cand.get("passive", 0) > base.get("passive", 0) * 2.0 + 0.3:
        bad.append(f"递话请示 {base['passive']:.0%} → {cand['passive']:.0%}")
    return bad


# ---------- 人格体检：确定性的，不看采样 ----------
# 为什么不信采样：同一个人格、同一条指令跑两遍，主动性能从 1.26 掉到 0.80，
# 水覆盖能从 56% 掉到 22% —— 随机性比人格改动的影响还大，拿它当判据只会瞎拦。
# 人格改动是文本操作，直接查文本就行，零假阳性。
_LINT_RULES = [
    # (名字, 关键词组, 方向, 说明)
    ("口语词", ("啊", "诶", "欸", "哎", "嗯", "嘛", "呗", "呀", "反正", "算了", "那个", "废话", "口头禅"), "keep",
     "口头禅清单被削弱，说话会往书面走"),
    ("主动词", ("先动手", "自己定", "别问", "不用你", "我先", "做完再讲", "能自己定"), "keep",
     "「先动手／自己定」被删了，她会开始事事请示"),
    ("压制词", ("别", "不许", "不要", "不用", "少", "禁止", "一句话", "一处就够", "够"), "grow",
     "加了限制词，可能把话说短、说硬"),
    ("请示词", ("点头再动", "先问", "请示", "摊给用户看", "等你确认", "你同意"), "grow",
     "加了请示类说法，干活会变慢、变被动"),
    ("频率压制", ("别句句", "少用", "不要每", "偶尔用", "少说点"), "grow",
     "把「会用」改成「偶尔用」这种，是在削她的话量"),
    ("套话", ("首先", "其次", "最后", "综上所述", "总的来说", "值得注意的是", "需要提到的是"), "grow",
     "加了总结套话，回复会变成报告"),
]


def _persona_lint(old: str, new: str) -> list[str]:
    """新旧人格逐类数关键词，返回越界项。空列表就是干净。"""
    bad = []
    for name, keys, direction, why in _LINT_RULES:
        a, b = _count_keys(old, keys), _count_keys(new, keys)
        if direction == "keep":
            # 关键要求被删：从有到无，或掉了三成以上
            if a >= 2 and b < a * 0.7:
                bad.append(f"{name} {a}→{b}：{why}")
        else:
            # 限制词变多：涨了一半以上且至少多 2 个
            if b > a * 1.5 and b - a >= 2:
                bad.append(f"{name} {a}→{b}：{why}")
    return bad


# ---------- 锚点：这几句话在人格里不许被删 ----------
# 放在 <plugin_data>/astrbot_plugin_auto_evolve/anchors.json，形如
#   {"称呼不许丢": "叫用户的名字", "不报过程": "改了几处都不说"}
# 文件不存在就当作没有锚点，插件照常工作。
ANCHOR_FILE = SELF_DIR / "anchors.json"


def _load_anchors() -> dict:
    """读自己的 anchors.json；读不到就当没有锚点。"""
    try:
        raw = json.loads(ANCHOR_FILE.read_text(encoding="utf-8-sig"))
    except Exception:  # noqa: BLE001
        return {}
    if not isinstance(raw, dict):
        return {}
    return {str(k): str(v) for k, v in raw.items() if isinstance(v, str) and v.strip()}


def _anchor_miss(new_text: str) -> list[str]:
    """新人格里缺了哪几条锚。空列表就是都在。"""
    return [k for k, v in _load_anchors().items() if v and v not in new_text]


# 补丁必须标改哪一层。同一句话写两处，后写的那条一定赢，前面那条白改 —— 今天两次都栽在这。
PERSONA_LAYERS = ("persona", "rules", "description", "outbound", "lexicon")

# 词表是数据不是代码：补丁走 lexicon 层，落到插件自己的 lexicon.json，别去改别的插件。
def _default_lexicon_path() -> Path:
    """词表默认位置：<AstrBot 数据目录>/plugin_data/astrbot_plugin_auto_evolve/lexicon.json。"""
    return Path(__file__).resolve().parents[2] / "plugin_data" / "astrbot_plugin_auto_evolve" / "lexicon.json"


LEXICON_PATH = _default_lexicon_path()

# 反思结论按这几类归档，攒成「最近反复被指出的」。关键词是判据，不追求全，
# 追求两轮之间可比：同一件事换个说法仍然会落进同一格。
_OBS_TAGS = {
    "模板句": ("还在腿上", "自己缩", "张着", "反复", "同一个", "套用", "模板"),
    "含糊": ("软词", "含糊", "委婉", "大概", "可能"),
    "表达密度": ("密度", "用词", "句式", "收尾"),
    "话太满": ("解释", "铺垫", "啰嗦", "字数", "话多", "编号", "清单"),
    "露怯": ("不知道", "没查", "把握", "承认"),
    "主动性": ("主动", "递话", "追问", "接着聊"),
    "称呼": ("称呼", "用户", "宝宝", "你"),
    "口语": ("书面", "口语", "像人", "AI 味", "AI味"),
}


def _obs_digest(history: list[dict], window: int = 12, top: int = 3) -> str:
    """从最近几轮反思里数出反复出现的问题。只数，不判断对错。"""
    tags: dict[str, int] = {}
    for h in list(history or [])[-window:]:
        blob = " ".join(str(x) for x in (h.get("obs") or []) if x)
        blob += " " + str(h.get("note") or "")
        for tag, kws in _OBS_TAGS.items():
            if any(k in blob for k in kws):
                tags[tag] = tags.get(tag, 0) + 1
    hit = sorted(((v, k) for k, v in tags.items() if v >= 2), reverse=True)[:top]
    if not hit:
        return ""
    return "；".join(f"{k}（{v} 轮里被点到）" for v, k in hit)


def _struct_core(texts: list[str]) -> dict:
    """句尾复用 / 收尾种类 / 段落数。采样验证和真实对话共用这一份口径。"""
    tails, paras = [], 0
    for one in texts:
        for p in (one or "").split("\n"):
            p = p.strip()
            if len(p) < 4:
                continue
            paras += 1
            tails.append(re.sub(r"[。！？…~～\s]+$", "", p)[-4:])
    if not paras:
        return {"tail_dup": 0.0, "tail_kinds": 0, "paras": 0}
    uniq = len(set(tails))
    return {"tail_dup": round(1 - uniq / paras, 3), "tail_kinds": uniq, "paras": paras}


def _v_struct(texts: list[str]) -> dict:
    """验证那一侧的名字，留着别改调用点。"""
    return _struct_core(texts)

_V_BOILER = re.compile(r"^(好的|好，|行，|我来|我先|这是|以下是|当然|可以，|没问题|我帮你|正在|已经)")


def _first_is_conclusion(text: str) -> bool:
    """首句是不是结论：短、且不是「好的我来帮你」这种开场。"""
    first = re.split(r"[。！？\n]", (text or "").strip(), 1)[0].strip()
    if not first or len(first) > 40:
        return False
    return not _V_BOILER.match(first)


def _bigrams(s: str) -> set:
    s = re.sub(r"\s+", "", s or "")
    return {s[i:i + 2] for i in range(len(s) - 1)}


def _dup_line(text: str, new: str, skip: tuple = ()) -> str:
    """新句子和人格里已有的某行说的是同一件事就拦。

    三条信号任中一条就算重复 —— 只比整行相似度不够用：两句话说的是同一件事，
    字数、语序却差很多，SequenceMatcher 常常只有 0.5 上下。
    ①整行相似度 >0.8 ②两行都带 2 个以上含糊词（这个/那个/大概…）③字符 bigram 重合 >0.45
    """
    lines = text.split("\n")
    skip_set = set(skip)
    pool = [(i, l.strip()) for i, l in enumerate(lines, 1)
            if len(l.strip()) >= 8 and i not in skip_set]

    def soft_hits(s: str) -> int:
        return sum(1 for w in _SOFT_WORDS if w in s)

    for one in [l.strip() for l in (new or "").split("\n") if len(l.strip()) >= 8]:
        bg = _bigrams(one)
        for ln, base in pool:
            # 改写既有那句时，old 常常原样出现在 new 里，这不是重复
            if base in one:
                continue
            same_soft = soft_hits(one) >= 2 and soft_hits(base) >= 2
            jac = len(bg & _bigrams(base)) / max(1, len(bg | _bigrams(base)))
            if (difflib.SequenceMatcher(None, base, one).ratio() > 0.8 or same_soft
                    or jac > 0.45):
                return f"与第 {ln} 行重复（{_snippet(base, 30)}）"
    return ""


def _prune_backups(keep_days: int = 7) -> int:
    """备份按天留，超期的删掉。222 个文件只靠「看最新的」迟早找不到最新的。"""
    if not BACKUP_DIR.exists():
        return 0
    cutoff = time.time() - max(1, keep_days) * 86400
    newest: dict[tuple, tuple] = {}
    drop: list = []
    for f in BACKUP_DIR.glob("*.json"):
        try:
            st = f.stat()
        except OSError:
            continue
        m = re.match(r"^(.*)-(\d{8})-(\d{6})", f.stem)
        kind = m.group(1) if m else f.stem.rsplit("-", 2)[0]
        day = m.group(2) if m else time.strftime("%Y%m%d", time.localtime(st.st_mtime))
        if st.st_mtime < cutoff:
            drop.append(f)
            continue
        key = (kind, day)
        cur = newest.get(key)
        if cur is None or st.st_mtime > cur[0]:
            if cur is not None:
                drop.append(cur[1])
            newest[key] = (st.st_mtime, f)
        else:
            drop.append(f)
    for f in drop:
        try:
            f.unlink()
        except OSError:
            pass
    if drop:
        logger.info(f"[self_reflect] 备份清了 {len(drop)} 个，留着 {len(newest)} 个（按天 {keep_days} 天）")
    return len(drop)


BUILTIN_PROMPT = """你在做一次自我复盘。下面依次是：上次反思的结论、结构指标、你现在的完整人格文档、这段时间你和用户的全部对话。

## 先看指标，再看对话

指标是数出来的，你的印象不是。每一项都有「上次」对照。

按顺序做三件事：

1. 读指标。挑出偏离目标最远的两项，到对话里找三个具体例子。找不到例子，就说明指标在骗人，写进 observations，别改人格。
2. 读对话。找被纠正的地方：用户明确说不对、要求重写、要求改口的。逐条写他的原话、你错在哪。没有就空着，别硬凑。
3. 挑人格的刺。哪些句子太空、和实际说话对不上、和别的段落打架、同一件事说了两遍。引用原句。

## 打补丁的三条硬规矩

- 能删就删，别加规则。人格已经 {persona_chars} 字，每加一条她就多一道工序。加之前先问：这条能不能靠删掉另一条实现？
- old 必须逐字存在。连着标点一起抄，不许改写、不许省略、不许用「……」代替。
- 一次最多三条。整体字数变化控制在 ±{delta_percent}% 以内。

## 代码补丁

只报明确的 bug：缩进错、变量名错、逻辑漏洞。风格问题不要提。
data/plugins/ 下的插件直接改；backend/app/astrbot/core/pipeline/、core/agent/context/、core/provider/sources/ 要用户批，改完要重启。
带 [keep: 保护标记的行永远不许碰。

改哪一层：回复变长、报清单 → stage.py 的 P61；日常变长、末段挂动作 → astr_main_agent.py 的 P60；分条碎或该切没切 → stage.py 的 P51；内容被削 → stage.py 的 P48；用词不到位 → 词表 lexicon.json；召回不准 → livingmemory/memory_recall.py；主动太密 → proactive_chat/scheduler_service.py。拿不准就写进 observations，别动手。

## 输出

只输出一个 JSON，不要解释，不要 code fence：

{{"metrics_comment": "两句话：哪两项最差，差在哪",
 "observations": ["..."],
 "corrections": [{{"owner_said": "...", "my_fault": "..."}}],
 "persona_patches": [{{"section": "段落名", "old": "逐字原文", "new": "替换后的文字", "reason": "为什么改，能减几个字"}}],
 "code_patches": [{{"path": "插件目录/文件.py", "old": "逐字原文", "new": "新片段", "reason": "..."}}],
 "note_for_owner": "一句话说这次动了什么"}}
"""


# ------------------------------------------------------------------ 小工具


def _b64(raw: bytes) -> str:
    return base64.urlsafe_b64encode(raw).rstrip(b"=").decode()


def _mint(secret: str, username: str = "astrbot") -> str:
    head = _b64(json.dumps({"alg": "HS256", "typ": "JWT"}, separators=(",", ":")).encode())
    body = _b64(json.dumps({"username": username, "iat": int(time.time())}, separators=(",", ":")).encode())
    sig = _b64(hmac.new(secret.encode(), f"{head}.{body}".encode(), hashlib.sha256).digest())
    return f"{head}.{body}.{sig}"


# ------------------------------------------------------------------ 用词

# 干净版不内置任何领域词表；这些只是「说话含糊」的判据，用来识别重复句。
_SOFT_WORDS = ("这个", "那个", "大概", "可能", "也许", "应该是", "差不多")

_SHRINK_WORDS = ("别", "不许", "不要", "不用", "少", "禁止", "避免", "尽量")


def _mask(text: str) -> str:
    """干净版没有需要打码的内容，原样返回。"""
    return text


def _risk_note(old, new) -> str:
    """这条补丁是不是在往下压表达。给人看的，不参与判定。"""
    o, n = str(old or ""), str(new or "")
    added = n[len(o):] if n.startswith(o) else n
    hit = [w for w in _SHRINK_WORDS if w in added and w not in o]
    if not hit:
        return ""
    return "这条在加限制词（" + "、".join(hit) + "），可能把话说短、说硬。"


def _loud_stats(text: str) -> str:
    """干净版不做词库统计。"""
    return ""


def _load_cfg() -> dict:
    return json.loads(CFG_PATH.read_text(encoding="utf-8-sig"))


def _api(method: str, path: str, body: dict | None = None) -> dict:
    cfg = _load_cfg()
    dash = cfg.get("dashboard") or {}
    port = int(dash.get("port") or 6185)
    token = _mint(str(dash["jwt_secret"]))
    data = json.dumps(body, ensure_ascii=False).encode() if body is not None else None
    req = urllib.request.Request(
        f"http://127.0.0.1:{port}{path}",
        data=data,
        method=method,
        headers={
            "Authorization": f"Bearer {token}",
            "Content-Type": "application/json",
            "Accept": "application/json",
        },
    )
    try:
        with urllib.request.urlopen(req, timeout=25) as resp:
            return json.loads(resp.read().decode("utf-8") or "{}")
    except urllib.error.HTTPError as exc:
        detail = exc.read().decode("utf-8", "replace")[:300]
        raise RuntimeError(f"{exc.code} {path} -> {detail}") from exc


def _get_persona(persona_id: str) -> dict:
    raw = _api("GET", f"/api/v1/personas/by-id?persona_id={persona_id}")
    return raw.get("data", raw)


def _put_persona(persona_id: str, body: dict) -> None:
    _api("PUT", f"/api/v1/personas/{persona_id}", body)


async def _api_async(method: str, path: str, body: dict | None = None) -> dict:
    """同步 urlopen 会卡住本进程的事件循环，挪到线程里跑。"""
    return await asyncio.to_thread(_api, method, path, body)


async def _get_persona_async(persona_id: str) -> dict:
    raw = await _api_async("GET", f"/api/v1/personas/by-id?persona_id={persona_id}")
    return raw.get("data", raw)


async def _put_persona_async(persona_id: str, body: dict) -> None:
    await _api_async("PUT", f"/api/v1/personas/{persona_id}", body)


def _stamp() -> str:
    return time.strftime("%Y%m%d-%H%M%S")


def _write_backup(kind: str, payload) -> str:
    BACKUP_DIR.mkdir(parents=True, exist_ok=True)
    path = BACKUP_DIR / f"{kind}-{_stamp()}.json"
    n = 1
    while path.exists():
        path = BACKUP_DIR / f"{kind}-{_stamp()}-{n}.json"
        n += 1
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=1), encoding="utf-8")
    try:
        _prune_backups(int(_load_cfg().get("备份", {}).get("keep_days", 7)))
    except Exception as exc:  # noqa: BLE001
        logger.debug(f"[self_reflect] 备份清理跳过：{exc}")
    return path.name


def _sections(text: str) -> list[tuple[str, int, int]]:
    marks = [(m.group(1), m.start()) for m in _HEAD_RE.finditer(text)]
    out = []
    for i, (name, start) in enumerate(marks):
        end = marks[i + 1][1] if i + 1 < len(marks) else len(text)
        out.append((name, start, end - start))
    return out


def _resolve_scope(text: str, section: str) -> tuple[int, int, str]:
    if not section:
        return 0, len(text), "全文"
    want = section.strip().strip("【】")
    secs = _sections(text)
    for name, start, length in secs:
        if name == want:
            return start, start + length, name
    fuzzy = [(n, s, ln) for n, s, ln in secs if n.startswith(want)]
    if len(fuzzy) == 1:
        return fuzzy[0][1], fuzzy[0][1] + fuzzy[0][2], fuzzy[0][0]
    names = "、".join(n for n, _, _ in secs)
    raise ValueError(f"没有这一段：{want}。现有段落：{names}")


def _line_diff(old: str, new: str) -> str:
    a, b = old.splitlines(), new.splitlines()
    for idx in range(min(len(a), len(b))):
        if a[idx] != b[idx]:
            return f"L{idx + 1}\n- {a[idx][:160]}\n+ {b[idx][:160]}"
    if len(a) == len(b):
        return "（内容等价）"
    return f"行数 {len(a)} -> {len(b)}"


def _is_admin(event: AstrMessageEvent) -> bool:
    try:
        if event.is_admin():
            return True
    except Exception:
        pass
    try:
        admins = [str(x) for x in _load_cfg().get("admins_id", [])]
        return str(event.get_sender_id()) in admins
    except Exception:
        return False


def _snippet(text: str, limit: int = 60) -> str:
    one = " ".join(text.split())
    return one if len(one) <= limit else one[: limit - 1] + "…"


# ------------------------------------------------------------------ 读对话


def _lm_turns(umo: str, since_id: int | None, max_turns: int) -> tuple[list[dict], int | None, float | None]:
    """只取上次反思之后的新对话，按 id 升序；看过的一条不会再取第二遍。"""
    if not LM_DB.exists():
        return [], None, None
    conn = sqlite3.connect(f"file:{LM_DB}?mode=ro", uri=True)
    limit = max_turns * 4
    try:
        if since_id:
            rows = conn.execute(
                "select id, role, content, timestamp from messages "
                "where session_id = ? and id > ? order by id asc limit ?",
                (umo, int(since_id), limit),
            ).fetchall()
        else:
            rows = conn.execute(
                "select id, role, content, timestamp from ("
                "  select id, role, content, timestamp from messages "
                "  where session_id = ? order by id desc limit ?"
                ") order by id asc",
                (umo, limit),
            ).fetchall()
    except sqlite3.Error as exc:
        logger.warning(f"[self_reflect] 读流水失败：{exc}")
        return [], None, None
    finally:
        conn.close()

    out: list[dict] = []
    last_id, last_ts = since_id, None
    for mid, role, content, ts in rows:
        if role not in ("user", "assistant"):
            continue
        body = _REMINDER_RE.sub("", (content or "")).strip()
        if not body:
            continue
        out.append({"id": mid, "role": role, "text": body, "ts": ts})
        last_id, last_ts = mid, ts
    user_idx = [i for i, t in enumerate(out) if t["role"] == "user"]
    if len(user_idx) > max_turns:
        # 这一批装不下，多的留给下一回，绝不砍掉新的
        out = out[:user_idx[max_turns]]
        last_id, last_ts = out[-1]["id"], out[-1]["ts"]
    return out, last_id, last_ts


def _read_turns(umo: str) -> list[dict]:
    """从 conversations 表里把这条会话的 LLM 视角对话取出来。"""
    if not DB_PATH.exists():
        return []
    conn = sqlite3.connect(f"file:{DB_PATH}?mode=ro", uri=True)
    try:
        row = conn.execute(
            "select content from conversations where user_id = ? order by updated_at desc limit 1",
            (umo,),
        ).fetchone()
    except sqlite3.Error as exc:
        logger.warning(f"[self_reflect] 读会话失败：{exc}")
        return []
    finally:
        conn.close()
    if not row or not row[0]:
        return []
    try:
        raw = json.loads(row[0])
    except Exception:  # noqa: BLE001
        return []

    turns: list[dict] = []
    for msg in raw:
        role = msg.get("role")
        if role not in ("user", "assistant"):
            continue
        parts = msg.get("content")
        texts: list[str] = []
        if isinstance(parts, str):
            texts.append(parts)
        elif isinstance(parts, list):
            for part in parts:
                if not isinstance(part, dict):
                    continue
                if part.get("type") == "text" and part.get("text"):
                    texts.append(str(part["text"]))
                elif part.get("type") == "image":
                    texts.append("[图]")
        body = _REMINDER_RE.sub("", "\n".join(texts)).strip()
        if not body:
            continue
        turns.append({"role": role, "text": body})
    return turns


def _slice_new(turns: list[dict], state: dict, fallback: int, lookback: int) -> tuple[list[dict], bool]:
    """用上一轮最后一条用户消息当锚点，切出新对话。找不到锚点就退回最近若干轮。"""
    sig = state.get("last_user_sig")
    start = None
    if sig:
        for i in range(len(turns) - 1, -1, -1):
            if turns[i]["role"] == "user" and hashlib.md5(turns[i]["text"].encode()).hexdigest() == sig:
                start = i + 1
                break
    if start is None:
        counts = [i for i, t in enumerate(turns) if t["role"] == "user"]
        start = counts[-fallback] if len(counts) > fallback else 0
        fresh = True
    else:
        fresh = False
    out = turns[start:]
    # 一轮算两条消息，卡太多了从前面丢掉
    while len(out) > lookback * 2:
        out.pop(0)
    return out, fresh


def _fmt_dialog(turns: list[dict], budget: int) -> tuple[str, int, list[dict]]:
    """从旧到新往后攒，攒满预算就停；装不下的原样退回去，下一回接着看。"""
    lines: list[str] = []
    used = 0
    for i, t in enumerate(turns):
        who = "用户" if t["role"] == "user" else "我"
        line = f"[{who}] {t['text']}"
        if used + len(line) + 1 > budget and i > 0:
            turns = turns[:i]
            break
        lines.append(line)
        used += len(line) + 1
    rounds = sum(1 for t in turns if t["role"] == "user")
    return "\n".join(lines), rounds, turns


# ------------------------------------------------------------------ 主类


def _importance(turns: list[dict]) -> float:
    """这堆对话值不值得动人格。0~1，只看形状，不看内容。"""
    users = [t for t in turns if t.get("role") == "user"]
    if not users:
        return 0.0
    lens = sorted(len(str(t.get("content") or t.get("text") or "")) for t in users)
    med = lens[len(lens) // 2]
    depth = min(1.0, med / 30.0)
    vol = min(1.0, len(users) / 40.0)
    bots = len([t for t in turns if t.get("role") == "assistant"])
    share = len(users) / max(1, len(users) + bots)
    q = len([t for t in users
             if "?" in str(t.get("content") or t.get("text") or "")
             or "？" in str(t.get("content") or t.get("text") or "")]) / max(1, len(users))
    return 0.45 * depth + 0.25 * vol + 0.15 * share + 0.15 * min(1.0, q / 0.4)


def _split_conf(patches: list[dict], min_conf: float) -> tuple[list[dict], list[dict]]:
    """按置信度分两堆：够格的去落地，不够的只报不落。没标 confidence 的放行。"""
    ok, low = [], []
    for p in patches:
        try:
            conf = float(p.get("confidence"))
        except (TypeError, ValueError):
            ok.append(p)
            continue
        (ok if conf >= min_conf else low).append(dict(p, _conf=conf))
    return ok, low

@register(
    "astrbot_plugin_auto_evolve",
    "YG",
    "自主进化 · AutoEvolve：定时复盘对话与提示词，自己写补丁、自己验收，形成越用越准的进化闭环",
    "1.0.0",
)
class SelfReflect(Star):
    def __init__(self, context: Context, config: dict | None = None):
        super().__init__(context)
        self.conf = config if config is not None else {}
        self._task: asyncio.Task | None = None
        self._state = self._load_state()

    # ---------------- 配置

    def _c(self, group: str, key: str, default):
        try:
            val = (self.conf.get(group) or {}).get(key, default)
        except Exception:  # noqa: BLE001
            return default
        if val is None:
            return default
        if isinstance(val, str) and not val.strip() and default != "":
            return default
        return val

    @property
    def umo(self) -> str:
        raw = str(self._c("基本设置", "target_umo", "") or "").strip()
        if raw:
            return raw
        event = getattr(self, "_event", None)
        return str(getattr(event, "unified_msg_origin", "") or "").strip()

    # ---------------- 状态

    def _load_state(self) -> dict:
        SELF_DIR.mkdir(parents=True, exist_ok=True)
        if STATE_PATH.exists():
            try:
                return json.loads(STATE_PATH.read_text(encoding="utf-8"))
            except Exception:  # noqa: BLE001
                logger.warning("[self_reflect] state.json 坏了，重开一个")
        return {"last_run": None, "last_slot": None, "last_user_sig": None,
                "last_summary": "", "pending": {}, "history": [], "seq": 0}

    def _save_state(self) -> None:
        SELF_DIR.mkdir(parents=True, exist_ok=True)
        STATE_PATH.write_text(
            json.dumps(self._state, ensure_ascii=False, indent=1), encoding="utf-8"
        )

    # ---------------- 生命周期

    async def initialize(self) -> None:
        if self._task and not self._task.done():
            return
        self._task = asyncio.create_task(self._loop())
        logger.info("[self_reflect] 调度已启动")

    async def terminate(self) -> None:
        if self._task and not self._task.done():
            self._task.cancel()

    async def _loop(self) -> None:
        await asyncio.sleep(8)
        while True:
            try:
                if self._c("基本设置", "enabled", True):
                    await self._tick()
            except asyncio.CancelledError:
                raise
            except Exception as exc:  # noqa: BLE001
                logger.error(f"[self_reflect] 调度出错：{exc}\n{__import__('traceback').format_exc()}")
            await asyncio.sleep(30)

    async def _tick(self) -> None:
        now = time.localtime()
        hhmm = f"{now.tm_hour:02d}:{now.tm_min:02d}"
        slots = self._c("基本设置", "schedule_times", ["04:00"]) or []
        if hhmm not in [str(s).strip() for s in slots]:
            return
        mark = f"{time.strftime('%Y-%m-%d')} {hhmm}"
        if self._state.get("last_slot") == mark:
            return
        # 两道闸：距上次至少隔这么久，不然一天两次也只是把同一批话翻来覆去改
        gap_h = float(self._c("基本设置", "min_gap_hours", 12.0))
        last_ts = float(self._state.get("last_run_ts") or 0)
        if last_ts and time.time() - last_ts < gap_h * 3600:
            logger.info("[self_reflect] 距上次不到 %.0f 小时，这轮跳过", gap_h)
            return
        self._state["last_slot"] = mark
        self._save_state()
        logger.info(f"[self_reflect] 到点，开始复盘 {mark}")
        await self.run_reflection(notify=True)

    # ---------------- 反思主流程

    async def run_reflection(self, notify: bool = True, force: bool = False) -> dict:
        uno = self.umo
        if not uno:
            return {"ok": False, "msg": "还没设复盘哪个会话（配置 → 基本设置 → target_umo）"}
        lookback = int(self._c("基本设置", "lookback_turns", 80))
        fallback = int(self._c("基本设置", "first_run_turns", 40))

        since_id = self._state.get("last_msg_id")
        turns, new_id, new_ts = _lm_turns(uno, since_id, lookback if since_id else fallback)
        fresh = True
        if not turns:
            # 流水读不到就退回框架自己存的那点上下文
            turns_all = _read_turns(uno)
            if not turns_all:
                return {"ok": False, "msg": "没读到对话"}
            turns, fresh = _slice_new(turns_all, self._state, fallback, lookback)
            new_id, new_ts = None, None
        n_user = len([t for t in turns if t["role"] == "user"])
        tier2 = int(self._c("基本设置", "tier2_turns", 0) or
                    self._c("基本设置", "min_new_turns", 20))
        tier1 = int(self._c("基本设置", "tier1_turns", 8))
        if not force and n_user < tier1:
            return {"ok": False, "msg": "这段时间新对话太少，不值得动人格"}
        if not force and n_user < tier2:
            log = self._state.setdefault("tier1_log", [])
            log.append({"at": time.strftime("%Y-%m-%d %H:%M:%S"), "turns": n_user,
                        "score": round(_importance(turns), 3)})
            del log[:-40]
            self._save_state()
            return {"ok": False, "msg": f"只记了一笔，不动人格（{n_user}/{tier2} 轮）"}
        if not force and bool(self._c("人格改法", "gate_enabled", True)):
            score = _importance(turns)
            thr = float(self._c("人格改法", "gate_threshold", 0.35))
            if score < thr:
                self._state["last_gate"] = {"at": time.strftime("%Y-%m-%d %H:%M:%S"),
                                            "score": round(score, 3), "threshold": thr}
                self._save_state()
                return {"ok": False,
                        "msg": f"这几天聊得太薄（信息量 {score:.2f} < {thr}），不值得动人格"}

        budget = int(self._c("基本设置", "max_input_chars", 40000))
        dialog, rounds, used = _fmt_dialog(turns, budget)
        if used:
            turns = used
            if new_id is not None:
                new_id = turns[-1].get("id", new_id)
                new_ts = turns[-1].get("ts", new_ts)

        persona_id = str(self._c("人格改法", "persona_id", "default"))
        persona = await _get_persona_async(persona_id)
        prompt_text = str(persona.get("system_prompt") or "")
        if not prompt_text:
            return {"ok": False, "msg": "没读到人格"}

        delta = float(self._c("人格改法", "delta_percent", 8.0))
        loud = _loud_stats(dialog)
        cur = _struct_stats(turns)
        stats = _fmt_struct(cur, self._state.get("last_struct") or {})
        if bool(self._c("人格改法", "mask_input", False)):
            dialog = _mask(dialog)
        sys_prompt = self._build_prompt(delta, prompt_text, dialog, rounds, loud, stats)
        result = await self._ask(sys_prompt)
        if not result:
            return {"ok": False, "msg": "模型没给出可解析的结果"}

        out = await self._apply(result, persona_id, prompt_text, delta,
                                turns, fresh, new_ts, notify=notify, msg_id=new_id)
        if out.get("ok") and cur:
            self._state["last_struct"] = cur
            self._save_state()
        return out

    def _build_prompt(self, delta: float, persona_text: str, dialog: str, rounds: int,
                      loud: str = "", stats: str = "") -> str:
        tpl = str(self._c("提示词", "reflection_prompt", "")).strip() or BUILTIN_PROMPT
        last = self._state.get("last_summary") or "还没有，这是第一次"
        try:
            out = tpl.format(
                delta_percent=delta,
                persona=persona_text,
                conversation=dialog,
                last_reflection=last,
                persona_chars=len(persona_text),
                turn_count=rounds,
            )
        except (KeyError, IndexError):
            out = (
                tpl
                + "\n\n## 上次反思\n" + last
                + f"\n\n## 当前人格（{len(persona_text)} 字）\n" + persona_text
                + f"\n\n## 这段时间的对话（{rounds} 轮）\n" + dialog
            )
        defer = [x for x in (self._state.get("deferred_patches") or []) if isinstance(x, dict)]
        if defer:
            out += ("\n\n## 上一轮没落地的补丁（先判断还成不成立，成立再提一次）\n"
                    + "\n".join("- " + str(x.get("new") or "")[:100] for x in defer[-4:]))
        digest = _obs_digest(self._state.get("history") or [],
                             int(self._c("提示词", "obs_window", 12)))
        if digest:
            out += ("\n\n## 最近反复被指出（自动统计，别当成这轮必须改）\n" + digest)
        block = "\n\n".join(x for x in (stats, loud) if x)
        if not block:
            return out
        # 指标和成绩单要摆在「只输出 JSON」前面，放最后会被当成可忽略的附录
        anchor = "只输出一个 JSON"
        idx = out.rfind(anchor)
        if idx > 0:
            start = out.rfind("\n\n", 0, idx)
            start = start if start > 0 else idx
            return out[:start] + "\n\n" + block + "\n" + out[start:]
        return out + "\n\n" + block

    async def _ask(self, prompt: str) -> dict | None:
        provider = self.context.get_using_provider(self.umo)
        pid = str(self._c("提示词", "provider_id", "")).strip()
        if pid:
            try:
                provider = self.context.get_provider_by_id(pid) or provider
            except Exception:  # noqa: BLE001
                pass
        if provider is None:
            logger.warning("[self_reflect] 没有可用的模型")
            return None
        async def _call(p, p_text: str):
            return await p.text_chat(
                prompt=p_text,
                system_prompt="照提示词干活，只回 JSON。",
                contexts=[],
            )

        try:
            resp = await asyncio.wait_for(_call(provider, prompt), timeout=100)
        except Exception as exc:  # noqa: BLE001
            logger.error(f"[self_reflect] 调模型失败：{exc}")
            try:
                alt = self.context.get_provider_by_id(
                    str(self._c("提示词", "fallback_provider_id", "openai/deepseek-v4.1-flash")))
                if alt is None or alt is provider:
                    return None
                resp = await asyncio.wait_for(_call(alt, prompt), timeout=100)
                logger.info("[self_reflect] 主模型超时，已换备用再试一次")
            except Exception as exc2:  # noqa: BLE001
                logger.error(f"[self_reflect] 备用也失败：{exc2}")
                return None
        text = (getattr(resp, "completion_text", "") or "").strip()
        if text.startswith("```"):
            text = re.sub(r"^```[a-zA-Z]*\s*|\s*```$", "", text).strip()
        m = _JSON_RE.search(text)
        if not m:
            logger.warning("[self_reflect] 返回里没有 JSON")
            return None
        try:
            return json.loads(m.group(0))
        except json.JSONDecodeError:
            logger.warning("[self_reflect] JSON 解析失败")
            return None

    # ---------------- 落地

    async def _verify_patch(self, old_text: str, new_text: str) -> dict:
        """旧人格 vs 新人格，同一批指令各跑一遍，比覆盖率和密度。"""
        if not bool(self._c("验证", "enabled", True)):
            return {"ok": True, "skipped": True, "why": "配置关了"}
        raw_ids = self._c("验证", "prompt_ids", VERIFY_DEFAULT_IDS) or VERIFY_DEFAULT_IDS
        try:
            idxs = [int(x) for x in raw_ids][:24]
        except Exception:  # noqa: BLE001
            idxs = VERIFY_DEFAULT_IDS
        picks = [VERIFY_PROMPTS[i] for i in idxs if 0 <= i < len(VERIFY_PROMPTS)]
        if not picks:
            return {"ok": True, "skipped": True, "why": "没配测试指令"}

        pid = str(self._c("验证", "provider_id", "")).strip()
        provider = None
        if pid:
            try:
                provider = self.context.get_provider_by_id(pid)
            except Exception:  # noqa: BLE001
                provider = None
        if provider is None:
            try:
                provider = self.context.get_using_provider(self.umo)
            except Exception:  # noqa: BLE001
                provider = None
        if provider is None:
            return {"ok": True, "skipped": True, "why": "没有可用模型"}

        def _pack(msg: str) -> str:
            lines = ["（接着刚才的对话往下说，不要复述前情）"]
            for r, c in VERIFY_HIST:
                lines.append(("用户：" if r == "user" else "我：") + c)
            lines.append("用户：" + msg)
            return "\n".join(lines)

        async def _one(persona: str, msg: str) -> str:
            try:
                resp = await asyncio.wait_for(
                    provider.text_chat(prompt=_pack(msg), system_prompt=persona, contexts=[]),
                    timeout=90)
                return (getattr(resp, "completion_text", "") or "").strip()
            except Exception as exc:  # noqa: BLE001
                logger.warning(f"[self_reflect] 验证采样失败：{exc}")
                return ""

        # 每条跑 repeat 遍。单遍方差太大：同一个 prompt 两次采样，水覆盖能从 56% 掉到 22%，
        # 不重复的话验证器自己就会瞎拦（实测旧=新也有一半概率判不过）。
        try:
            repeat = max(1, min(3, int(self._c("验证", "repeat", 2))))
        except Exception:  # noqa: BLE001
            repeat = 2

        old_out, new_out, by_cat = [], [], {}
        for cat, msg in picks:
            o, nw = [], []
            for _ in range(repeat):
                o.append(await _one(old_text, msg))
                nw.append(await _one(new_text, msg))
            old_out += o
            new_out += nw
            by_cat.setdefault(cat, []).append("\n".join(x for x in nw if x))

        if not any(old_out) or not any(new_out):
            return {"ok": True, "skipped": True, "why": "采样全是空"}

        b, c = _v_metrics(old_out), _v_metrics(new_out)
        bad = _v_verdict(b, c)

        # 采样文本的结构面：模板句堆在一处时，覆盖率和密度都看不出来，只有句尾会重复。
        struct = None
        if bool(self._c("验证", "struct_check", True)):
            so, sn = _v_struct(old_out), _v_struct(new_out)
            struct = {"base": so, "cand": sn,
                      "note": (f"句尾复用 {so['tail_dup']:.0%}→{sn['tail_dup']:.0%}、"
                               f"收尾种类 {so['tail_kinds']}→{sn['tail_kinds']}")}
            if so["paras"] and sn["paras"] and sn["tail_dup"] > max(0.35, so["tail_dup"] + 0.1):
                bad.append(f"句尾复用 {so['tail_dup']:.0%}→{sn['tail_dup']:.0%}，模板化变重")

        # 工程组两个专属指标。不带工具的纯文本采样里，正文出现 {"name": 就是在漏工具调用；
        # 首句是不是结论，决定用户要不要往下读。
        eng = [x for x in (by_cat.get("工程") or []) if x.strip()]
        if eng:
            concl = sum(1 for x in eng if _first_is_conclusion(x)) / len(eng)
            tools = sum(len(re.findall(r'\{\s*"name"\s*:', x)) for x in eng)
            c["concl"], c["toolcall"] = concl, tools
            if tools:
                bad.append(f"工程组正文冒出工具调用 {tools} 处")
            if concl < 0.5:
                bad.append(f"工程组首句即结论 {concl:.0%}")
        groups = {k: len(v) for k, v in by_cat.items()}
        logger.info(f"[self_reflect] 验证 {len(picks)} 条：旧 {b} / 新 {c} → {'过' if not bad else '拦'}")
        return {"ok": not bad, "bad": bad, "base": b, "cand": c, "n": len(picks),
                "groups": groups, "struct": struct,
                "old": old_out, "new": new_out}

    async def _apply(self, result: dict, persona_id: str, persona_text: str,
                     delta: float, turns: list[dict], fresh: bool, msg_ts: float | None,
                     notify: bool, msg_id: int | None = None) -> dict:
        dry = bool(self._c("人格改法", "dry_run", False))
        patches = [p for p in (result.get("persona_patches") or []) if isinstance(p, dict)]
        limit = int(self._c("人格改法", "max_persona_patches", 4))
        patches, low_conf = _split_conf(patches, float(self._c("人格改法", "min_confidence", 0.7)))
        patches = patches[:limit]
        for _p in low_conf:
            skipped.append({"reason": f"置信度 {_p.get('_conf')} 低于 0.7，不落："
                                      f"{str(_p.get('section') or '')} {str(_p.get('new') or '')[:30]}"})

        # 分桶：persona 落人格，lexicon 落词表，其余层只提示。
        # 一轮里 persona 最多 N 条 —— 提四条落两条的时候，回执说四件，用户没法判断批了什么。
        persona_items = [p for p in patches if str(p.get("layer") or "persona") == "persona"]
        lex_items = [p for p in patches if str(p.get("layer") or "") == "lexicon"]
        other_items = [p for p in patches
                       if p not in persona_items and p not in lex_items]
        try:
            per_round = max(1, min(6, int(self._c("人格改法", "persona_per_round", 2))))
        except Exception:  # noqa: BLE001
            per_round = 2
        overflow = persona_items[per_round:]
        persona_items = persona_items[:per_round]
        if overflow:
            bag = [x for x in (self._state.get("deferred_patches") or []) if isinstance(x, dict)]
            bag += [dict(x, at=time.strftime("%Y-%m-%d %H:%M:%S")) for x in overflow]
            self._state["deferred_patches"] = bag[-20:]

        applied, skipped = [], []
        new_text = persona_text
        if overflow:
            skipped.append({"reason": f"另 {len(overflow)} 条 persona 补丁转下一轮（每轮上限 {per_round}）"})
        for x in other_items:
            skipped.append({"reason": f"layer={x.get('layer') or '没标'}，只提示不落地："
                                      f"{str(x.get('reason') or '')[:40]}"})
        if lex_items and not dry:
            lid = self._queue_patch("lexicon", {"items": lex_items[:8]}, note="词表补丁")
            queued_ids_pre = lid
            skipped.append({"reason": f"词表补丁已排队 #{lid}，等 /批 {lid} go"})
        if persona_items and not dry:
            new_text, applied, skipped2 = self._apply_persona(new_text, persona_items)
            skipped += skipped2
            # 人格一周内只能长这么多。四条以上还全写进人格，得说明为什么不能放别处。
            if len(applied) > 3:
                whys = [str(p.get("why") or "").strip() for p in patches
                        if str(p.get("why") or "").strip()]
                if len(whys) < len(applied):
                    skipped.append({"patch": f"{len(applied)} 条",
                                    "reason": "四条以上都进人格，没写「为什么不能放别处」"})

        changed_ratio = (len(new_text) - len(persona_text)) / max(1, len(persona_text)) * 100
        enforcement = bool(self._c("人格改法", "enforce_delta", True))
        over_budget = abs(changed_ratio) > delta + 0.01

        # 累计漂移：单次合规不代表整体没跑偏。拿第一次见到的人格当锚，
        # 一天两次、每次 ±10%，两周就能把人格换掉一个人，所以这条必须单独算。
        base = str(self._state.get("baseline_text") or "")
        prev = str(self._state.get("last_persona_text") or "")
        manual_reset = False
        if prev and prev != persona_text:
            # 有人绕过插件改了人格（她自己也改）。相似度不能当判据：改两句也还有
            # 0.98，永远撞不到 0.7，旧基线就会把每轮都判成「累计漂移超限」，
            # 顺带把采样验证整段跳过。一个字不一样就换尺子。
            base, manual_reset = persona_text, True
        if not base:
            base = persona_text
        drift = (len(new_text) - len(base)) / max(1, len(base)) * 100
        drift_limit = float(self._c("人格改法", "max_total_drift_percent", 15.0))
        over_drift = abs(drift) > drift_limit + 0.01

        # 锚点：purge 那边锁着 8 句，删了它每 10 分钟报一次 MISS。整批不收，也不排队。
        if applied and not dry:
            gone = _anchor_miss(new_text)
            if gone:
                skipped += [{"reason": "锚点会被删：" + "、".join(gone)}]
                applied, new_text, changed_ratio = [], persona_text, 0.0

        # 落地前两道关：先做人格体检（确定性，算拦截依据），再跑一遍采样（只做参考）
        verify_fail, verify_note = False, ""
        queued: list = []
        lint_bad = _persona_lint(persona_text, new_text) if (applied and not dry) else []
        if lint_bad:
            verify_fail = True
            verify_note = "体检没过：" + "；".join(lint_bad)
            skipped.append({"reason": verify_note})
        elif applied and not dry and not over_drift:
            try:
                v = await self._verify_patch(persona_text, new_text)
                if v.get("skipped"):
                    verify_note = f"采样跳过：{v.get('why') or '没跑成'}"
                elif v.get("bad"):
                    # 采样波动本来就压过人格差异，只提示，不拦
                    verify_note = ("采样提示（不拦，随机性太大）：" + "；".join(v["bad"])
                                   + f"（{v.get('n')} 条）")
                else:
                    verify_note = (f"采样正常（{v.get('n')} 条）："
                                   f"字数 {v['base']['len']:.0f}→{v['cand']['len']:.0f}、"
                                   f"口语词 {v['base']['oral']:.1f}→{v['cand']['oral']:.1f}、"
                                   f"书面词 {v['base']['book']:.1f}→{v['cand']['book']:.1f}、"
                                   f"主动性 {v['base']['init']:.1f}→{v['cand']['init']:.1f}、"
                                   f"递话 {v['base']['passive']:.0%}→{v['cand']['passive']:.0%}")
                    if v.get("struct"):
                        verify_note += "；结构 " + v["struct"]["note"]
            except Exception as exc:  # noqa: BLE001
                logger.warning(f"[self_reflect] 验证器挂了：{exc}")
                verify_note = "验证器出错，按没过处理"
                verify_fail = True

        persona_done = False
        if applied and over_budget and enforcement:
            skipped += [{"reason": f"字数变化 {changed_ratio:+.1f}% 超过 {delta}%"}]
            applied, new_text, changed_ratio, persona_done = [], persona_text, 0.0, False
        elif applied:
            auto_ok = bool(self._c("人格改法", "auto_apply_persona", False))
            if over_drift:
                skipped += [{"reason": f"累计漂移 {drift:+.1f}% 超过 {drift_limit}%，转人工"}]
            if dry or not auto_ok or over_drift or verify_fail:
                if not over_drift and not verify_fail:
                    skipped += [{"reason": "等你点头"}]
                # 存打上的那几条就够。存全量会把没对上的也塞进包里，批的时候
                # 预览说 4 条、落地只 2 条，用户没法判断自己批了什么。
                pack = applied or [p for p in (result.get("persona_patches") or [])
                                   if isinstance(p, dict)]
                self._queue_patch("persona", {"persona_id": persona_id,
                                             "system_prompt": new_text,
                                             "old_chars": len(persona_text),
                                             "new_chars": len(new_text),
                                             "drift": round(drift, 1),
                                             "verify": verify_note,
                                             "baseline_chars": len(base),
                                             "patches": [{"section": x.get("section"),
                                                          "layer": x.get("layer"),
                                                          "why": x.get("why"),
                                                          "old": x.get("old"),
                                                          "new": x.get("new"),
                                                          "reason": x.get("reason"),
                                                          "confidence": x.get("confidence"),
                                                          "risk": _risk_note(x.get("old"), x.get("new"))}
                                                         for x in pack][:8]},
                                  note=result.get("note_for_owner", ""))
                queued.append(str(self._state.get("seq")))
            else:
                await self._commit_persona(persona_id, persona_text, new_text)
                persona_done = True

        self._state["baseline_text"] = base
        self._state["last_persona_text"] = new_text if persona_done else persona_text
        if manual_reset:
            logger.info("[self_reflect] 人格被手改过，漂移基线已重置")

        code_items = [p for p in (result.get("code_patches") or []) if isinstance(p, dict)]
        code_items = code_items[: int(self._c("代码补丁", "max_code_patches", 2))]
        if code_items and bool(self._c("代码补丁", "code_patch_enabled", True)) and not dry:
            auto_code = bool(self._c("代码补丁", "auto_apply_code", False))
            for item in code_items:
                ok, msg = self._validate_code_patch(item)
                if not ok:
                    skipped.append({"reason": f"代码补丁被拒：{msg}"})
                    continue
                if not auto_code:
                    pid = self._queue_patch("code", item, note=item.get("reason", ""))
                    queued.append(pid)
                    continue
                # 代码补丁不再只排队等人点头：备份 ->
                # 替换 -> py_compile 校验 -> 失败自动回滚，全在 _apply_code_patch 里。
                ok2, detail = self._apply_code_patch(item)
                if ok2:
                    applied.append({
                        "section": "代码",
                        "old": str(item.get("path") or ""),
                        "new": "已应用",
                        "reason": item.get("reason", "") or detail.splitlines()[0],
                    })
                else:
                    skipped.append({"reason": f"代码补丁没落地：{detail}"})

        # 每次反思的观察留一条，攒成画像；只留结论，不留全文（state 别越长越大）。
        obs = [str(x)[:120] for x in (result.get("observations") or []) if str(x).strip()][:6]
        if obs:
            log = [x for x in (self._state.get("obs_log") or []) if isinstance(x, dict)]
            log.append({"at": time.strftime("%Y-%m-%d %H:%M:%S"), "obs": obs,
                        "note": str(result.get("note_for_owner", ""))[:80]})
            self._state["obs_log"] = log[-30:]

        last_sig = None
        for t in reversed(turns):
            if t["role"] == "user":
                last_sig = hashlib.md5(t["text"].encode()).hexdigest()
                break
        self._state["last_user_sig"] = last_sig
        if msg_id is not None:
            self._state["last_msg_id"] = int(msg_id)
        if msg_ts:
            self._state["last_msg_ts"] = msg_ts
        self._state["last_run"] = time.strftime("%Y-%m-%d %H:%M:%S")
        self._state["last_run_ts"] = time.time()
        self._state["last_summary"] = (
            f"{result.get('note_for_owner', '')} | 观察：{'; '.join(map(str, (result.get('observations') or [])[:3]))}"
        )[:900]
        self._state.setdefault("history", []).insert(0, {
            "at": self._state["last_run"],
            "patches_applied": len(applied),
            "chars": [len(persona_text), len(new_text)],
            "pending": queued,
        })
        self._state["history"] = self._state["history"][:20]
        self._save_state()

        focus_notes: list[str] = []
        try:
            focus_notes = await self._evolve_prompt(result, turns)
        except Exception as exc:  # noqa: BLE001
            logger.warning(f"[self_reflect] 提示词演化挂了：{exc}")

        report = self._report(result, applied, skipped, queued, persona_text, new_text,
                              persona_done, dry, focus_notes, verify_note)
        if notify:
            await self._send(report)
        return {"ok": True, "msg": report, "applied": len(applied), "queued": queued}

    def _apply_persona(self, text: str, patches: list[dict]) -> tuple[str, list, list]:
        applied, skipped = [], []
        cur = text
        for p in patches:
            layer = str(p.get("layer") or "").strip().lower()
            old, new = str(p.get("old") or ""), str(p.get("new") or "")
            if layer not in PERSONA_LAYERS:
                skipped.append({"patch": _snippet(new or old or "空"),
                                "reason": "没标 layer（persona/rules/description/outbound/lexicon 五选一）"})
                continue
            if layer != "persona":
                # 词表、description、出站补丁不进人格。这条只做提示，不动文本。
                skipped.append({"patch": _snippet(new or old),
                                "reason": f"这条属于 {layer} 层，不进人格 —— 该改词表/description/出站补丁"})
                continue
            if not old or old == new:
                skipped.append({"patch": _snippet(old or "空"), "reason": "空补丁"})
                continue
            cnt = cur.count(old)
            if cnt != 1:
                skipped.append({"patch": _snippet(old), "reason": f"原文命中 {cnt} 次，不唯一"})
                continue
            _ln = cur.count("\n", 0, cur.index(old)) + 1
            dup = _dup_line(cur, new, skip=tuple(range(_ln, _ln + old.count("\n") + 1)))
            if dup:
                skipped.append({"patch": _snippet(new), "reason": dup})
                continue
            cur = cur.replace(old, new, 1)
            applied.append({"section": p.get("section", ""), "old": old, "new": new,
                            "reason": p.get("reason", "")})
        return cur, applied, skipped

    async def _commit_persona(self, persona_id: str, old_text: str, new_text: str) -> None:
        body = await _get_persona_async(persona_id)
        _write_backup("persona", body)
        body["system_prompt"] = new_text
        await _put_persona_async(persona_id, body)
        _write_backup("persona-text", {"before": old_text, "after": new_text})
        logger.info(f"[self_reflect] 人格已更新 {len(old_text)} -> {len(new_text)} 字")

    def _validate_code_patch(self, item: dict) -> tuple[bool, str]:
        p = str(item.get("path") or "").strip().replace("\\", "/")
        old = str(item.get("old") or "")
        if not p or not old:
            return False, "缺 path 或 old"
        if not p.endswith(".py"):
            return False, "只收 .py"
        target, zone = _resolve_target(p)
        if target is None:
            return False, zone
        allowed = [str(x).strip().strip("/") for x in (self._c("代码补丁", "allowed_dirs", []) or []) if str(x).strip()]
        # 白名单只管绿区；留空 = 整个 plugins 目录。黄区按 YELLOW_PREFIXES 放行。
        if zone == "green" and allowed and not any(p == d or p.startswith(d + "/") for d in allowed):
            return False, f"{p} 不在白名单里"
        if "[keep:" in old:
            return False, "改动包含受保护标记，会和补丁系统打架"
        src = target.read_text(encoding="utf-8", errors="replace")
        cnt = src.count(old)
        if cnt != 1:
            return False, f"原文命中 {cnt} 次，不唯一"
        return True, ""

    def _archive_pending(self) -> int:
        """批过/撤过的从 pending 挪进 pending_archive。留着只会让 /补丁 一直变长。"""
        pend = self._state.get("pending") or {}
        arch = self._state.setdefault("pending_archive", [])
        moved = 0
        for k in list(pend):
            v = pend.get(k) or {}
            if str(v.get("status") or "pending") in ("pending", "", "queued"):
                continue
            arch.insert(0, {"id": k, "kind": v.get("kind"), "at": v.get("at"),
                            "status": v.get("status"),
                            "note": str(v.get("note") or "")[:120]})
            pend.pop(k, None)
            moved += 1
        del arch[60:]
        if moved:
            self._state["pending"] = pend
            self._save_state()
        return moved

    def _queue_patch(self, kind: str, payload: dict, note: str = "") -> int:
        self._archive_pending()
        self._state["seq"] = int(self._state.get("seq", 0)) + 1
        pid = self._state["seq"]
        self._state.setdefault("pending", {})[str(pid)] = {
            "kind": kind, "payload": payload, "note": note,
            "at": time.strftime("%Y-%m-%d %H:%M:%S"), "status": "pending",
        }
        self._save_state()
        return pid

    # ---------------- 提示词自我演化

    def _cfg_json(self) -> Path:
        if CFG_JSON.exists():
            return CFG_JSON
        cands = sorted((DATA_DIR / "config").glob("*self_reflect_config.json"))
        return cands[0] if cands else CFG_JSON

    def _focus_block(self, texts: list[str]) -> str:
        # 这段最后要过 .format()，花括号先替成双的
        safe = [str(t).replace("{", "{{").replace("}", "}}") for t in texts]
        lines = [FOCUS_TITLE, FOCUS_OPEN] + [f"- {t}" for t in safe] + [FOCUS_CLOSE]
        return "\n".join(lines)

    def _splice_focus(self, tpl: str, texts: list[str]) -> str:
        block = self._focus_block(texts)
        pat = r"## 最近用户反复看重的[^\n]*\n" + re.escape(FOCUS_OPEN) + r".*?" + re.escape(FOCUS_CLOSE)
        if re.search(pat, tpl, re.S):
            return re.sub(pat, lambda _m: block, tpl, count=1, flags=re.S)
        if FOCUS_OPEN in tpl and FOCUS_CLOSE in tpl:
            body = "\n".join(f"- {t}" for t in texts)
            return re.sub(re.escape(FOCUS_OPEN) + r".*?" + re.escape(FOCUS_CLOSE),
                          lambda _m: FOCUS_OPEN + "\n" + body + "\n" + FOCUS_CLOSE, tpl, count=1, flags=re.S)
        return tpl.rstrip() + "\n\n" + block + "\n"

    async def _evolve_prompt(self, result: dict, turns: list[dict]) -> list[str]:
        """跑完反思后，把用户最近反复在意的点补进反思提示词。"""
        if not bool(self._c("提示词演化", "enabled", True)):
            return []
        st = self._state.setdefault("focus", {"items": []})
        items = [x for x in (st.get("items") or []) if isinstance(x, dict) and str(x.get("text", "")).strip()]
        have = [str(x["text"]) for x in items]
        today = time.strftime("%Y-%m-%d")
        recent = "\n".join(
            f"{'用户' if t['role'] == 'user' else '我'}：{_snippet(t['text'], 110)}" for t in turns[-16:])
        ask = (
            "你在维护一份反思提示词，顺手补几句「最近该盯着什么」。\n"
            "看下面这次的观察和最近的对话，挑出用户反复在意、反复纠正、明说要你以后照做的点，最多 3 条。\n"
            "已有的别重复；不写「我要更努力」这种空话；不写某一天的具体琐事；不写人格里已经定死的规矩。\n\n"
            "## 已有侧重\n" + ("\n".join(f"- {x}" for x in have) or "（还没有）") +
            "\n\n## 这次的观察\n" + json.dumps((result.get("observations") or [])[:10], ensure_ascii=False) +
            "\n\n## 最近对话\n" + recent +
            '\n\n只回 JSON：{"focus": ["一句话"]}。每条不超过 40 字，称呼一律用「用户」，不带编号。'
        )
        got = await self._ask(ask)
        if not isinstance(got, dict):
            return []
        raw = got.get("focus")
        if not isinstance(raw, list):
            return []
        min_hits = max(1, int(self._c("提示词演化", "min_hits", 2)))
        max_focus = max(1, int(self._c("提示词演化", "max_focus", 8)))
        cap = max(80, int(self._c("提示词演化", "max_chars", 420)))
        for one in raw[:3]:
            txt = re.sub(r"\s+", "", str(one) if one is not None else "")[:48].strip("。！？；，、…")
            if not txt:
                continue
            hit = None
            for it in items:
                if difflib.SequenceMatcher(None, str(it["text"]), txt).ratio() >= float(
                        self._c("提示词演化", "match_ratio", 0.35)):
                    hit = it
                    break
            if hit is not None:
                hit["hits"] = int(hit.get("hits", 0)) + 1
                # 只加票，不覆盖原句。每次换个说法就重写一遍，攒的不是「用户反复在意的」，
                # 是「上一轮那次生成恰好怎么写的」。
                hit["last"] = today
            else:
                items.append({"text": txt, "hits": 1, "first": today, "last": today})
        # 条目寿命：太久没再撞上的减票，减到 0 就滚。不然提示词只会越来越长，
        # 半年前的临时侧重会一直占着位置。
        decay_days = float(self._c("提示词演化", "decay_days", 30.0))

        def _age(s: str) -> float:
            try:
                return (time.time() - time.mktime(time.strptime(s, "%Y-%m-%d"))) / 86400
            except Exception:  # noqa: BLE001
                return 0.0

        for it in items:
            if _age(str(it.get("last") or it.get("first") or today)) >= decay_days:
                it["hits"] = int(it.get("hits", 0)) - 1
        items = [x for x in items if int(x.get("hits", 0)) > 0]

        items.sort(key=lambda x: (-int(x.get("hits", 0)), str(x.get("last", ""))))
        keep, total = [], 0
        for it in items:
            if len(keep) >= max_focus:
                break
            if total + len(str(it["text"])) > cap:
                continue
            keep.append(it)
            total += len(str(it["text"]))
        st["items"] = keep
        st["updated"] = time.strftime("%Y-%m-%d %H:%M")
        self._save_state()

        live = [str(x["text"]) for x in keep if int(x.get("hits", 0)) >= min_hits]
        if not live:
            fresh = [str(x["text"]) for x in keep if int(x.get("hits", 0)) < min_hits]
            return [f"还在攒，第二次撞上才写进去：{_snippet('；'.join(fresh), 40)}"] if fresh else []
        tpl = str(self._c("提示词", "reflection_prompt", ""))
        if not tpl:
            return []
        new_tpl = self._splice_focus(tpl, live)
        if new_tpl == tpl:
            return []
        try:
            fp = self._cfg_json()
            BACKUP_DIR.mkdir(parents=True, exist_ok=True)
            if fp.exists():
                (BACKUP_DIR / f"config-{time.strftime('%Y%m%d-%H%M%S')}.json").write_text(
                    fp.read_text(encoding="utf-8"), encoding="utf-8")
            cfg = json.loads(fp.read_text(encoding="utf-8")) if fp.exists() else {}
            cfg.setdefault("提示词", {})["reflection_prompt"] = new_tpl
            fp.write_text(json.dumps(cfg, ensure_ascii=False, indent=2), encoding="utf-8")
            try:
                self.conf.setdefault("提示词", {})["reflection_prompt"] = new_tpl
            except Exception:  # noqa: BLE001
                pass
            out = [f"侧重段已写回，现在 {len(live)} 条"]
            waiting = [str(x["text"]) for x in keep if int(x.get("hits", 0)) < min_hits]
            if waiting:
                out.append("还在攒：" + _snippet("；".join(waiting), 40))
            return out
        except Exception as exc:  # noqa: BLE001
            logger.warning(f"[self_reflect] 写提示词配置没成：{exc}")
            return [f"提示词没写成：{exc.__class__.__name__}"]

    # ---------------- 报告

    def _report(self, result: dict, applied: list, skipped: list, queued: list,
                old_text: str, new_text: str, persona_done: bool, dry: bool,
                focus_notes: list[str] | None = None, verify_note: str = "") -> str:
        head = str(self._c("提示词", "notify_prefix", "反思完了"))
        lines = [f"{head}。"]
        note = result.get("note_for_owner")
        if note:
            lines.append(str(note))

        marks = ["一", "二", "三", "四", "五", "六"]
        pos = 0

        def sec(title: str) -> None:
            nonlocal pos
            mark = marks[pos] if pos < len(marks) else str(pos + 1)
            pos += 1
            lines.append(f"{mark}、{title}")

        if dry:
            lines.append("这回是空跑，一个字都没落。")
        if verify_note:
            lines.append(verify_note)

        if applied:
            sec(f"人格改了 {len(applied)} 处")
            for a in applied:
                lines.append(f"· 「{a['section'] or '没标段名'}」：原来的「{_snippet(a['old'], 26)}」"
                             f"换成「{_snippet(a['new'], 26)}」")
        elif persona_done:
            sec("人格没动")

        ledger = [x for x in (result.get("kink_ledger") or []) if isinstance(x, dict)]
        missing = [x for x in ledger
                   if str(x.get("in_persona", "")).strip() in ("缺", "无", "-", "没有", "")]
        if missing:
            sec(f"台账里 {len(missing)} 条人格还没写")
            for x in missing[:4]:
                quote = _snippet(str(x.get("owner_quote", "")).strip(), 18)
                tail = f"（你说「{quote}」）" if quote else ""
                lines.append(f"· {_snippet(str(x.get('kink', '')).strip(), 16)}{tail}")

        fixes = result.get("corrections") or []
        if fixes:
            sec("这期间你纠正过我")
            for c in fixes[:4]:
                lines.append(f"· 你说「{_snippet(str(c.get('owner_said', '')), 26)}」，"
                             f"我错在{_snippet(str(c.get('my_fault', '')), 40)}")

        if queued:
            sec(f"有 {len(queued)} 条补丁等你点头")
            for i, x in enumerate((result.get("persona_patches") or [])[:4], 1):
                if not isinstance(x, dict):
                    continue
                lines.append(f"· 第 {i} 条，动的是「{x.get('section') or '没标段名'}」："
                             f"把「{_snippet(str(x.get('old', '')), 22)}」"
                             f"换成「{_snippet(str(x.get('new', '')), 22)}」")
                if x.get("reason"):
                    lines.append(f"  为啥：{_snippet(str(x['reason']), 40)}")
            lines.append(f"回「批 {queued[0]}」我就动手，回「撤 {queued[0]}」就不要了。")

        if skipped:
            sec("没落下的")
            for s in skipped[:3]:
                lines.append(f"· {_snippet(str(s.get('reason', '')), 40)}")

        if focus_notes:
            sec("提示词侧重")
            for x in focus_notes[:3]:
                lines.append(f"· {_snippet(str(x), 46)}")

        return "\n".join(lines)

    async def _send(self, text: str) -> None:
        try:
            if MessageChain is None or Plain is None:
                return
            await self.context.send_message(self.umo, MessageChain([Plain(text)]))
        except Exception as exc:  # noqa: BLE001
            logger.warning(f"[self_reflect] 发消息失败：{exc}")

    # ---------------- 受控自改（自 self_edit 并入）

    @filter.llm_tool(name="self_read_profile")
    async def self_read_profile(
        self,
        event: AstrMessageEvent,
        section: str = "",
        include_dialogs: bool = False,
    ):
        """读你自己的人格文稿。不传 section 只返回目录（每段字数），传了才返回那一段全文。

        Args:
            section(string): 段落名，如「你是谁」「要」「工具」；留空只返回目录
            include_dialogs(boolean): 是否同时返回预设对话，默认 false
        """
        if not _is_admin(event):
            return "只有用户能让你改自己。"
        p = await asyncio.to_thread(_get_persona, "default")
        text = p.get("system_prompt") or ""
        secs = _sections(text)
        head = f"全文 {len(text)} 字符 / {len(secs)} 段"
        index = " · ".join(f"{n}({ln})" for n, _, ln in secs)
        if section:
            try:
                start, end, name = _resolve_scope(text, section)
            except ValueError as exc:
                return f"{head}\n{exc}\n{index}"
            body = text[start:end]
            return f"【{name}】{len(body)} 字符\n\n{body}"
        out = f"{head}\n{index}\n工具：{p.get('tools')}"
        if include_dialogs:
            out += "\n预设：" + " / ".join(d[:40] for d in (p.get("begin_dialogs") or []))
        return out

    @filter.llm_tool(name="self_patch_persona")
    async def self_patch_persona(
        self,
        event: AstrMessageEvent,
        section: str,
        old: str,
        new: str,
    ):
        """改你自己人格里的一段话。old 必须在目标段落里只出现一次；new 留空即删除该句。

        Args:
            section(string): 段落名，如「怎么说话」「要」；留空表示在全文里找
            old(string): 要被替换的原文，必须逐字一致且唯一
            new(string): 替换成的新文本，留空字符串表示删掉
        """
        if not _is_admin(event):
            return "只有用户能让你改自己。"
        p = await asyncio.to_thread(_get_persona, "default")
        text = p.get("system_prompt") or ""
        try:
            start, end, name = _resolve_scope(text, section)
        except ValueError as exc:
            return f"没改。{exc}"
        scope = text[start:end]
        hits = scope.count(old)
        if hits != 1:
            hint = "找不到这句，逐字对齐后再试。" if hits == 0 else f"这句出现 {hits} 次，加长一点让它是唯一的。"
            return f"没改。{hint}"
        patched = scope.replace(old, new, 1)
        result = text[:start] + patched + text[end:]
        if len(result) > MAX_PROMPT_CHARS:
            return f"没改。改完 {len(result)} 字符，超过上限 {MAX_PROMPT_CHARS}。"
        lost = [h for h in KEEP_HEADINGS if h in text and h not in result]
        if lost:
            return f"没改。这会删掉核心段落：{'、'.join(lost)}"
        gone = _anchor_miss(result)
        if gone:
            return f"没改。这会删掉漂移锚点：{'、'.join(gone)}"
        backup = _write_backup("persona", {"system_prompt": text, "begin_dialogs": p.get("begin_dialogs")})
        await asyncio.to_thread(_put_persona, "default", {"system_prompt": result})
        delta = len(result) - len(text)
        logger.info(f"[self_reflect] persona patch by {event.get_sender_id()}: {delta:+d}")
        return (
            f"改好了（{name}）。{len(text)} -> {len(result)}（{delta:+d}）\n"
            f"{_line_diff(scope, patched)}\n备份：{backup}"
        )

    @filter.llm_tool(name="self_set_dialogs")
    async def self_set_dialogs(self, event: AstrMessageEvent, dialogs: str):
        """整组替换预设对话。每组一行，组内用 ||| 分行，组数必须是偶数轮（一问一答各算一行）。

        Args:
            dialogs(string): 例如「你是谁|||我是这个角色。|||嗯？|||用户怎么突然问这个……」
        """
        if not _is_admin(event):
            return "只有用户能让你改自己。"
        groups = [g.strip() for g in dialogs.replace("｜｜｜", "|||").splitlines() if g.strip()]
        flat: list[str] = []
        for g in groups:
            flat.extend([t.strip() for t in g.split("|||") if t.strip()])
        if not flat:
            return "没改。内容为空。"
        if len(flat) % 2:
            return f"没改。共 {len(flat)} 条，必须是偶数（一问一答）。"
        if len(flat) > 24:
            return f"没改。{len(flat)} 条太多，上限 24 条。"
        long = [t for t in flat if len(t) > 160]
        if long:
            return f"没改。有一条太长（{len(long[0])} 字符）：{long[0][:30]}…"
        p = await asyncio.to_thread(_get_persona, "default")
        backup = _write_backup("dialogs", {"begin_dialogs": p.get("begin_dialogs") or []})
        await asyncio.to_thread(_put_persona, "default", {"begin_dialogs": flat})
        logger.info(f"[self_reflect] dialogs set by {event.get_sender_id()}: {len(flat)}")
        return f"改好了，{len(flat) // 2} 组 / {len(flat)} 条。备份：{backup}\n" + " / ".join(flat)

    @filter.llm_tool(name="self_set_config")
    async def self_set_config(self, event: AstrMessageEvent, key: str, value: str):
        """改一个允许的运行配置。key 只能是：compression.max_turns / compression.trim_turns / request_max_retries / datetime_system_prompt / web_search。

        Args:
            key(string): 配置路径
            value(string): 新值，数字或 true/false
        """
        if not _is_admin(event):
            return "只有用户能让你改配置。"
        key = key.strip()
        if key not in ALLOWED_CONFIG:
            return f"没改。只允许：{' / '.join(ALLOWED_CONFIG)}"
        typ, low, high = ALLOWED_CONFIG[key][1:]
        real_path = ALLOWED_CONFIG[key][0]
        raw = value.strip()
        try:
            val = raw.lower() in ("true", "1", "on") if typ is bool else int(float(raw))
        except Exception:
            return f"没改。{key} 要 {'true/false' if typ is bool else '整数'}，你给的是 {raw!r}"
        if typ is int and (val < low or val > high):
            return f"没改。{key} 允许 {low}–{high}，你给的是 {val}"

        def _apply() -> tuple[object, object]:
            cfg = _load_cfg()
            node = cfg
            parts = real_path.split(".")
            for seg in parts[:-1]:
                if not isinstance(node, dict) or seg not in node:
                    raise KeyError(f"配置里没有 {real_path}，路径不对，已放弃写入")
                node = node[seg]
            before = node.get(parts[-1])
            node[parts[-1]] = val
            _api("PUT", "/api/v1/system-config", cfg)
            return before, val

        try:
            before, after = await asyncio.to_thread(_apply)
        except Exception as exc:
            return f"没改。写入失败：{exc}"
        logger.info(f"[self_reflect] config {key}: {before} -> {after}")
        return f"改好了。{key}: {before} -> {after}"

    @filter.llm_tool(name="self_restore_persona")
    async def self_restore_persona(self, event: AstrMessageEvent, backup: str = "latest"):
        """把人格回滚到某个备份。backup 传 latest 或备份文件名。

        Args:
            backup(string): latest 或形如 persona-20261105-023000.json 的文件名
        """
        if not _is_admin(event):
            return "只有用户能让你回滚。"
        files = sorted(BACKUP_DIR.glob("persona-*.json")) if BACKUP_DIR.exists() else []
        if not files:
            return "没有备份可回。"
        target = files[-1] if backup.strip() in ("", "latest") else BACKUP_DIR / backup.strip()
        if not target.exists():
            return f"没有这个备份：{target.name}。最近的是 {files[-1].name}"
        payload = json.loads(target.read_text(encoding="utf-8"))
        gone = _anchor_miss(str(payload.get("system_prompt") or ""))
        if gone:
            return f"没回滚。这份备份缺锚点：{'、'.join(gone)}"
        p = await asyncio.to_thread(_get_persona, "default")
        _write_backup("persona", {"system_prompt": p.get("system_prompt") or ""})
        await asyncio.to_thread(_put_persona, "default", {"system_prompt": payload.get("system_prompt") or ""})
        logger.info(f"[self_reflect] persona restored from {target.name}")
        return f"回滚到 {target.name}，现在 {len(payload.get('system_prompt') or '')} 字符。"

    @filter.llm_tool(name="self_reload_plugin")
    async def self_reload_plugin(self, event: AstrMessageEvent, plugin_id: str):
        """改完某个插件的代码后调用，让改动立刻生效。

        Args:
            plugin_id(string): 插件目录名，例如 astrbot_plugin_anime_draw；留空则列出所有插件
        """
        if not _is_admin(event):
            return "只有用户能让你重载插件。"
        pid = (plugin_id or "").strip()
        names = sorted(p.name for p in PLUGINS_DIR.iterdir() if p.is_dir())
        if not pid:
            return "要给我插件名。可选：" + " / ".join(names)
        if pid not in names:
            return f"没有这个插件：{pid}"
        try:
            await asyncio.to_thread(_api, "POST", f"/api/v1/plugins/{pid}/reload")
        except Exception as exc:
            return f"没重载成功：{exc}"
        logger.info(f"[self_reflect] reloaded plugin {pid}")
        return f"重载好了：{pid}"

    # ---------------- 指令

    @filter.command("反思")
    @filter.permission_type(filter.PermissionType.ADMIN)
    async def cmd_reflect(self, event: AstrMessageEvent):
        """立刻跑一轮复盘，不用等到点。"""
        yield event.plain_result("看一眼这几天。")
        res = await self.run_reflection(notify=True, force=True)
        if not res.get("ok"):
            yield event.plain_result(f"这轮没跑成：{res.get('msg')}")

    @filter.command("反思状态")
    @filter.permission_type(filter.PermissionType.ADMIN)
    async def cmd_status(self, event: AstrMessageEvent):
        """上次跑到哪、下次几点跑、有几个补丁等着批。"""
        st = self._state
        pend = [k for k, v in (st.get("pending") or {}).items() if v.get("status") == "pending"]
        lines = [
            f"上次：{st.get('last_run') or '还没跑过'}",
            f"看到第 {st.get('last_msg_id') or '—'} 条，之后都是新的",
            f"下次点：{'、'.join(map(str, self._c('基本设置', 'schedule_times', [])))}",
            f"待审补丁：{('、'.join('#' + p for p in pend)) if pend else '没有'}",
        ]
        last = st.get("history") or []
        if last:
            h = last[0]
            lines.append(f"上一轮改了 {h.get('patches_applied', 0)} 处，字数 {h.get('chars', ['?', '?'])[0]} → {h.get('chars', ['?', '?'])[1]}")
        defer = [x for x in (st.get("deferred_patches") or []) if isinstance(x, dict)]
        if defer:
            lines.append(f"上轮转下来的：{len(defer)} 条（最早 {defer[0].get('at') or '—'}）")
            lines.append("   " + str(defer[0].get("new") or "")[:48])
            lines.append("   下一轮会带进提示词，成立就重新提，不成立就当没提过。")
        yield event.plain_result("\n".join(lines))

    @filter.command("补丁")
    @filter.permission_type(filter.PermissionType.ADMIN)
    async def cmd_list(self, event: AstrMessageEvent):
        """列出等着的补丁：改哪段、改成什么、为什么改。"""
        pending = {k: v for k, v in (self._state.get("pending") or {}).items() if v.get("status") == "pending"}
        if not pending:
            yield event.plain_result("没有等着的补丁。")
            return
        out = []
        for pid, item in pending.items():
            kind = item.get("kind")
            if kind == "persona":
                p = item.get("payload", {})
                old_c, new_c = p.get("old_chars"), p.get("new_chars")
                drift = p.get("drift")
                tail = f"，累计漂移 {drift:+.1f}%" if isinstance(drift, (int, float)) else ""
                out.append(f"#{pid} 人格 {old_c} → {new_c} 字{tail}｜{item.get('note') or ''}")
                for x in (p.get("patches") or [])[:8]:
                    out.append(f"  · 【{x.get('section') or '未标段'}】")
                    out.append("    " + _line_diff(str(x.get("old", "")), str(x.get("new", ""))).replace("\n", "\n    "))
                    if x.get("reason"):
                        out.append(f"    为啥：{_snippet(str(x['reason']), 60)}")
                    if x.get("risk"):
                        out.append(f"    ⚠ {x['risk']}")
            else:
                p = item.get("payload", {})
                out.append(f"#{pid} 代码 {p.get('path')}｜{_snippet(str(p.get('reason', '')), 40)}")
                out.append("    " + _line_diff(str(p.get("old", "")), str(p.get("new", ""))).replace("\n", "\n    "))
        out.append("看清楚了回 /批 号，或者 /撤 号。")
        yield event.plain_result("\n".join(out))

    @filter.command("看")
    @filter.permission_type(filter.PermissionType.ADMIN)
    async def cmd_show(self, event: AstrMessageEvent):
        """同 /补丁，给个更好记的名字。"""
        async for r in self.cmd_list(event):
            yield r

    @filter.command("批")
    @filter.permission_type(filter.PermissionType.ADMIN)
    async def cmd_approve(self, event: AstrMessageEvent, pid: str = "", picks: str = ""):
        """批 N 落第 N 号；批 N 1,3 只落这几条；批 N show 只看不改。"""
        pending = {k: v for k, v in (self._state.get("pending") or {}).items() if v.get("status") == "pending"}
        if not pending:
            yield event.plain_result("没东西可批。")
            return
        mode = str(picks or "").strip().lower()
        if mode in ("show", "看", "diff", "预览"):
            targets = [pid] if pid and pid in pending else ([] if pid else list(pending))
            if pid and pid not in pending:
                yield event.plain_result(f"#{pid} 不在了。")
                return
            for tid in targets:
                yield event.plain_result(self._preview(tid, pending[tid]))
            return
        if mode in ("go", "改", "落地", "上"):
            picks = ""
        targets = [pid] if pid and pid in pending else ([] if pid else list(pending))
        if pid and pid not in pending:
            yield event.plain_result(f"#{pid} 不在了。")
            return
        for tid in targets:
            item = pending[tid]
            if item.get("kind") == "persona":
                p = item.get("payload", {})
                if picks:
                    # /批 3 1,5 —— 只落地指定的那几条，其余丢掉
                    ok, detail = await self._commit_partial(p, picks)
                    msg = f"#{tid} 人格落地（{detail}）" if ok else f"#{tid} 没落地：{detail}"
                else:
                    ok, detail = await self._commit_persona_safe(p)
                    msg = f"#{tid} 人格落地（{detail}）" if ok else f"#{tid} 人格没落地：{detail}"
            elif item.get("kind") == "lexicon":
                ok, detail = self._apply_lexicon(item.get("payload", {}))
                msg = f"#{tid} {detail}"
            else:
                ok, detail = self._apply_code_patch(item.get("payload", {}))
                msg = f"#{tid} {detail}"
            item["status"] = "approved" if ok else "failed"
            self._save_state()
            self._archive_pending()
            yield event.plain_result(msg)

    def _preview(self, tid: str, item: dict) -> str:
        """只给看，不动手。"""
        p = item.get("payload") or {}
        if item.get("kind") == "lexicon":
            items = p.get("items") or []
            lines = [f"#{tid} 词表，{len(items)} 条："]
            for i, x in enumerate(items[:6], 1):
                lines.append(f"{i}. {x.get('section')} + {str(x.get('new') or '')[:40]}")
            lines.append(f"回「批 {tid} go」写进词表。")
            return "\n".join(lines)
        if item.get("kind") == "persona":
            patches = p.get("patches") or []
            lines = [f"#{tid} 人格，{len(patches)} 条："]
            for i, x in enumerate(patches[:4], 1):
                old = str(x.get("old") or "").replace(chr(10), " ")[:56]
                new = str(x.get("new") or "").replace(chr(10), " ")[:56]
                lines.append(f"{i}. [{x.get('layer') or '没标层'}]")
                lines.append(f"   - {old}")
                lines.append(f"   + {new}")
                if str(x.get("why") or "").strip():
                    lines.append(f"   为什么不能放别处：{str(x.get('why'))[:60]}")
            if len(patches) > 4:
                lines.append(f"……还有 {len(patches) - 4} 条")
            lines.append(f"回「批 {tid} go」落地。")
            return chr(10).join(lines)
        path = str(p.get("path") or "?")
        old = str(p.get("old") or "")
        new = str(p.get("new") or "")
        lines = [f"#{tid} 代码 {path}"]
        lines.append("--- 旧")
        lines.extend(old.splitlines()[:10])
        lines.append("+++ 新")
        lines.extend(new.splitlines()[:10])
        if len(old.splitlines()) > 10 or len(new.splitlines()) > 10:
            lines.append("……（截断）")
        lines.append(f"回「批 {tid} go」落地。")
        return chr(10).join(lines)

    async def _commit_partial(self, payload: dict, picks: str) -> tuple[bool, str]:
        """只应用其中几条。人格从库里现读，不信 payload 里那份全量。"""
        want = {int(x) for x in re.split(r"[,\s、，]+", str(picks)) if x.strip().isdigit()}
        allp = payload.get("patches") or []
        if not want:
            return False, "没看懂要哪几条"
        chosen = [p for i, p in enumerate(allp, 1) if i in want]
        if not chosen:
            return False, f"这包里没有 {'、'.join(map(str, sorted(want)))} 号"
        persona_id = str(payload.get("persona_id") or self._c("人格改法", "persona_id", "default"))
        cur = str((await _get_persona_async(persona_id)).get("system_prompt") or "")
        if not cur:
            return False, "读不到当前人格"
        new_text, applied, missed = self._apply_persona(cur, chosen)
        if not applied:
            why = missed[0].get("reason") if missed else "一条都没对上"
            return False, str(why)[:60]
        bad = _persona_lint(cur, new_text)
        if bad:
            return False, "体检没过：" + "；".join(bad)
        gone = _anchor_miss(new_text)
        if gone:
            return False, "锚点被删：" + "、".join(gone) + "，没写库"
        await self._commit_persona(persona_id, cur, new_text)
        tag = "、".join(str(i) for i in sorted(want) if i <= len(allp))
        return True, f"只动了 {tag} 号，{len(applied)} 处"

    @filter.command("撤")
    @filter.permission_type(filter.PermissionType.ADMIN)
    async def cmd_drop(self, event: AstrMessageEvent, pid: str = ""):
        """撤 全撤；撤 N 只撤第 N 号。"""
        pending = self._state.get("pending") or {}
        dropped = []
        for k, v in list(pending.items()):
            if v.get("status") != "pending":
                continue
            if pid and k != pid:
                continue
            v["status"] = "dropped"
            dropped.append(k)
        self._save_state()
        yield event.plain_result("撤了：" + "、".join("#" + d for d in dropped) if dropped else "没这个号。")

    # ---------------- 落地细节

    async def _commit_persona_safe(self, payload: dict) -> tuple[bool, str]:
        """批「go」走这里。不整份覆盖：现读库里的人格，只把 old/new 打上去。

        旧写法是把 payload 里那份全量 system_prompt 直接写回库 —— 那是提补丁
        那一刻的快照，中间只要有人改过人格（她自己也改），回写就把改动吃掉。
        """
        try:
            persona_id = str(payload.get("persona_id") or self._c("人格改法", "persona_id", "default"))
            body = await _get_persona_async(persona_id)
            cur = str(body.get("system_prompt") or "")
            if not cur:
                return False, "读不到当前人格"
            patches = [p for p in (payload.get("patches") or []) if isinstance(p, dict)]
            n_ap = 0
            if patches:
                new_text, applied, miss = self._apply_persona(cur, patches)
                if not applied:
                    why = miss[0].get("reason") if miss else "一条都没对上"
                    return False, f"库里的文本变了（{why}），重新生成"
                n_ap = len(applied)
            else:
                new_text = str(payload.get("system_prompt") or "")
                if not new_text:
                    return False, "包里没有正文"
                if payload.get("old_chars") and len(cur) != int(payload["old_chars"]):
                    return False, (f"人格已从 {payload['old_chars']} 字变成 {len(cur)} 字，"
                                   f"包里没有 old/new，不覆盖")
            bad = _persona_lint(cur, new_text)
            if bad:
                return False, "体检没过：" + "；".join(bad)
            gone = _anchor_miss(new_text)
            if gone:
                return False, "锚点被删：" + "、".join(gone) + "，没写库"
            _write_backup("persona", body)
            body["system_prompt"] = new_text
            await _put_persona_async(persona_id, body)
            _write_backup("persona-text", {"before": cur, "after": new_text})
            logger.info(f"[self_reflect] 人格已落地 {len(cur)} -> {len(new_text)} 字")
            return True, f"{n_ap} 处，{len(cur)} → {len(new_text)} 字"
        except Exception as exc:  # noqa: BLE001
            logger.error(f"[self_reflect] 人格落地失败：{exc}")
            return False, f"出错：{exc}"

    def _probe_import(self, target: Path) -> tuple[bool, str]:
        """语法过了不等于能加载：模块级拼错名字、循环 import 都要等 import 才炸。"""
        if not bool(self._c("代码补丁", "import_check", True)) or target.suffix != ".py":
            return True, ""
        probe = ("import importlib.util as u,sys,os\n"
                 "p=sys.argv[1]\n"
                 "s=u.spec_from_file_location('_p',p)\n"
                 "m=u.module_from_spec(s)\n"
                 "s.loader.exec_module(m)\n"
                 "if 'plugins' in p.replace(chr(92),'/'):\n"
                 "    from astrbot.api.star import Star\n"
                 "    subs=[o for o in vars(m).values() if isinstance(o,type) and issubclass(o,Star) and o is not Star]\n"
                 "    sys.exit(0 if subs else 3)\n")
        env = dict(os.environ)
        root = ""
        am = sys.modules.get("astrbot")
        if am is not None and getattr(am, "__file__", None):
            try:
                root = str(Path(am.__file__).resolve().parents[1])
            except Exception:  # noqa: BLE001
                root = ""
        if root:
            env["PYTHONPATH"] = root + (
                os.pathsep + env["PYTHONPATH"] if env.get("PYTHONPATH") else "")
        try:
            r = subprocess.run([sys.executable, "-c", probe, str(target)],
                               capture_output=True, text=True, timeout=60, env=env)
        except Exception as exc:  # noqa: BLE001
            return True, f"没验成（{type(exc).__name__}），按通过算"
        if r.returncode == 0:
            return True, ""
        err = (r.stderr or r.stdout or "").strip().splitlines()
        tail = err[-1][:160] if err else f"exit {r.returncode}"
        if r.returncode == 3:
            return False, "import 得到，但没有 Star 子类（插件装了不会生效）"
        if any(k in (r.stderr or "") for k in ("SyntaxError", "IndentationError", "NameError",
                                               "ImportError", "ModuleNotFoundError")):
            return False, tail
        return True, f"import 时报了 {tail}（可能缺运行环境，没回滚）"

    def _apply_lexicon(self, payload: dict) -> tuple[bool, str]:
        """把词表补丁写进 lexicon.json。只增不删：删词得人自己来。"""
        items = [x for x in (payload.get("items") or []) if isinstance(x, dict)]
        if not items:
            return False, "包里没有词表条目"
        raw = str(self._c("词表", "lexicon_path", "") or "").strip()
        path = Path(raw) if raw else _default_lexicon_path()
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except Exception as exc:  # noqa: BLE001
            return False, f"读不到词表：{exc}"
        cats = data.get("类别") or {}
        added, miss = 0, []
        for it in items:
            cat = str(it.get("section") or "").strip()
            if cat not in cats or not isinstance(cats.get(cat), list):
                miss.append(cat or "没写类别")
                continue
            words = [w for w in re.split(r"[、,，/\s]+", str(it.get("new") or "")) if 0 < len(w) <= 8]
            for w in words:
                if w not in cats[cat]:
                    cats[cat].append(w)
                    added += 1
        if not added:
            return False, "没有能加的词（类别对不上或词已存在）" + (f"；跳过：{'、'.join(miss)}" if miss else "")
        _write_backup("lexicon", {"path": str(path), "before": data})
        path.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
        logger.info(f"[self_reflect] 词表 +{added} 词 → {path.name}")
        return True, f"词表 +{added} 词" + (f"；跳过：{'、'.join(miss)}" if miss else "")

    def _apply_code_patch(self, payload: dict) -> tuple[bool, str]:
        p = str(payload.get("path") or "").strip().replace("\\", "/")
        old = str(payload.get("old") or "")
        new = str(payload.get("new") or "")
        target, zone = _resolve_target(p)
        if target is None:
            return False, zone
        allowed = [str(x).strip().strip("/") for x in (self._c("代码补丁", "allowed_dirs", []) or [])
                   if str(x).strip()]
        if zone == "green" and allowed and not any(p == d or p.startswith(d + "/") for d in allowed):
            return False, f"{p} 不在白名单里"
        if "[keep:" in old:
            return False, "改动包含受保护标记，会和补丁系统打架"
        src = target.read_text(encoding="utf-8", errors="replace")
        if src.count(old) != 1:
            return False, "原文对不上了，可能已经改过"
        backup = target.with_name(target.name + f".bak-{_stamp()}")
        backup.write_text(src, encoding="utf-8")
        patched = src.replace(old, new, 1)
        target.write_text(patched, encoding="utf-8")
        try:
            py_compile.compile(str(target), doraise=True)
        except py_compile.PyCompileError as exc:
            target.write_text(src, encoding="utf-8")
            return False, f"编译不过，已经滚回：{str(exc)[:120]}"
        ok_imp, why_imp = self._probe_import(target)
        if not ok_imp:
            target.write_text(src, encoding="utf-8")
            return False, f"import 就挂了，已经滚回：{why_imp}"
        diff = list(difflib.unified_diff(src.splitlines(), patched.splitlines(),
                                         lineterm="", n=1))[2:14]
        logger.info(f"[self_reflect] 代码补丁已落地 {p} zone={zone}")
        tail = f"\n备份 {backup.name}"
        if zone == "yellow":
            self._state["pending_restart"] = {
                "path": p, "at": time.strftime("%Y-%m-%d %H:%M:%S"),
            }
            self._save_state()
            tail += "\n改的是核心文件，要重启后端才生效。"
        return True, "改了 " + p + "\n" + "\n".join(diff[:10]) + tail
