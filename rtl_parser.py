# Pure-Python Verilog(.v) hierarchy analyzer & batch grouping JSON generator
# - No PyVerilog/iverilog dependency
# - Ascend to 'RTL' folder (case-insensitive) from a given path, collect .v files
# - Parse modules/ports/instances (Verilog-2005 지향, best-effort)
# - Find all instantiations of a target module; let user group them (all/ranges/indices)
# - Save per-group JSON with shared ports + selected Paths/Instances only
# - Console prints: formal Korean; logs: English

import logging
from pathlib import Path
import re
import json
from typing import List, Dict, Any, Optional, Tuple, Set

LOG = logging.getLogger("rtl_group_mode")

# ============================================================
# 분류 패턴 후보(자유롭게 추가/수정 가능, 대소문자 무시)
# ============================================================
CLOCK_PATTERNS = [
    r"^(i_)?clk$", r"^(i_)?sclk$", r"^(i_)?clock(\b|_)", r"^clk(_\w+)?$",
]
RESET_PATTERNS = [
    r"^(i_)?rst(n)?$", r"^(i_)?reset(n)?$", r"^.*_rst(n)?$",
]
PARAM_PATTERNS = [
    r"^p_[A-Za-z0-9_]+$", r"^P_[A-Za-z0-9_]+$",
]

def is_match_any(name: str, patterns: List[str]) -> bool:
    for p in patterns:
        if re.search(p, name, flags=re.IGNORECASE):
            return True
    return False

def classify_name(name: str) -> str:
    if is_match_any(name, CLOCK_PATTERNS):
        return "clock"
    if is_match_any(name, RESET_PATTERNS):
        return "reset"
    if is_match_any(name, PARAM_PATTERNS):
        return "parameter"
    return "other"

# -----------------------------
# File discovery and RTL root
# -----------------------------
def discover_files(root: Path, exts: List[str]) -> List[Path]:
    extset = set(e if e.startswith(".") else f".{e}" for e in exts)
    files = []
    for p in root.rglob("*"):
        if p.is_file() and p.suffix.lower() in extset:
            files.append(p)
    return files

def find_rtl_root_from(start: Path) -> Tuple[Path, bool]:
    cur = start if start.is_dir() else start.parent
    orig = cur
    while True:
        if cur.name.lower() == "rtl":
            return cur.resolve(), True
        if cur.parent == cur:
            break
        cur = cur.parent
    return (orig.resolve(), False)

# -----------------------------
# Preprocess: strip comments & attributes
# -----------------------------
_re_line_comment = re.compile(r"//.*?$", re.MULTILINE)
_re_block_comment = re.compile(r"/\*.*?\*/", re.DOTALL)
_re_attr = re.compile(r"\(\*.*?\*\)", re.DOTALL)

def preprocess(text: str) -> str:
    text = _re_block_comment.sub("", text)
    text = _re_line_comment.sub("", text)
    text = _re_attr.sub("", text)
    text = text.replace("\r\n", "\n").replace("\r", "\n")
    return text

# -----------------------------
# Helpers
# -----------------------------
def skip_spaces(text: str, i: int) -> int:
    n = len(text)
    while i < n and text[i].isspace():
        i += 1
    return i

def extract_balanced(text: str, start: int, open_ch: str, close_ch: str) -> Tuple[str, int]:
    assert text[start] == open_ch
    depth = 0
    i = start
    n = len(text)
    buf = []
    while i < n:
        ch = text[i]
        if ch == open_ch:
            depth += 1
            if depth > 1:
                buf.append(ch)
        elif ch == close_ch:
            depth -= 1
            if depth == 0:
                return ("".join(buf), i + 1)
            else:
                buf.append(ch)
        else:
            buf.append(ch)
        i += 1
    raise ValueError("Unbalanced parentheses while parsing")

# -----------------------------
# Module/Port/Instance parsing
# -----------------------------
_module_decl_re = re.compile(r"\bmodule\s+([A-Za-z_]\w*)", re.MULTILINE)
_endmodule_re = re.compile(r"\bendmodule\b", re.MULTILINE)
_dir_kw = ("input", "output", "inout")
_ws_collapse = re.compile(r"\s+")

def collapse_ws(s: str) -> str:
    return _ws_collapse.sub(" ", s).strip()

def parse_widths(part: str) -> str:
    widths = re.findall(r"\[[^\]]+\]", part)
    return "".join(widths) if widths else ""

def split_top_level_commas(s: str) -> List[str]:
    out, buf = [], []
    depth = {"()": 0, "[]": 0, "{}": 0}
    for ch in s:
        if ch == "(":
            depth["()"] += 1
        elif ch == ")":
            depth["()"] -= 1
        elif ch == "[":
            depth["[]"] += 1
        elif ch == "]":
            depth["[]"] -= 1
        elif ch == "{":
            depth["{}"] += 1
        elif ch == "}":
            depth["{}"] -= 1
        if ch == "," and all(v == 0 for v in depth.values()):
            out.append("".join(buf)); buf = []
        else:
            buf.append(ch)
    if buf: out.append("".join(buf))
    return out

def extract_modules_from_text(text: str) -> List[Dict[str, Any]]:
    mods = []
    pos = 0
    n = len(text)
    while True:
        m = _module_decl_re.search(text, pos)
        if not m:
            break
        name = m.group(1)
        i = m.end()
        i = skip_spaces(text, i)
        param_ports = ""
        if i < n and text[i] == "#":
            i += 1
            i = skip_spaces(text, i)
            if i < n and text[i] == "(":
                content, j = extract_balanced(text, i, "(", ")")
                param_ports = content
                i = j
                i = skip_spaces(text, i)
        if i >= n or text[i] != "(":
            LOG.warning("Malformed module header (missing port list): %s", name)
            pos = i
            continue
        ports_header, j = extract_balanced(text, i, "(", ")")
        i = j
        i = skip_spaces(text, i)
        if i < n and text[i] == ";":
            i += 1
        else:
            LOG.warning("Expected ';' after module port list: %s", name)
        endm = _endmodule_re.search(text, i)
        if not endm:
            LOG.warning("endmodule not found for module: %s", name)
            body = text[i:]
            pos = n
        else:
            body = text[i:endm.start()]
            pos = endm.end()
        mods.append({"name": name, "param_ports": param_ports, "ports_header": ports_header, "body": body})
    return mods

def parse_ports_header(ports_header: str) -> List[Dict[str, str]]:
    entries = split_top_level_commas(ports_header)
    ports = []
    for e in entries:
        e = collapse_ws(e)
        if not e or e == "...":
            continue
        dir_ = "unknown"
        width = ""
        name = None
        for dk in _dir_kw:
            if re.search(rf"\b{dk}\b", e):
                dir_ = dk
                break
        w = parse_widths(e)
        if w: width = w
        ids = re.findall(r"[A-Za-z_]\w*", e)
        if ids:
            name = ids[-1]
        if name:
            ports.append({"name": name, "dir": dir_, "width": width})
    return ports

def parse_body_io_decls(body: str) -> Dict[str, Dict[str, str]]:
    decls = {}
    pattern = re.compile(r"\b(input|output|inout)\b([^;]*);", re.IGNORECASE | re.MULTILINE | re.DOTALL)
    for m in pattern.finditer(body):
        dir_ = m.group(1).lower()
        rest = m.group(2)
        width = parse_widths(rest)
        tmp = re.sub(r"\[[^\]]+\]", " ", rest)
        tmp = re.sub(r"\b(wire|reg|logic|signed|unsigned|var|tri|supply0|supply1)\b", " ", tmp)
        names = [t for t in re.findall(r"[A-Za-z_]\w*", tmp) if t not in _dir_kw]
        for nm in names:
            decls[nm] = {"dir": dir_, "width": width}
    return decls

_reserved = {
    "if","else","for","while","case","endcase","begin","end",
    "assign","always","posedge","negedge","edge","function","endfunction","task","endtask",
    "generate","endgenerate","module","endmodule","typedef","class","endclass","interface","endinterface",
    "package","endpackage","import","export","clocking","endclocking","randcase","priority","unique"
}

def build_known_types(raw_modules: List[Dict[str, Any]]) -> List[str]:
    return [m["name"] for m in raw_modules]

def extract_instances_strict(body: str, known_types: List[str], allow_unknown: bool=False) -> List[Dict[str, str]]:
    insts = []
    if known_types:
        types_alt = "|".join(re.escape(t) for t in sorted(set(known_types)))
        pat = re.compile(
            rf"(?<!\w)(?P<type>{types_alt})\s*"
            rf"(?:#\s*\((?:[^()]*|\([^()]*\))*\)\s*)?"
            rf"(?P<inst>[A-Za-z_]\w*)\s*\(",
            re.MULTILINE
        )
        it, n = 0, len(body)
        while True:
            m = pat.search(body, it)
            if not m: break
            t, i = m.group("type"), m.group("inst")
            lp = m.end() - 1
            try:
                _, j = extract_balanced(body, lp, "(", ")")
                k = skip_spaces(body, j)
                if k < n and body[k] == ";":
                    insts.append({"inst": i, "type": t})
                    it = k + 1
                else:
                    it = j
            except Exception:
                it = m.end()
    if allow_unknown:
        pat2 = re.compile(
            r"(?<!\w)(?P<type>[A-Za-z_]\w*)\s*"
            r"(?:#\s*\((?:[^()]*|\([^()]*\))*\)\s*)?"
            r"(?P<inst>[A-Za-z_]\w*)\s*\(",
            re.MULTILINE
        )
        it, n = 0, len(body)
        while True:
            m = pat2.search(body, it)
            if not m: break
            t, i = m.group("type"), m.group("inst")
            if t in _reserved:
                it = m.end(); continue
            prev = body[max(0, m.start()-6):m.start()]
            if re.search(r"[.\->]", prev):
                it = m.end(); continue
            lp = m.end() - 1
            try:
                _, j = extract_balanced(body, lp, "(", ")")
                k = skip_spaces(body, j)
                if k < n and body[k] == ";":
                    insts.append({"inst": i, "type": t})
                    it = k + 1
                else:
                    it = j
            except Exception:
                it = m.end()
    return insts

# -----------------------------
# Build modules DB (two-pass, keep file origin)
# -----------------------------
def build_modules_db(files: List[Path], allow_unknown: bool=False) -> Dict[str, Any]:
    LOG.info("Start building modules DB from %d files", len(files))
    # First pass: collect raw modules with file info
    raw_all = []
    texts_by_file = {}
    for p in files:
        try:
            t = preprocess(p.read_text(encoding="utf-8", errors="ignore"))
            texts_by_file[p] = t
            rms = extract_modules_from_text(t)
            for rm in rms:
                raw_all.append({**rm, "file": str(p)})
        except Exception as e:
            LOG.warning("Failed to read file: %s, err=%s", p, e)
    known_types = build_known_types(raw_all)

    modules: Dict[str, Any] = {}
    for rm in raw_all:
        header_ports = parse_ports_header(rm["ports_header"])
        body_decls = parse_body_io_decls(rm["body"])
        ports = merge_ports(header_ports, body_decls)
        instances = extract_instances_strict(rm["body"], known_types, allow_unknown=allow_unknown)
        name = rm["name"]
        if name in modules:
            LOG.warning("Duplicate module name found; overriding: %s (prev=%s, new=%s)", name, modules[name].get("file"), rm["file"])
        modules[name] = {
            "module": name,
            "file": rm["file"],
            "ports": ports,
            "instances": instances
        }
        LOG.debug("Module parsed: %s (ports=%d, instances=%d, file=%s)", name, len(ports), len(instances), rm["file"])
    LOG.info("Finished modules DB: %d modules", len(modules))
    return modules

# -----------------------------
# Hierarchy and occurrences
# -----------------------------
def find_top_modules(modules: Dict[str, Any]) -> List[str]:
    all_mods = set(modules.keys())
    inst_types = set()
    for m in modules.values():
        for c in m["instances"]:
            inst_types.add(c["type"])
    tops = sorted(list(all_mods - inst_types))
    return tops or sorted(list(all_mods))

def find_occurrences_of_target(modules: Dict[str, Any], target: str) -> List[Dict[str, str]]:
    tops = find_top_modules(modules)
    occs: List[Dict[str, str]] = []

    def dfs(mod_name: str, inst_chain: List[str], top_name: str):
        for child in modules[mod_name]["instances"]:
            inst = child["inst"]
            ctype = child["type"]
            new_chain = inst_chain + [inst]
            if ctype == target:
                path = f"{top_name}." + ".".join(new_chain) if new_chain else top_name
                occs.append({"top": top_name, "path": path, "instance": inst})
            if ctype in modules:
                dfs(ctype, new_chain, top_name)

    for t in tops:
        dfs(t, [], t)

    occs.sort(key=lambda x: (x["path"], x["instance"]))
    return occs

# -----------------------------
# Ports grouping and classification
# -----------------------------
def classify_groups(ports: List[Dict[str, str]]) -> Dict[str, List[Dict[str, str]]]:
    clocks, resets, params = [], [], []
    for p in ports:
        cls = classify_name(p["name"])
        item = {"name": p["name"], "width": p.get("width", "")}
        if cls == "clock":
            clocks.append(item)
        elif cls == "reset":
            resets.append(item)
        elif cls == "parameter":
            params.append(item)
    return {"clocks": clocks, "resets": resets, "parameters": params}

def ports_bundle_for_module(modules: Dict[str, Any], target: str) -> Dict[str, Any]:
    m = modules[target]
    inputs, outputs, inouts = [], [], []
    for p in m["ports"]:
        item = {"name": p["name"], "width": p.get("width", "")}
        if p["dir"] == "input":
            inputs.append(item)
        elif p["dir"] == "output":
            outputs.append(item)
        elif p["dir"] == "inout":
            inouts.append(item)
    cls = classify_groups(m["ports"])
    return {
        "inputs": inputs,
        "outputs": outputs,
        "inouts": inouts,
        "clocks": cls["clocks"],
        "resets": cls["resets"],
        "parameters": cls["parameters"]
    }

# -----------------------------
# Target selection helpers
# -----------------------------
def modules_defined_under(modules: Dict[str, Any], base: Path) -> List[str]:
    base = base.resolve()
    out = []
    for name, m in modules.items():
        try:
            f = Path(m["file"]).resolve()
            if f.is_relative_to(base):
                out.append(name)
        except Exception:
            # Python < 3.9 compatibility: manual check
            try:
                if str(f).startswith(str(base)):
                    out.append(name)
            except:
                pass
    return sorted(set(out))

def pick_target_module(start_path: Path, modules: Dict[str, Any]) -> Optional[str]:
    if start_path.is_file():
        base = start_path
        cand = [name for name, m in modules.items() if Path(m["file"]).resolve() == base.resolve()]
    else:
        base = start_path
        cand = modules_defined_under(modules, base)
    if not cand:
        # fallback: show all modules
        print("지정하신 경로에서 정의된 모듈을 찾지 못하였습니다. 전체 모듈 목록에서 선택하여 주십시오.")
        allmods = sorted(modules.keys())
        for i, n in enumerate(allmods):
            print(f"[{i}] {n}")
        while True:
            s = input("원하시는 번호를 입력하여 주십시오 > ").strip()
            if s.isdigit() and 0 <= int(s) < len(allmods):
                return allmods[int(s)]
            print("유효한 번호를 입력하여 주십시오.")
    else:
        print("검증 대상 모듈 후보는 다음과 같습니다.")
        for i, n in enumerate(cand):
            print(f"[{i}] {n}  (file={modules[n]['file']})")
        while True:
            s = input("검증 대상 모듈 번호를 입력하여 주십시오 > ").strip()
            if s.isdigit() and 0 <= int(s) < len(cand):
                return cand[int(s)]
            print("유효한 번호를 입력하여 주십시오.")

# -----------------------------
# Grouping selection
# -----------------------------
def parse_selection(line: str, available: Set[int]) -> List[int]:
    line = line.strip().lower()
    if not line:
        return []
    tokens = re.split(r"[,\s]+", line)
    picked: Set[int] = set()
    for tok in tokens:
        if not tok:
            continue
        if tok == "all":
            return sorted(list(available))
        m = re.match(r"^(\d+)-(\d+)$", tok)
        if m:
            a, b = int(m.group(1)), int(m.group(2))
            if a > b:
                a, b = b, a
            for i in range(a, b+1):
                if i in available:
                    picked.add(i)
            continue
        if tok.isdigit():
            i = int(tok)
            if i in available:
                picked.add(i)
            continue
        # ignore invalid tokens silently
    return sorted(picked)

def save_json(obj: Any, path: Path):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as f:
        json.dump(obj, f, ensure_ascii=False, indent=2)

def sanitize_filename(s: str) -> str:
    s = s.replace("`", "")
    s = re.sub(r"[^A-Za-z0-9_.\-]+", "_", s)
    s = re.sub(r"_+", "_", s)
    s = s.lstrip("._")
    return s or "group"

def run_grouping_flow(modules: Dict[str, Any], target: str, occs: List[Dict[str, str]]):
    # 1) Show occurrences
    if not occs:
        print("대상 모듈의 인스턴스를 찾지 못하였습니다.")
        return
    print("대상 모듈 인스턴스 목록은 다음과 같습니다.")
    for idx, o in enumerate(occs, start=1):
        print(f"[{idx}] {o['path']}  (inst={o['instance']})")

    # 2) Ask Top Path once (example)
    print("위의 하이어라키 경로 앞에 붙일 Top Path를 입력하여 주십시오. 예: top.dut")
    print("공란으로 두시면 입력하지 않은 것으로 처리합니다.")
    top_path_value = input("Top Path > ").strip()

    # 3) Ports bundle for target module
    bundle = ports_bundle_for_module(modules, target)

    # 4) Group loop
    available = set(range(1, len(occs)+1))
    group_idx = 1
    outdir = Path("out/groups").resolve()
    outdir.mkdir(parents=True, exist_ok=True)

    while available:
        print("\n선택 방법 안내: all | 1-4 | 1 2 3 4 | 1-3,5,7-9")
        line = input("묶어 적용할 인덱스를 입력하여 주십시오 (엔터 시 종료) > ").strip()
        picked = parse_selection(line, available)
        if not picked:
            print("선택을 종료합니다.")
            break

        # Build group JSON
        selected_paths = [occs[i-1]["path"] for i in picked]
        selected_instances = [occs[i-1]["instance"] for i in picked]
        obj = {
            "top_path": top_path_value,
            "module": target,
            # 공유 포트/분류는 유지
            "inputs": bundle["inputs"],
            "outputs": bundle["outputs"],
            "inouts": bundle["inouts"],
            "clocks": bundle["clocks"],
            "resets": bundle["resets"],
            "parameters": bundle["parameters"],
            # 이 묶음에만 해당하는 목록
            "paths": selected_paths,
            "instances": selected_instances,
            "count": len(selected_paths)
        }

        # Save
        fname = f"{sanitize_filename(target)}.group{group_idx:02d}.json"
        save_json(obj, outdir / fname)
        LOG.info("Saved group JSON: %s", outdir / fname)
        print(f"그룹 JSON이 저장되었습니다: {outdir/fname}")

        # Remove picked indices from available and continue
        for i in picked:
            if i in available:
                available.remove(i)
        group_idx += 1

        if available:
            print(f"남은 항목 수: {len(available)}개. 추가로 묶음을 생성하시겠습니까?")
        else:
            print("모든 항목을 처리하였습니다.")

# -----------------------------
# Main
# -----------------------------
def main():
    # Logging (English)
    logdir = Path("logs"); logdir.mkdir(parents=True, exist_ok=True)
    logfile = logdir / "rtl_nav.log"
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s [%(levelname)s] %(name)s: %(message)s",
        handlers=[logging.FileHandler(logfile, encoding="utf-8"), logging.StreamHandler()]
    )
    LOG.info("==== RTL Group Mode started ====")

    # 1) Ask a starting path (file or directory)
    user_path = input("시작 경로(파일 또는 디렉터리)를 입력하여 주십시오 (예: ./proj/sim/top_tb.sv 또는 ./proj/rtl) > ").strip()
    start_path = Path(user_path).resolve()
    if not start_path.exists():
        print("지정하신 경로를 찾을 수 없습니다. 경로를 다시 확인하여 주십시오.")
        LOG.error("Invalid start path: %s", start_path)
        return

    # 2) Ascend to 'RTL' directory if present
    rtl_root, found = find_rtl_root_from(start_path)
    if found:
        print(f"상위에서 RTL 디렉터리를 발견하였습니다. 다음 경로를 루트로 사용합니다: {rtl_root}")
        LOG.info("Detected RTL root at: %s", rtl_root)
    else:
        if start_path.is_dir():
            print(f"RTL 디렉터리를 찾지 못하였습니다. 입력하신 디렉터리를 루트로 사용합니다: {start_path}")
            rtl_root = start_path
        else:
            print(f"RTL 디렉터리를 찾지 못하였습니다. 입력하신 파일의 상위 디렉터리를 루트로 사용합니다: {start_path.parent}")
            rtl_root = start_path.parent

    # 3) Build modules DB
    files = discover_files(rtl_root, [".v"])
    if not files:
        print("RTL 디렉터리 하위에서 .v 파일을 찾지 못했습니다.")
        LOG.warning("No .v files under: %s", rtl_root)
        return

    try:
        modules = build_modules_db(files, allow_unknown=False)
    except Exception as e:
        LOG.exception("Parsing failed")
        print(f"파싱 중 오류가 발생하였습니다: {e}")
        print("자세한 내용은 logs/rtl_nav.log 파일을 확인하여 주십시오.")
        return

    if not modules:
        print("모듈을 하나도 찾지 못했습니다. 파일 구성을 확인하여 주십시오.")
        LOG.warning("No modules extracted")
        return

    # 4) Pick target module from the initially entered path
    target = pick_target_module(start_path, modules)
    if not target:
        print("검증 대상 모듈 선택이 완료되지 않았습니다.")
        return

    # 5) Find occurrences of the target module across hierarchy
    occs = find_occurrences_of_target(modules, target)
    run_grouping_flow(modules, target, occs)

    LOG.info("==== RTL Group Mode finished ====")

if __name__ == "__main__":
    main()