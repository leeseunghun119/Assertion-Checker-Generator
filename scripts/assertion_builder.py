#!/usr/bin/env python3
"""
Unified, modular assertion builder.

Features:
- RTL scan using scripts/rtl_parser.py internal APIs to extract ports for a target module.
- Define Excel population (reuses scripts/fill_define.py logic via JSON handoff).
- Extensible assertion plugins (see scripts/assertions/*) for each Excel sheet type.
- Configurable inputs via CLI or optional config file.

Quick start:
  python scripts/assertion_builder.py \
    --rtl-start EDA/RTL \
    --target-module blur_scaler \
    --excel Data/Assertion_TF.xlsx \
    --auto-define-fill \
    --out out/assertions

No-args interactive mode:
- Run without options to launch an interactive wizard that lets you pick
  RTL start path, target module, Excel file from Data/, plugins, and modes
  (Define fill, JSON output, SV generation).

Adding new assertion sheet:
- Create a plugin under scripts/assertions (see base.py and counter.py).
- Implement parse/generate_sv, register in registry.
- Run with --enable <plugin_name> or leave enabled by default.

Assistant prompt hint to extend:
- "Add a plugin 'sequence' for sheet 'sequence_gen' with headers ... that
    emits sequence ..." The AI should add scripts/assertions/sequence.py
    inheriting BaseAssertionPlugin and update registry.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple, Type

# Make local 'scripts' directory importable no matter the CWD
_THIS_DIR = Path(__file__).resolve().parent
if str(_THIS_DIR) not in sys.path:
    sys.path.insert(0, str(_THIS_DIR))

# Import RTL parsing helpers from scripts/rtl_parser.py (as a library)
from rtl_parser import (  # type: ignore
    discover_files,
    find_rtl_root_from,
    build_modules_db,
    find_top_modules,
    find_occurrences_of_target,
    compute_env_for_occurrence,
    resolve_ports_with_params,
    classify_groups,
)

from assertions import get_registered_plugins, BaseAssertionPlugin  # type: ignore


def build_module_context(rtl_start: Path, target_module: Optional[str]) -> Dict[str, Any]:
    exts = [".v", ".sv"]
    rtl_root, found = find_rtl_root_from(rtl_start)
    start_scope_dir = rtl_start if rtl_start.is_dir() else rtl_start.parent
    files = sorted(set(discover_files(rtl_root, exts)) | set(discover_files(start_scope_dir, exts)), key=lambda p: str(p))
    modules = build_modules_db(files, allow_unknown=False)
    if not modules:
        raise SystemExit("No modules parsed from RTL scope")

    if not target_module:
        tops = find_top_modules(modules)
        # Fallback: pick the first top as target
        target_module = tops[0] if tops else next(iter(modules.keys()))

    # Resolve first occurrence for environment
    occs = find_occurrences_of_target(modules, target_module)
    env = compute_env_for_occurrence(occs[0], modules, {}) if occs else {}
    ports_resolved = resolve_ports_with_params(modules, target_module, env)
    cls = classify_groups(modules[target_module]["ports"])
    # Exclude clock/reset names from inputs
    ex_names = {x["name"] for x in cls.get("clocks", [])} | {x["name"] for x in cls.get("resets", [])}
    inputs_filtered = [it for it in ports_resolved["inputs"] if it["name"] not in ex_names]

    module_info = {
        "module": target_module,
        "inputs": inputs_filtered,
        "outputs": ports_resolved["outputs"],
        "inouts": ports_resolved["inouts"],
        "clocks": cls.get("clocks", []),
        "resets": cls.get("resets", []),
        "parameters": cls.get("parameters", []),
    }
    return {"modules": modules, "module_info": module_info, "occs": occs}


def fill_define_excel_if_needed(excel_path: Path, module_info: Dict[str, Any], out_json_dir: Path):
    out_json_dir.mkdir(parents=True, exist_ok=True)
    define_json_path = out_json_dir / "module_define.json"
    define_json = {
        "top_path": "",
        "module": module_info["module"],
        "paths": [],
        "instances": [],
        "clocks": module_info["clocks"],
        "resets": module_info["resets"],
        "inputs": module_info["inputs"],
        "outputs": module_info["outputs"],
        "inouts": module_info["inouts"],
        "parameters": module_info["parameters"],
    }
    define_json_path.write_text(json.dumps(define_json, ensure_ascii=False, indent=2), encoding="utf-8")

    # Reuse the fill_define.py script via import and call its main logic? It is CLI-oriented.
    # For simplicity and to avoid tight coupling, invoke it as a subprocess-like call would be ideal,
    # but here we keep it as an external step. The caller can run:
    #   python scripts/fill_define.py <excel_path> <define_json_path>
    return define_json_path


def run_builder(
    rtl_start: Path,
    target_module: Optional[str],
    excel_path: Path,
    out_dir: Path,
    auto_define_fill: bool,
    enabled_plugins: Optional[List[str]],
    emit_json: bool,
) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)

    ctx = build_module_context(rtl_start, target_module)
    module_info = ctx["module_info"]

    # Optionally emit JSON for Define sheet population
    if auto_define_fill:
        define_json_path = fill_define_excel_if_needed(excel_path, module_info, out_dir)
        print(f"Define JSON written: {define_json_path}")
        # Auto-run fill_define.py to populate the Excel Define sheet
        fill_script = _THIS_DIR / "fill_define.py"
        if fill_script.exists():
            try:
                subprocess.run([sys.executable, str(fill_script), str(excel_path), str(define_json_path)], check=False)
            except Exception as e:
                print(f"[Warn] fill_define.py execution failed: {e}")
        else:
            print("[Info] scripts/fill_define.py not found; please run it manually.")

    # Load enabled plugins
    plugin_types: List[Type[BaseAssertionPlugin]] = get_registered_plugins()
    if enabled_plugins:
        enabled_names = set(enabled_plugins)
        plugin_types = [p for p in plugin_types if p.plugin_name in enabled_names]

    # Parse Excel sheets via plugins
    parsed_by_plugin: Dict[str, Dict[str, Any]] = {}
    for pcls in plugin_types:
        try:
            parsed_by_plugin[pcls.plugin_name] = pcls().parse(Path(excel_path))
        except Exception as e:
            print(f"[Warn] Plugin {pcls.plugin_name} parse failed: {e}")

    # Emit consolidated JSON (ports + per-plugin parsed structures)
    if emit_json:
        json_blob = {
            "module": module_info["module"],
            "clocks": module_info["clocks"],
            "resets": module_info["resets"],
            "inputs": module_info["inputs"],
            "outputs": module_info["outputs"],
            "inouts": module_info["inouts"],
            "parameters": module_info["parameters"],
            "sheets": parsed_by_plugin,
        }
        json_path = out_dir / "assertion_inputs.json"
        json_path.write_text(json.dumps(json_blob, ensure_ascii=False, indent=2), encoding="utf-8")
        print(f"Inputs JSON written: {json_path}")

    # Generate assertion SV sections via plugins
    sv_sections: List[str] = []
    common_context = {
        "module_info": module_info,
        "define_excel_path": str(excel_path),
        "output_dir": str(out_dir),
        "config": {
            "auto_define_fill": auto_define_fill,
            "enabled_plugins": enabled_plugins,
            "emit_json": emit_json,
        },
    }
    for pcls in plugin_types:
        parsed = parsed_by_plugin.get(pcls.plugin_name)
        if not parsed:
            continue
        try:
            sv_sections.extend(pcls().generate_sv(parsed, common_context))
        except Exception as e:
            print(f"[Warn] Plugin {pcls.plugin_name} generate failed: {e}")

    # Write unified checker SV
    if sv_sections:
        out_sv = out_dir / "auto_assertion_checker.sv"
        header = "/***** Auto-generated Assertion Checker *****/\n"
        out_sv.write_text(header + "\n\n".join(sv_sections), encoding="utf-8")
        print(f"SV written: {out_sv}")


def _prompt(msg: str, default: Optional[str] = None) -> str:
    hint = f" [{default}]" if default else ""
    s = input(f"{msg}{hint}: ").strip()
    return s or (default or "")


def _pick_one(title: str, options: List[Tuple[str, str]], allow_custom: bool = False) -> str:
    print(title)
    for i, (label, _) in enumerate(options, start=1):
        print(f"  [{i}] {label}")
    if allow_custom:
        print("  [0] Enter custom path")
    while True:
        s = input("Select > ").strip()
        if allow_custom and s == "0":
            return _prompt("Enter custom path")
        if s.isdigit():
            i = int(s)
            if 1 <= i <= len(options):
                return options[i-1][1]
        print("Invalid selection. Try again.")


def _pick_multi(title: str, options: List[str]) -> List[str]:
    print(title)
    for i, label in enumerate(options, start=1):
        print(f"  [{i}] {label}")
    print("Enter numbers separated by space/comma (or 'all').")
    while True:
        s = input("Select > ").strip().lower()
        if s in ("all", "a"):
            return list(options)
        toks = [t for t in s.replace(",", " ").split() if t.isdigit()]
        picks: List[str] = []
        for t in toks:
            i = int(t)
            if 1 <= i <= len(options):
                picks.append(options[i-1])
        if picks:
            return picks
        print("Invalid selection. Try again.")


def interactive_wizard():
    print("==== Assertion Builder Interactive Mode ====")
    repo_root = _THIS_DIR.parent

    # RTL start candidates
    candidates: List[Tuple[str, str]] = []
    eda_rtl = repo_root / "EDA" / "RTL"
    if eda_rtl.exists():
        candidates.append((f"{eda_rtl} (EDA/RTL)", str(eda_rtl.resolve())))
    # Scan for other 'RTL' dirs (limit to 10)
    found = []
    try:
        for p in repo_root.rglob("RTL"):
            if p.is_dir() and p != eda_rtl:
                found.append(p)
                if len(found) >= 10:
                    break
    except Exception:
        pass
    for p in found:
        candidates.append((str(p), str(p.resolve())))
    if not candidates:
        candidates.append((str(repo_root), str(repo_root.resolve())))
    rtl_start_str = _pick_one("Select RTL start directory", candidates, allow_custom=True)
    rtl_start = Path(rtl_start_str).resolve()

    # Build modules DB to offer module selection
    try:
        ctx = build_module_context(rtl_start, None)
        modules = ctx["modules"]
    except SystemExit as e:
        print(str(e))
        sys.exit(1)

    mod_names = sorted(list(modules.keys()))
    # Prefer tops at front
    tops = set(find_top_modules(modules))
    mod_names_sorted = sorted(mod_names, key=lambda m: (0 if m in tops else 1, m))
    target_module = _pick_one("Select target module", [(m, m) for m in mod_names_sorted])

    # Excel selection from Data/
    data_dir = repo_root / "Data"
    excel_opts: List[Tuple[str, str]] = []
    if data_dir.exists():
        for x in sorted(data_dir.glob("*.xlsx")):
            if x.name.startswith("~$"):
                continue
            excel_opts.append((x.name, str(x.resolve())))
    if not excel_opts:
        excel_path = Path(_prompt("Enter Excel file path"))
    else:
        excel_path_str = _pick_one("Select Excel file (Data/)", excel_opts, allow_custom=True)
        excel_path = Path(excel_path_str).resolve()

    # Output directory
    out_default = str((repo_root / "out" / "assertions").resolve())
    out_dir = Path(_prompt("Output directory", out_default)).resolve()

    # Modes selection
    mode_labels = ["Fill Define sheet", "Emit inputs JSON", "Generate SV"]
    picks = _pick_multi("Select modes", mode_labels)
    auto_define_fill = ("Fill Define sheet" in picks)
    emit_json = ("Emit inputs JSON" in picks)

    # Plugin selection
    plugin_types: List[Type[BaseAssertionPlugin]] = get_registered_plugins()
    plugin_names = [p.plugin_name for p in plugin_types]
    enabled = _pick_multi("Select plugins (or 'all')", plugin_names)

    return {
        "rtl_start": rtl_start,
        "target_module": target_module,
        "excel_path": excel_path,
        "out_dir": out_dir,
        "auto_define_fill": auto_define_fill,
        "enabled_plugins": enabled,
        "emit_json": emit_json,
    }


def main():
    # Interactive when no args
    if len(sys.argv) == 1:
        cfg = interactive_wizard()
        return run_builder(**cfg)

    parser = argparse.ArgumentParser(description="Modular Assertion Builder")
    parser.add_argument("--rtl-start", help="Start path (file or dir) to scan RTL")
    parser.add_argument("--target-module", help="Target module name (optional)")
    parser.add_argument("--excel", help="Reference Excel path containing sheets")
    parser.add_argument("--out", default="out/assertions", help="Output directory for generated files")
    parser.add_argument("--auto-define-fill", action="store_true", help="Produce Define JSON for fill_define.py and log path")
    parser.add_argument("--use-default-excel", action="store_true", help="Ignore --excel and use default Data/Assertion_TF.xlsx")
    parser.add_argument("--enable", action="append", help="Enable only listed plugins (name). Can repeat.")
    parser.add_argument("--json", action="store_true", help="Emit consolidated JSON of inputs/outputs/parameters")
    args = parser.parse_args()

    # Validate required when not interactive
    if not args.rtl_start:
        raise SystemExit("--rtl-start is required when not using interactive mode")
    # Excel path selection with optional default
    if args.use_default_excel:
        excel_path = Path("Data/Assertion_TF.xlsx").resolve()
    else:
        if not args.excel:
            raise SystemExit("--excel is required when not using interactive mode (or use --use-default-excel)")
        excel_path = Path(args.excel).resolve()

    run_builder(
        rtl_start=Path(args.rtl_start).resolve(),
        target_module=args.target_module,
        excel_path=excel_path,
        out_dir=Path(args.out).resolve(),
        auto_define_fill=bool(args.auto_define_fill),
        enabled_plugins=list(args.enable) if args.enable else None,
        emit_json=bool(args.json),
    )


if __name__ == "__main__":
    main()


