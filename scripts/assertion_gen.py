"""
How to run
----------
Generate ALL: 
python assertion_gen.py -i assertion_tf2.xlsx

Generate Counter SV file: 
python assertion_gen.py -i assertion_tf2.xlsx -c

Generate Sequence SV file: 
python assertion_gen.py -i assertion_tf2.xlsx -s

Generate Property SV file: 
python assertion_gen.py -i assertion_tf2.xlsx -p

Generate JSON file: 
python assertion_gen.py -i assertion_tf2.xlsx -j

"""

import argparse
from pathlib import Path
import pandas as pd
import json
from collections import defaultdict, OrderedDict

COUNTER_SHEET = "counter_gen"
SEQUENCE_SHEET = "sequence_gen"
PROPERTY_SHEET = "property_gen"

def _apply_syntax(syntax: str, signal: str) -> str:
    syn = (syntax or "").strip()
    sig = (signal or "").strip()
    if syn and not sig:
        print(f"[Warning] missing 'Antecedent' for 'Antecedent Syntax'")
    elif syn == "Data":
        return sig
    elif syn and sig:
        return f"{syn}({sig})"
    return sig


def _duration_suffix(minv, maxv) -> str:
    min_s = str(minv).strip() if minv != "" else ""
    max_s = str(maxv).strip() if maxv != "" else ""
    if (min_s == "" and max_s == ""):
        return ""
    elif min_s != "" and (max_s == "" or min_s == max_s):
        return f"[*{min_s}]"
    elif (min_s == "" and max_s != ""):
        return f"[*0:{max_s}]"
    elif min_s != "" and max_s != "":
        return f"[*{min_s}:{max_s}]"
    return ""


def write_sv_file(file_path: Path, sections: list, header: str):
    content = [f"/***** {header} *****/"]
    content.extend(sections)
    file_path.write_text("\n\n".join(content), encoding="utf-8")
    print(f"  Path to SV file : {file_path}")


def generate_counters_sv(xls_data: dict):
    CG = xls_data.get(COUNTER_SHEET, {})
    cg1 = CG.get(CG.get("cnt_left_header")) or []
    cg2 = CG.get(CG.get("cnt_right_header")) or []
    cg1_header_name = CG.get("left_header") or []
    cg2_header_name = CG.get("right_header") or []

    cnt_base = OrderedDict()
    for row in cg1:
        cname = (row.get(cg1_header_name[0]) or "")
        if cname and cname not in cnt_base:
            cnt_base[cname] = row
    cnt_conds = defaultdict(list)
    for row in cg2:
        cname = (row.get(cg2_header_name[0]) or "")
        if cname:
            cnt_conds[cname].append(row)
    cnt_sections = []
    for name, base in cnt_base.items():
        clk_edge = (base.get(cg1_header_name[1]) or "")
        if not clk_edge: print(f"[Warning] Counter {name}: missing 'Edge Types'")
        clk = (base.get(cg1_header_name[2]) or "")
        if not clk: print(f"[Warning] Counter {name}: missing 'Base Clock'")
        
        rst_edge = (base.get(cg1_header_name[3]) or "")
        rst = (base.get(cg1_header_name[4]) or "")
        has_reset = bool(rst_edge and rst)
        sens = f"{clk_edge} {clk}" if not has_reset else f"{clk_edge} {clk} or {rst_edge} {rst}"
        
        cnt_lines = [f"always @({sens}) begin"]
        conds = cnt_conds.get(name, [])
        for i, c in enumerate(conds):
            st = (c.get(cg2_header_name[1]) or "").lower()
            cond = (c.get(cg2_header_name[2]) or "")
            cons = (c.get(cg2_header_name[3]) or "")
            if i == 0 or st == "if":
                cond_expr = cond if cond else "1'b0"
                cnt_lines.append(f"    if ({cond_expr}) begin")
                if cons: cnt_lines.append(f"        {cons};")
                cnt_lines.append("    end")
            elif st == "else if":
                cond_expr = cond if cond else "1'b0"
                cnt_lines.append(f"    else if ({cond_expr}) begin")
                if cons: cnt_lines.append(f"        {cons};")
                cnt_lines.append("    end")
            else:
                cnt_lines.append("    else begin")
                if cons: cnt_lines.append(f"        {cons};")
                cnt_lines.append("    end")
        cnt_lines.append("end")
        cnt_sections.append(f"// ---- {name} ----\n" + "\n".join(cnt_lines))

    return cnt_sections


def generate_sequences_sv(xls_data: dict):
    SG = xls_data.get(SEQUENCE_SHEET, {})
    sg1 = SG.get(SG.get("seq_all_header")) or []
    sg1_header_name = SG.get("all_header") or []
    
    seq_sections = []
    for row in sg1:
        sname = (row.get(sg1_header_name[0]) or "")
        if not sname:
            continue
        sinput = (row.get(sg1_header_name[1]) or "")
        sinput_part = f"({sinput})" if sinput != "" else ""
        clk_edge = (row.get(sg1_header_name[2]) or "")
        if not clk_edge: print(f"[Warning] Sequence {sname}: missing 'Edge Types'")
        clk = (row.get(sg1_header_name[3]) or "")
        if not clk: print(f"[Warning] Sequence {sname}: missing 'Base Clock'")
        ant = _apply_syntax(row.get(sg1_header_name[4],""), row.get(sg1_header_name[5],""))
        delay = str(row.get(sg1_header_name[6],""))
        delay_part = f" ##{delay}" if delay != "" else ""
        cons = _apply_syntax(row.get(sg1_header_name[7],""), row.get(sg1_header_name[8],""))
        dur = _duration_suffix(row.get(sg1_header_name[9],""), row.get(sg1_header_name[10],""))
        body = f"{ant}\n   {delay_part} {cons} {dur}"
        clk_event = f"@({clk_edge} {clk})" if clk else ""

        seq_lines = [f"sequence {sname}{sinput_part}; {clk_event}"]
        seq_lines.append(f"    {body};")
        seq_lines.append("endsequence")
        seq_sections.append(f"// ---- {sname} ----\n" + "\n".join(seq_lines))

    return seq_sections


def generate_properties_sv(xls_data: dict):
    PG = xls_data.get(PROPERTY_SHEET, {})
    pg1 = PG.get(PG.get("prop_left_header")) or []
    pg2 = PG.get(PG.get("prop_right_header")) or []
    pg1_header_name = PG.get("left_header") or []
    pg2_header_name = PG.get("right_header") or []
    
    prop_base = OrderedDict()
    for row in pg1:
        pname = (row.get(pg1_header_name[0]) or "")
        if pname and pname not in prop_base:
            prop_base[pname] = row
    prop_cons = defaultdict(list)
    for row in pg2:
        pname = (row.get(pg2_header_name[0]) or "")
        if pname:
            prop_cons[pname].append(row)
    prop_sections = []
    for name, base in prop_base.items():
        consequences = prop_cons.get(name, [])
        clk_edge = (base.get(pg1_header_name[1]) or "")
        if not clk_edge: print(f"[Warning] Property {name}: missing 'Edge Types'")
        clk = (base.get(pg1_header_name[2]) or "")
        if not clk: print(f"[Warning] Property {name}: missing 'Base Clock'")
        dis = (base.get(pg1_header_name[3]) or "")
        ant = _apply_syntax(base.get(pg1_header_name[4]), base.get(pg1_header_name[5]))
        imp = (base.get(pg1_header_name[6]) or "")
        
        clk_event = f"@({clk_edge} {clk})" if clk else ""
        dis_part = f" disable iff ({dis})" if dis else ""
        prop_lines = [f"property {name}; {clk_event}{dis_part}\n    {ant} {imp}"]
        pcons = prop_cons.get(name, [])
        for i, c in enumerate(pcons):
                delay = str(c.get(pg2_header_name[1],""))
                cons = _apply_syntax(c.get(pg2_header_name[2],""), c.get(pg2_header_name[3],""))
                dur = _duration_suffix(c.get(pg2_header_name[4],""), c.get(pg2_header_name[5],""))
                delay_part = f" ##{delay}" if delay != "" else ""
                body = f"{delay_part} {cons} {dur}"
                prop_lines.append(f"    {body}")
        prop_lines.append("endproperty\n")
        prop_lines.append(f"act_{name}: assert property({name})")
        prop_lines.append(f'    else $error(\"{name} failed at time %0t\", $time);')
        prop_sections.append(f"// ---- {name} ----\n" + "\n".join(prop_lines))

    return prop_sections


def keep_non_empty_rows(df):
    """Return only rows that have at least one non-empty cell.
    Empty cells are filled with "" (empty string)."""
    # ignore warning messege (df.fillna)
    #pd.set_option('future.no_silent_downcasting', True)
    
    df = df.fillna("").infer_objects(copy=False)
    keep = []
    for i in range(len(df)):
        row = df.iloc[i]
        has_value = False
        for value in row:
            if str(value).strip() != "":
                has_value = True
                break
        if has_value:
            keep.append(True)
        else:
            keep.append(False)
    df = df.loc[keep].reset_index(drop=True)
    # strip string values in all columns
    for col in df.columns:
        df[col] = df[col].apply(lambda x: str(x).strip() if isinstance(x, str) else x)
    return df


def parse_counter_gen(xls_path, sheet_name):
    raw = pd.read_excel(xls_path, sheet_name=sheet_name, header=None)
    cnt_left_header = raw.iloc[0, 0]
    cnt_right_header = raw.iloc[0, 5]

    # Left table: first 5 columns
    left_header = raw.iloc[1, 0:5].tolist()
    left = raw.iloc[2:, 0:5].copy()
    left.columns = left_header
    left = keep_non_empty_rows(left)

    # Right table: next 4 columns
    right_header = raw.iloc[1, 5:9].tolist()
    right = raw.iloc[2:, 5:9].copy()
    right.columns = right_header
    right = keep_non_empty_rows(right)

    return {
        "cnt_left_header": cnt_left_header,
        "cnt_right_header": cnt_right_header,
        "left_header": left_header,
        "right_header": right_header,
        cnt_left_header: left.to_dict(orient="records"),
        cnt_right_header: right.to_dict(orient="records")
    }


def parse_sequence_gen(xls_path, sheet_name):
    raw = pd.read_excel(xls_path, sheet_name=sheet_name, header=None)
    seq_all_header = raw.iloc[0, 0]

    all_header = raw.iloc[1, 0:11].tolist()
    all = raw.iloc[2:, 0:11].copy()
    all.columns = all_header
    all = keep_non_empty_rows(all)
    
    return {
        "seq_all_header": seq_all_header,
        "all_header": all_header,
        seq_all_header: all.to_dict(orient="records")
    }


def parse_property_gen(xls_path, sheet_name):
    raw = pd.read_excel(xls_path, sheet_name=sheet_name, header=None)
    prop_left_header = raw.iloc[0, 0]
    prop_right_header = raw.iloc[0, 7]

    # Left side table: 7 columns
    left_header = raw.iloc[1, 0:7].tolist()
    left = raw.iloc[2:, 0:7].copy()
    left.columns = left_header
    left = keep_non_empty_rows(left)

    # Right side table: next 6 columns
    right_header = raw.iloc[1, 7:13].tolist()
    right = raw.iloc[2:, 7:13].copy()
    right.columns = right_header
    right = keep_non_empty_rows(right)

    return {
        "prop_left_header": prop_left_header,
        "prop_right_header": prop_right_header,
        "left_header": left_header,
        "right_header": right_header,
        prop_left_header: left.to_dict(orient="records"),
        prop_right_header: right.to_dict(orient="records")
    }


def main():
    parser = argparse.ArgumentParser(description="Assertion Python Script Make Argument")
    parser.add_argument("-i", "--input", required=True, help="Path to Excel file (e.g., assertion_tf2.xlsx)")
    parser.add_argument("-c", "--counter", action="store_true", help="Generate counter SV file")
    parser.add_argument("-s", "--sequence", action="store_true", help="Generate sequence SV file")
    parser.add_argument("-p", "--property", action="store_true", help="Generate property SV file")
    parser.add_argument("-j", "--json", action="store_true", help="Generate JSON file")
    args = parser.parse_args()

    script_dir = Path(__file__).resolve().parent
    out_root = script_dir/"result_files"
    out_root.mkdir(parents=True, exist_ok=True)
    
    print("Reading and parsing sheets...")
    xls_path = Path(args.input).resolve()
    if not xls_path.exists():
        print(f"[Error] Input file not found: {xls_path}")
        raise SystemExit(1)
    print(f"  Path to Excel file : {xls_path}")
    xls_data = {}
    if not (args.property or args.sequence or args.counter):
        xls_data[COUNTER_SHEET] = parse_counter_gen(xls_path, COUNTER_SHEET)
        xls_data[SEQUENCE_SHEET] = parse_sequence_gen(xls_path, SEQUENCE_SHEET)
        xls_data[PROPERTY_SHEET] = parse_property_gen(xls_path, PROPERTY_SHEET)
    else:
        if args.counter:
            xls_data[COUNTER_SHEET] = parse_counter_gen(xls_path, COUNTER_SHEET)
        if args.sequence:
            xls_data[SEQUENCE_SHEET] = parse_sequence_gen(xls_path, SEQUENCE_SHEET)
        if args.property:
            xls_data[PROPERTY_SHEET] = parse_property_gen(xls_path, PROPERTY_SHEET)

    if args.json:
        print("Writing JSON file...")
        json_path = out_root/"xls_data.json"
        print(f"  Path to output JSON : {json_path}")
        json_path.write_text(json.dumps(xls_data, ensure_ascii=False, indent=2), encoding="utf-8")
    
    print("Writing SV file...")
    all_sections = []
    if not (args.property or args.sequence or args.counter):
        all_sections += generate_counters_sv(xls_data)
        all_sections += generate_sequences_sv(xls_data)
        all_sections += generate_properties_sv(xls_data)
        assertion_file = out_root/"auto_assertion.sv"
        write_sv_file(assertion_file, all_sections, "Auto-generated Assertions")
    else:
        if args.counter:
            cnt_sections = generate_counters_sv(xls_data)
            write_sv_file(out_root/"auto_counter.sv", cnt_sections, "Auto-generated Counters")
        if args.sequence:
            seq_sections = generate_sequences_sv(xls_data)
            write_sv_file(out_root/"auto_sequence.sv", seq_sections, "Auto-generated Sequences")
        if args.property:
            prop_sections = generate_properties_sv(xls_data)
            write_sv_file(out_root/"auto_property.sv", prop_sections, "Auto-generated Properties")


if __name__ == "__main__":
    main()
