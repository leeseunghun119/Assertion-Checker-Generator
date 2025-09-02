import sys
import pandas as pd
import re


def parse_range_expression(text):
    if not text:
        return []
    ranges = []
    range_pattern = r'\[(\d+):(\d+)\]'
    matches = re.finditer(range_pattern, text)
    for match in matches:
        start_num = int(match.group(1))
        end_num = int(match.group(2))
        indices = list(range(start_num, end_num + 1)) if start_num <= end_num else list(range(start_num, end_num - 1, -1))
        ranges.append((match.group(0), indices))
    return ranges

def expand_checker_for_ranges(block):
    checker_name = block["name"]
    checker_path = block["checker_path"]
    name_ranges = parse_range_expression(checker_name)
    path_ranges = parse_range_expression(checker_path)
    
    if not name_ranges and not path_ranges:
        return [block]
    
    primary_ranges = name_ranges if name_ranges else path_ranges
    expanded_blocks = []
    
    for range_pattern, indices in primary_ranges:
        width = len(str(max(indices)))
        for index in indices:
            if name_ranges:
                new_name = checker_name.replace(range_pattern, f"_{index:0{width}d}")
            else:
                new_name = f"{checker_name}_{index:0{width}d}"
            
            new_path = checker_path
            for pattern, _ in name_ranges:
                new_path = new_path.replace(pattern, f"[{index}]")
            for pattern, _ in path_ranges:
                new_path = new_path.replace(pattern, f"[{index}]")
            
            new_block = {
                "name": new_name,
                "checker_path": new_path,
                "events": block["events"].copy()
            }
            expanded_blocks.append(new_block)
    
    return expanded_blocks

def parse_excel(file_path, debug=False):
    df = pd.read_excel(file_path, header=None, engine='openpyxl')
    blocks = []
    current_block = None
    skip_next_row = False

    for index, row in df.iterrows():
        row_values = row.tolist()
        if str(row[1]).strip() == "Checker Name":
            if current_block:
                blocks.append(current_block)
            checker_name = str(row[2]).strip() if pd.notna(row[2]) else "Unnamed_Checker"
            checker_path = str(row[5]).strip() if pd.notna(row[5]) else "default_path"
            current_block = {
                "name": checker_name,
                "checker_path": checker_path,
                "events": []
            }
            skip_next_row = True
        elif skip_next_row:
            skip_next_row = False
            if debug:
                print(f"[INFO] Skipping header row after 'Checker Name' at line {index}: {row_values}")
            continue
        elif str(row[1]).strip() in ["Waiver Type", "Event Trigger Name"]:
            if debug:
                print(f"[WARNING] Skipping header row at line {index}: {row_values}")
            continue
        elif current_block and pd.notna(row[1]) and str(row[1]).strip() not in ["Checker Name"]:
            event_type = str(row[1]).strip()
            event_name = str(row[2]).strip() if pd.notna(row[2]) else None
            repeat_count = str(row[3]).strip() if pd.notna(row[3]) else None
            trigger_type = str(row[4]).strip() if pd.notna(row[4]) else None
            event_path = str(row[5]).strip() if pd.notna(row[5]) else None
            waive_target = str(row[6]).strip() if pd.notna(row[6]) else None
            note = str(row[7]).strip() if pd.notna(row[7]) else None
            if event_name and trigger_type and event_path:
                current_block["events"].append({
                    "type": event_type,
                    "name": event_name,
                    "trigger_type": trigger_type,
                    "repeat_count": repeat_count,
                    "path": event_path,
                    "waive_target": waive_target,
                    "note": note
                })

    if current_block:
        blocks.append(current_block)

    expanded_blocks = []
    for block in blocks:
        expanded_blocks.extend(expand_checker_for_ranges(block))

    if debug:
        print("[DEBUG]:")
        for i, block in enumerate(expanded_blocks, 1):
            print(f"\nBlock {i}: {block['name']}")
            print(f"  - Checker Path: {block['checker_path']}")
            for j, event in enumerate(block['events'], 1):
                print(f"    Event {j}:")
                print(f"      Type         : {event['type']}")
                print(f"      Name         : {event['name']}")
                print(f"      Trigger Type : {event['trigger_type']}")
                print(f"      Repeat Count : {event['repeat_count']}")
                print(f"      Path         : {event['path']}")
                print(f"      Waive Target : {event['waive_target']}")
                print(f"      Note         : {event['note']}")

    return expanded_blocks


def generate_sv_code(blocks):
    sv_code = """
`ifndef ASSERTION_WAIVER_INLINE
`define ASSERTION_WAIVER_INLINE

// ====================================================================
// ASSERTION WAIVER SYSTEM - INLINE VERSION (NO MACROS)
// Direct $asserton/$assertoff/$assertkill calls for maximum compatibility
// ====================================================================

// Individual Checker Instantiation Macro (Only macro needed)
`define INSTANTIATE_CHECKER_INLINE(CHECKER_NAME, CHECKER_ID) \\
    logic checker_``CHECKER_NAME``_en; \\
    initial begin \\
        checker_``CHECKER_NAME``_en = global_assert_en && !$test$plusargs($sformatf("AW_%0d", CHECKER_ID)); \\
        $display($time, " [AW_GLOBAL] Checker %s (ID:%0d) enabled: %0d", `"CHECKER_NAME`", CHECKER_ID, checker_``CHECKER_NAME``_en); \\
    end \\
    aw_signals_``CHECKER_NAME``_checker_intf aw_``CHECKER_NAME``(.global_assert_en(checker_``CHECKER_NAME``_en));

// ====================================================================
// INDIVIDUAL CHECKER INTERFACES - Inline Version (No Macros)
// ====================================================================

"""

    # Generate individual interfaces with inline code
    checker_id = 1
    for block_idx, block in enumerate(blocks):
        name = block["name"]
        checker_path = block["checker_path"]
        prefix = f"AW_{name.upper()}"
        
        sv_code += f"// {name} Checker Interface (ID: {checker_id}) - Inline Version\n"
        sv_code += f"interface aw_signals_{name}_checker_intf(input logic global_assert_en);\n"
        sv_code += f"    localparam string waiver_prefix = \"{prefix}\";\n"
        sv_code += f"    localparam string base_checker_path = \"{checker_path}\";\n\n"
        
        # Add wire declarations for all signals
        unique_signals = {}
        for event in block["events"]:
            signal_name = event["name"]
            signal_path = event["path"]
            if signal_name and signal_path and signal_name not in unique_signals:
                unique_signals[signal_name] = signal_path
        
        for signal_name, signal_path in unique_signals.items():
            sv_code += f"    wire {signal_name} = {signal_path};\n"
        
        sv_code += "\n"
        
        # Initial assertion disable - direct call
        sv_code += "    // Initial assertion disable\n"
        sv_code += "    initial begin\n"
        sv_code += f"        $display($time, \" [{prefix}] Assertion waiver initialized - assertions OFF\");\n"
        sv_code += f"        $assertoff(0, {checker_path});\n"
        sv_code += "    end\n\n"
        
        # Group events by initial blocks
        i = 0
        while i < len(block["events"]):
            event = block["events"][i]
            current_initial = [event]
            
            # Check for connected events (└ +Event)
            j = i + 1
            while j < len(block["events"]) and block["events"][j]["type"].startswith("└"):
                current_initial.append(block["events"][j])
                j += 1
            
            # Generate initial block for this group
            if not event["type"].startswith("└"):
                if event["type"] in ["Forever Loop", "Always Loop", "always begin"]:
                    # Handle always begin - this is an assertion OFF trigger followed by connected events
                    trigger_type = event["trigger_type"].lower()
                    event_name = event["name"]
                    waive_target = event["waive_target"] if event["waive_target"] else ""
                    note = event["note"] if event["note"] and event["note"] != "nan" else None
                    
                    # Calculate full path
                    if waive_target:
                        full_path = f"{checker_path}.{waive_target}"
                    else:
                        full_path = checker_path
                    
                    # Check if there are connected events
                    connected_events = [evt for evt in current_initial[1:] if evt["type"].startswith("└")]
                    
                    sv_code += f"    // Always Begin: {event_name} {trigger_type} (assertion OFF)"
                    if connected_events:
                        for conn_evt in connected_events:
                            conn_type = "enable" if "On Event" in conn_evt["type"] else "disable"
                            sv_code += f" -> {conn_evt['name']} {conn_evt['trigger_type'].lower()} ({conn_type})"
                    sv_code += "\n"
                    
                    # Single initial block for the entire sequence
                    sv_code += "    initial begin\n"
                    sv_code += "        if (global_assert_en) begin\n"
                    
                    # Add note as comment if provided
                    if note:
                        sv_code += f"            // NOTE: {note}\n"
                    
                    # First: Wait for always begin trigger and turn OFF assertions
                    if trigger_type == "wait":
                        sv_code += f"            wait({event_name});\n"
                    elif trigger_type in ["posedge", "negedge"]:
                        sv_code += f"            @({trigger_type} {event_name});\n"
                    else:
                        sv_code += f"            @({trigger_type} {event_name});\n"
                    
                    sv_code += f"            $display($time, \" [{prefix}] Always begin trigger - disabling assertions\");\n"
                    sv_code += f"            $assertoff(0, {full_path});\n"
                    
                    # Then: Process connected events sequentially
                    if connected_events:
                        # Determine the final action based on the last connected event
                        final_action = "off"  # default
                        for evt in connected_events:
                            if "On Event" in evt["type"]:
                                final_action = "on"
                            elif "Off Event" in evt["type"]:
                                final_action = "off"
                            elif "Kill Event" in evt["type"]:
                                final_action = "kill"
                        
                        for evt in connected_events:
                            base_type = evt["type"].replace("└", "").strip()
                            trigger_type_conn = evt["trigger_type"].lower()
                            event_name_conn = evt["name"]
                            repeat_count_conn = evt["repeat_count"] if evt["repeat_count"] and evt["repeat_count"] != "nan" else None
                            note_conn = evt["note"] if evt["note"] and evt["note"] != "nan" else None
                            
                            # Add note as comment if provided
                            if note_conn:
                                sv_code += f"            // NOTE: {note_conn}\n"
                            
                            # Add wait for this connected event (just waiting, no action)
                            if repeat_count_conn and repeat_count_conn.isdigit():
                                repeat_num = int(repeat_count_conn)
                                if trigger_type_conn in ["posedge", "negedge"]:
                                    sv_code += f"            repeat ({repeat_num}) @({trigger_type_conn} {event_name_conn});\n"
                                else:
                                    sv_code += f"            // ERROR: Repeat only supported for posedge/negedge\n"
                                    sv_code += f"            wait({event_name_conn});\n"
                            else:
                                if trigger_type_conn in ["posedge", "negedge"]:
                                    sv_code += f"            @({trigger_type_conn} {event_name_conn});\n"
                                else:
                                    sv_code += f"            wait({event_name_conn});\n"
                        
                        # Apply final action based on the connected event type - DIRECT CALL
                        if final_action == "on":
                            sv_code += f"            $display($time, \" [{prefix}] Connected events completed - enabling assertions\");\n"
                            sv_code += f"            $asserton(0, {full_path});\n"
                        elif final_action == "off":
                            sv_code += f"            $display($time, \" [{prefix}] Connected events completed - disabling assertions\");\n"
                            sv_code += f"            $assertoff(0, {full_path});\n"
                        elif final_action == "kill":
                            sv_code += f"            $display($time, \" [{prefix}] Connected events completed - killing assertions\");\n"
                            sv_code += f"            $assertkill(0, {full_path});\n"
                    
                    sv_code += "        end\n"
                    sv_code += "    end\n\n"
                else:
                    # Handle regular events with inline code (no macros)
                    event_description = event["type"]
                    sv_code += f"    // {event_description}: {event['name']}\n"
                    sv_code += "    initial begin\n"
                    
                    # Check if there are connected events (starting with └)
                    has_connected_events = any(evt["type"].startswith("└") for evt in current_initial[1:])
                    
                    # Determine the primary action from the first event
                    first_event = current_initial[0]
                    primary_action = "off"  # default
                    if first_event["type"] == "On Event":
                        primary_action = "on"
                    elif first_event["type"] == "Off Event":
                        primary_action = "off"
                    elif first_event["type"] == "Kill Event":
                        primary_action = "kill"
                    
                    for evt in current_initial:
                        trigger_type = evt["trigger_type"].lower()
                        event_name = evt["name"]
                        waive_target = evt["waive_target"] if evt["waive_target"] else ""
                        repeat_count = evt["repeat_count"] if evt["repeat_count"] and evt["repeat_count"] != "nan" else None
                        note = evt["note"] if evt["note"] and evt["note"] != "nan" else None
                        
                        # Calculate full path for this event
                        if waive_target:
                            full_path = f"{checker_path}.{waive_target}"
                        else:
                            full_path = checker_path
                        
                        # Add note as comment if provided
                        if note:
                            sv_code += f"        // NOTE: {note}\n"
                        
                        # Check for repeat functionality
                        if repeat_count and repeat_count.isdigit():
                            repeat_num = int(repeat_count)
                            if trigger_type not in ["posedge", "negedge"]:
                                sv_code += f"        // ERROR: Repeat functionality only supported for posedge/negedge triggers, not '{trigger_type}'\n"
                                sv_code += f"        $error($time, \" [ERROR] Repeat count {repeat_num} specified for '{trigger_type}' trigger type - only posedge/negedge supported\");\n"
                                continue
                        
                        # Handle different event types
                        if evt["type"] in ["On Event", "Off Event", "Kill Event"]:
                            if has_connected_events:
                                # Connected events - add global_assert_en check and wait for trigger
                                sv_code += "        if (global_assert_en) begin\n"
                                if repeat_count and repeat_count.isdigit():
                                    repeat_num = int(repeat_count)
                                    if trigger_type in ["posedge", "negedge"]:
                                        sv_code += f"            repeat ({repeat_num}) @({trigger_type} {event_name});\n"
                                    else:
                                        sv_code += f"            // ERROR: Repeat only supported for posedge/negedge\n"
                                        sv_code += f"            wait({event_name});\n"
                                else:
                                    if trigger_type in ["posedge", "negedge"]:
                                        sv_code += f"            @({trigger_type} {event_name});\n"
                                    elif trigger_type == "wait":
                                        sv_code += f"            wait({event_name});\n"
                                    else:
                                        sv_code += f"            @({trigger_type} {event_name});\n"
                                # Don't close the if block yet - will be closed after final action
                            else:
                                # No connected events - perform action immediately using INLINE CODE
                                sv_code += "        if (global_assert_en) begin\n"
                                
                                # Generate inline trigger wait
                                if repeat_count and repeat_count.isdigit():
                                    repeat_num = int(repeat_count)
                                    if trigger_type in ["posedge", "negedge"]:
                                        sv_code += f"            repeat ({repeat_num}) @({trigger_type} {event_name});\n"
                                    else:
                                        sv_code += f"            // ERROR: Repeat only supported for posedge/negedge\n"
                                        sv_code += f"            wait({event_name});\n"
                                else:
                                    if trigger_type == "wait":
                                        sv_code += f"            wait({event_name});\n"
                                    elif trigger_type in ["posedge", "negedge"]:
                                        sv_code += f"            @({trigger_type} {event_name});\n"
                                    else:
                                        sv_code += f"            @({trigger_type} {event_name});\n"
                                
                                # Generate inline action - DIRECT SYSTEM TASK CALLS
                                if evt["type"] == "On Event":
                                    sv_code += f"            $display($time, \" [{prefix}] Trigger detected - enabling assertions\");\n"
                                    sv_code += f"            $asserton(0, {full_path});\n"
                                elif evt["type"] == "Off Event":
                                    sv_code += f"            $display($time, \" [{prefix}] Trigger detected - disabling assertions\");\n"
                                    sv_code += f"            $assertoff(0, {full_path});\n"
                                elif evt["type"] == "Kill Event":
                                    sv_code += f"            $display($time, \" [{prefix}] Kill trigger detected - killing assertions\");\n"
                                    sv_code += f"            $assertkill(0, {full_path});\n"
                                
                                sv_code += "        end\n"
                        elif evt["type"].startswith("└"):
                            # Sequential connected event - add wait in same initial block
                            base_type = evt["type"].replace("└", "").strip()
                            # Add note as comment if provided for connected event
                            if note:
                                sv_code += f"        // NOTE: {note}\n"
                            
                            # Add sequential wait for this event (within the existing if block)
                            if repeat_count and repeat_count.isdigit():
                                repeat_num = int(repeat_count)
                                if trigger_type in ["posedge", "negedge"]:
                                    sv_code += f"            repeat ({repeat_num}) @({trigger_type} {event_name});\n"
                                else:
                                    sv_code += f"            // ERROR: Repeat only supported for posedge/negedge\n"
                                    sv_code += f"            wait({event_name});\n"
                            else:
                                if trigger_type in ["posedge", "negedge"]:
                                    sv_code += f"            @({trigger_type} {event_name});\n"
                                else:
                                    sv_code += f"            wait({event_name});\n"
                            
                            # Continue waiting for more events
                    
                    # Apply the primary action after all events are processed (only if there are connected events)
                    if has_connected_events:
                        first_waive_target = first_event["waive_target"]
                        if first_waive_target:
                            target_path_full = f"{checker_path}.{first_waive_target}"
                        else:
                            target_path_full = checker_path
                            
                        # DIRECT SYSTEM TASK CALLS for connected events
                        if primary_action == "on":
                            sv_code += f"            $display($time, \" [{prefix}] All events completed - enabling assertions\");\n"
                            sv_code += f"            $asserton(0, {target_path_full});\n"
                        elif primary_action == "off":
                            sv_code += f"            $display($time, \" [{prefix}] All events completed - disabling assertions\");\n"
                            sv_code += f"            $assertoff(0, {target_path_full});\n"
                        elif primary_action == "kill":
                            sv_code += f"            $display($time, \" [{prefix}] All events completed - killing assertions\");\n"
                            sv_code += f"            $assertkill(0, {target_path_full});\n"
                        
                        # Close the global_assert_en if block
                        sv_code += "        end\n"
                    
                    sv_code += "    end\n\n"
            
            i = j
        
        sv_code += "endinterface\n\n"
        checker_id += 1

    # Generate main interface with scalable checker management
    sv_code += """
// ====================================================================
// MAIN ASSERTION WAIVER INTERFACE - Central Management Hub (Inline Version)
// ====================================================================

// Main Assertion Waiver Interface - Central Management with Individual Control
interface assertion_waiver_intf();
    // Global assertion enable control via plusargs
    logic global_assert_en;
    initial begin
        global_assert_en = 1'b1;  // Default: assertions ON
        if ($test$plusargs("AW_ALL")) begin
            global_assert_en = 1'b0;  // Global OFF if AW_ALL is set
            $display($time, " [AW_GLOBAL] All assertions globally disabled via AW_ALL");
        end
    end
    
    // Individual Checker Instantiations with Plusargs Control
    // Usage: +AW_1 to disable checker ID 1, +AW_2 to disable checker ID 2, etc.
"""

    # Add individual checker instantiations with ID-based control
    checker_id = 1
    for block in blocks:
        name = block["name"]
        sv_code += f"    `INSTANTIATE_CHECKER_INLINE({name}, {checker_id})\n"
        checker_id += 1

    sv_code += """
    initial begin
        $display("====== Assertion Waiver Status (Inline Version - No Macros) ======");
        $display("global_assert_en: %0d", global_assert_en);
        $display("Individual checker control via +AW_<ID>");
        $display("Direct $asserton/$assertoff/$assertkill calls for maximum compatibility");
        $display("====================================================================");
    end
    
endinterface

`endif
"""
    return sv_code


if __name__ == "__main__":
    args = sys.argv[1:]

    if len(args) < 1:
        print("Usage: python assertion_waiver_builder_inline.py <excel_file> [-debug]")
        sys.exit(1)

    file_path = args[0]
    debug_mode = "-debug" in args

    blocks = parse_excel(file_path, debug=debug_mode)
    sv_code = generate_sv_code(blocks)

    output_file = "assertion_waiver_inline.sv"
    with open(output_file, "w") as f:
        f.write(sv_code)

    print(f"Generated {output_file} (Inline Version - No Macros)") 