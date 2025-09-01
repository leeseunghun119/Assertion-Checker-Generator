`ifndef ASSERTION_WAIVER
`define ASSERTION_WAIVER

// Optimized Macros for Common Waiver Patterns (from builder script)
`define WAIVER_INITIAL_OFF_ON(PREFIX, CHECKER_PATH, TRIGGER_SIGNAL, EVENT_TYPE) \
    initial begin \
        $display($time, " [%s] Assertion waiver initialized - assertions OFF", PREFIX); \
        $assertoff(0, tb_top.CHECKER_PATH``_checker_intf); \
        if (global_assert_en) begin \
            wait(RSTN); \
            $display($time, " [%s] Reset deasserted - waiting for trigger", PREFIX); \
            EVENT_TYPE(TRIGGER_SIGNAL); \
            $display($time, " [%s] Trigger detected - enabling assertions", PREFIX); \
            $asserton(0, tb_top.CHECKER_PATH``_checker_intf); \
        end \
    end

`define WAIVER_FOREVER_LOOP(PREFIX, CHECKER_PATH, CONDITION_SIGNAL, EVENT_TYPE, ACTION) \
    initial begin \
        if (global_assert_en) begin \
            wait(RSTN); \
            forever begin \
                @(EVENT_TYPE CONDITION_SIGNAL); \
                $display($time, " [%s] Transition detected - %s assertions", PREFIX, ACTION ? "waiving" : "enabling"); \
                if (ACTION) $assertoff(0, tb_top.CHECKER_PATH``_checker_intf); \
                else $asserton(0, tb_top.CHECKER_PATH``_checker_intf); \
            end \
        end \
    end

// Parameter-based Waiver Macro
`define WAIVER_PARAM_CONDITION(PREFIX, CHECKER_PATH, PARAM_NAME, EXPECTED_VALUE) \
    always @* begin \
        if (global_assert_en && (PARAM_NAME == EXPECTED_VALUE)) $asserton(0, tb_top.CHECKER_PATH``_checker_intf); \
        else $assertoff(0, tb_top.CHECKER_PATH``_checker_intf); \
    end

// Video Sync Out Checker - ID: 1
interface aw_signals_video_sync_out_checker_intf(input logic global_assert_en);
    wire RSTN = dut.I_RSTN;
    wire vsync_after_scale = dut.w_vsync_after_scale;
    `WAIVER_INITIAL_OFF_ON("AW_VIDEO_SYNC_OUT", video_sync_out, vsync_after_scale, wait)
    `WAIVER_FOREVER_LOOP("AW_VIDEO_SYNC_OUT", video_sync_out, vsync_after_scale, posedge, 1)
    `WAIVER_FOREVER_LOOP("AW_VIDEO_SYNC_OUT", video_sync_out, vsync_after_scale, negedge, 0)
endinterface

// SFR Checker - ID: 2
interface aw_signals_sfr_checker_intf(input logic global_assert_en);
    wire RSTN = dut.I_RSTN;
    wire input_vsync = hw_intf.I_VSYNC;
    wire apb_transaction = apb_if.i_PSEL && apb_if.i_PEN;
    `WAIVER_INITIAL_OFF_ON("AW_SFR", sfr, input_vsync, wait)
    `WAIVER_FOREVER_LOOP("AW_SFR", sfr, apb_transaction, posedge, 1)
    `WAIVER_FOREVER_LOOP("AW_SFR", sfr, apb_transaction, negedge, 0)
    `WAIVER_FOREVER_LOOP("AW_SFR", sfr, input_vsync, posedge, 1)
    `WAIVER_FOREVER_LOOP("AW_SFR", sfr, input_vsync, negedge, 0)
endinterface

// Video Sync Checker - ID: 3
interface aw_signals_video_sync_checker_intf(input logic global_assert_en);
    wire RSTN = dut.I_RSTN;
    wire input_vsync = dut.I_VSYNC;
    `WAIVER_INITIAL_OFF_ON("AW_VIDEO_SYNC", video_sync, input_vsync, wait)
    initial if (global_assert_en) begin
        wait(RSTN);
        wait(input_vsync);
        repeat (3) @(posedge dut.I_CLK);
        $asserton(0, tb_top.video_sync_checker_intf);
    end
    `WAIVER_FOREVER_LOOP("AW_VIDEO_SYNC", video_sync, input_vsync, posedge, 1)
    `WAIVER_FOREVER_LOOP("AW_VIDEO_SYNC", video_sync, input_vsync, negedge, 0)
endinterface

// RAM Control Checker - ID: 4
interface aw_signals_ram_ctrl_checker_intf(input logic global_assert_en);
    wire RSTN = dut.I_RSTN;
    wire cs_change = (dut.w_cs1 || dut.w_cs2 || dut.w_cs3 || dut.w_cs4);
    initial begin
        $display($time, " [AW_RAM_CTRL] Assertion waiver initialized - assertions OFF");
        $assertoff(0, tb_top.ram_ctrl_checker_intf);
        if (global_assert_en) begin
            wait(RSTN);
            $display($time, " [AW_RAM_CTRL] Reset deasserted - enabling assertions");
            $asserton(0, tb_top.ram_ctrl_checker_intf);
        end
    end
    `WAIVER_FOREVER_LOOP("AW_RAM_CTRL", ram_ctrl, cs_change, posedge, 1)
    `WAIVER_FOREVER_LOOP("AW_RAM_CTRL", ram_ctrl, cs_change, negedge, 0)
endinterface

// SRAM Checker Template - IDs: 5-8
interface aw_signals_sram_checker_intf #(parameter int SRAM_ID = 1)(input logic global_assert_en);
    wire RSTN = dut.I_RSTN;
    wire sram_cs = (SRAM_ID == 1) ? dut.w_cs1 :
                   (SRAM_ID == 2) ? dut.w_cs2 :
                   (SRAM_ID == 3) ? dut.w_cs3 : dut.w_cs4;
    wire sram_we = (SRAM_ID == 1) ? dut.w_we1 :
                   (SRAM_ID == 2) ? dut.w_we2 :
                   (SRAM_ID == 3) ? dut.w_we3 : dut.w_we4;
    wire critical_access = sram_cs && sram_we;
    
    initial begin
        $display($time, " [AW_SRAM%0d] Assertion waiver initialized - assertions OFF", SRAM_ID);
        case(SRAM_ID)
            1: $assertoff(0, tb_top.sram1_checker_intf);
            2: $assertoff(0, tb_top.sram2_checker_intf);
            3: $assertoff(0, tb_top.sram3_checker_intf);
            4: $assertoff(0, tb_top.sram4_checker_intf);
        endcase
        if (global_assert_en) begin
            wait(RSTN);
            case(SRAM_ID)
                1: $asserton(0, tb_top.sram1_checker_intf);
                2: $asserton(0, tb_top.sram2_checker_intf);
                3: $asserton(0, tb_top.sram3_checker_intf);
                4: $asserton(0, tb_top.sram4_checker_intf);
            endcase
        end
    end
    
    initial begin
        if (global_assert_en) begin
            wait(RSTN);
            forever begin
                @(posedge critical_access);
                $display($time, " [AW_SRAM%0d] Critical access detected - waiving assertions", SRAM_ID);
                case(SRAM_ID)
                    1: $assertoff(0, tb_top.sram1_checker_intf);
                    2: $assertoff(0, tb_top.sram2_checker_intf);
                    3: $assertoff(0, tb_top.sram3_checker_intf);
                    4: $assertoff(0, tb_top.sram4_checker_intf);
                endcase
                @(negedge critical_access);
                case(SRAM_ID)
                    1: $asserton(0, tb_top.sram1_checker_intf);
                    2: $asserton(0, tb_top.sram2_checker_intf);
                    3: $asserton(0, tb_top.sram3_checker_intf);
                    4: $asserton(0, tb_top.sram4_checker_intf);
                endcase
            end
        end
    end
endinterface

// MUX Output Checker - ID: 9
interface aw_signals_mux_output_checker_intf(input logic global_assert_en);
    wire RSTN = dut.I_RSTN;
    wire mirror_mode_cap = dut.w_mirror_mode_cap;
    wire blur_mode_cap = dut.w_blur_mode_cap;
    wire w_scaler_on = mirror_mode_cap || blur_mode_cap;
    
    logic w_scaler_on_prev, w_scaler_on_stable;
    logic [3:0] mode_stable_cnt;
    
    always @(posedge tb_top.SystemClock or negedge RSTN) begin
        if (!RSTN) begin
            w_scaler_on_prev <= 1'b0;
            mode_stable_cnt <= 4'd0;
            w_scaler_on_stable <= 1'b0;
        end else begin
            w_scaler_on_prev <= w_scaler_on;
            if (w_scaler_on == w_scaler_on_prev) begin
                if (mode_stable_cnt < 4'd10) mode_stable_cnt <= mode_stable_cnt + 1'b1;
            end else mode_stable_cnt <= 4'd0;
            if (w_scaler_on == w_scaler_on_prev && mode_stable_cnt >= 4'd10)
                w_scaler_on_stable <= 1'b1;
            else if (w_scaler_on != w_scaler_on_prev)
                w_scaler_on_stable <= 1'b0;
        end
    end
    
    initial begin
        $display($time, " [AW_MUX_OUTPUT] Assertion waiver initialized - assertions OFF");
        $assertoff(0, tb_top.mux_output_checker_intf);
        if (global_assert_en) begin
            wait(RSTN);
            $asserton(0, tb_top.mux_output_checker_intf);
        end
    end
    
    `WAIVER_FOREVER_LOOP("AW_MUX_OUTPUT", mux_output, w_scaler_on_stable, negedge, 1)
    `WAIVER_FOREVER_LOOP("AW_MUX_OUTPUT", mux_output, w_scaler_on_stable, posedge, 0)
endinterface

// Main Assertion Waiver Interface - Central Management with Global Control
interface assertion_waiver_intf();
    wire RSTN = dut.I_RSTN;
    
    // Global assertion enable control via plusargs
    logic global_assert_en;
    initial begin
        global_assert_en = 1'b1;  // Default: assertions ON
        if ($test$plusargs("AW_ALL")) begin
            global_assert_en = 1'b0;  // Global OFF if AW_ALL is set
            $display($time, " [AW_GLOBAL] All assertions globally disabled via AW_ALL");
        end
    end
    
    // Instantiations with global control
    aw_signals_video_sync_out_checker_intf aw_video_sync_out(.global_assert_en(global_assert_en));
    aw_signals_sfr_checker_intf aw_sfr(.global_assert_en(global_assert_en));
    aw_signals_video_sync_checker_intf aw_video_sync(.global_assert_en(global_assert_en));
    aw_signals_ram_ctrl_checker_intf aw_ram_ctrl(.global_assert_en(global_assert_en));
    aw_signals_sram_checker_intf #(.SRAM_ID(1)) aw_sram1(.global_assert_en(global_assert_en));
    aw_signals_sram_checker_intf #(.SRAM_ID(2)) aw_sram2(.global_assert_en(global_assert_en));
    aw_signals_sram_checker_intf #(.SRAM_ID(3)) aw_sram3(.global_assert_en(global_assert_en));
    aw_signals_sram_checker_intf #(.SRAM_ID(4)) aw_sram4(.global_assert_en(global_assert_en));
    aw_signals_mux_output_checker_intf aw_mux_output(.global_assert_en(global_assert_en));
    
    initial begin
        $display("====== Assertion Waiver Status ======");
        $display("global_assert_en: %0d", global_assert_en);
        $display("======================================");
    end
    
endinterface

`endif 