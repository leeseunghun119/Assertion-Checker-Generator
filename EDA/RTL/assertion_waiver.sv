`ifndef ASSERTION_WAIVER
`define ASSERTION_WAIVER

// Video Sync Out Checker Assertion Waiver Interface - ID: 1
interface aw_signals_Video_Sync_Out_Checker_intf(input logic waiver_enable);
    
    wire RSTN;
    assign RSTN = dut.I_RSTN;
    
    wire vsync_after_scale = dut.w_vsync_after_scale;
    
    initial begin
        $display($time, " [AW_VIDEO_SYNC_OUT] Assertion waiver initialized - all assertions OFF");
        $assertoff(0, tb_top.video_sync_out_checker_intf);
        
        if (waiver_enable) begin
            wait(RSTN);
            $display($time, " [AW_VIDEO_SYNC_OUT] Reset deasserted - waiting for first vsync");
            
            wait(vsync_after_scale);
            $display($time, " [AW_VIDEO_SYNC_OUT] First vsync detected - enabling assertions");
            $asserton(0, tb_top.video_sync_out_checker_intf);
        end
    end
    
    initial begin
        if (waiver_enable) begin
            wait(RSTN);
            wait(vsync_after_scale);
            
            forever begin
                @(posedge vsync_after_scale);
                $display($time, " [AW_VIDEO_SYNC_OUT] VSYNC transition - temporarily waiving assertions");
                $assertoff(0, tb_top.video_sync_out_checker_intf);
                
                @(negedge vsync_after_scale);
                $asserton(0, tb_top.video_sync_out_checker_intf);
                $display($time, " [AW_VIDEO_SYNC_OUT] VSYNC transition waiver completed");
            end
        end
    end
    
endinterface

// SFR Checker Assertion Waiver Interface - ID: 2
interface aw_signals_sfr_checker_intf(
    input wire waiver_enable
);
    
    wire RSTN;
    assign RSTN = dut.I_RSTN;
    
    wire input_vsync = hw_intf.I_VSYNC;
    wire apb_transaction = apb_if.i_PSEL && apb_if.i_PEN;
    
    initial begin
        $display($time, " [AW_SFR] SFR checker assertion waiver initialized - assertions OFF");
        $assertoff(0, tb_top.sfr_checker_intf);
        
        if (waiver_enable) begin
            wait(RSTN);
            $display($time, " [AW_SFR] Reset deasserted - waiting for first vsync");
            
            wait(input_vsync);
            $display($time, " [AW_SFR] First vsync detected - enabling SFR checker assertions");
            $asserton(0, tb_top.sfr_checker_intf);
        end
    end
    
    initial begin
        if (waiver_enable) begin
            wait(RSTN);
            wait(input_vsync);
            
            forever begin
                @(posedge apb_transaction);
                $display($time, " [AW_SFR] APB transaction detected - waiving SFR assertions");
                $assertoff(0, tb_top.sfr_checker_intf);
                
                @(negedge apb_transaction);
                $asserton(0, tb_top.sfr_checker_intf);
                $display($time, " [AW_SFR] APB transaction waiver completed");
            end
        end
    end
    
    initial begin
        if (waiver_enable) begin
            wait(RSTN);
            wait(input_vsync);
            
            forever begin
                @(posedge input_vsync);
                $display($time, " [AW_SFR] VSYNC detected - waiving during SFR update period");
                $assertoff(0, tb_top.sfr_checker_intf);
                
                @(negedge input_vsync);
                $asserton(0, tb_top.sfr_checker_intf);
                $display($time, " [AW_SFR] SFR update waiver completed");
            end
        end
    end
    
endinterface

// Video Sync Checker Assertion Waiver Interface - ID: 3
interface aw_signals_video_sync_checker_intf(
    input wire waiver_enable
);
    
    wire RSTN;
    assign RSTN = dut.I_RSTN;
    
    wire input_vsync;
    assign input_vsync = dut.I_VSYNC;
    
    initial begin
        $display($time, " [AW_VIDEO_SYNC] Video sync checker assertion waiver initialized");
        $assertoff(0, tb_top.video_sync_checker_intf);
        
        
            wait(RSTN);
            wait(input_vsync);
            repeat (3) @(posedge dut.I_CLK);

            $asserton(0, tb_top.video_sync_checker_intf);
            $display($time, " [AW_VIDEO_SYNC] Video sync checker assertions enabled");
        
    end
    
    initial begin
        
            wait(RSTN);
            wait(input_vsync);
            
            forever begin
                @(posedge input_vsync);
                $display($time, " [AW_VIDEO_SYNC] Frame transition detected - waiving assertions");
                $assertoff(0, tb_top.video_sync_checker_intf);
                
                @(negedge input_vsync);
                $asserton(0, tb_top.video_sync_checker_intf);
                $display($time, " [AW_VIDEO_SYNC] Frame transition waiver completed");
            end
        
    end
    
endinterface

// RAM Control Checker Assertion Waiver Interface - ID: 4
interface aw_signals_ram_ctrl_checker_intf(
    input wire waiver_enable
);
    
    wire RSTN;
    assign RSTN = dut.I_RSTN;
    
    wire cs_change = (dut.w_cs1 || dut.w_cs2 || dut.w_cs3 || dut.w_cs4);
    
    initial begin
        $display($time, " [AW_RAM_CTRL] RAM control checker assertion waiver initialized");
        $assertoff(0, tb_top.ram_ctrl_checker_intf);
        
        if (waiver_enable) begin
            wait(RSTN);
            $asserton(0, tb_top.ram_ctrl_checker_intf);
            $display($time, " [AW_RAM_CTRL] RAM control checker assertions enabled");
        end
    end
    
    initial begin
        if (waiver_enable) begin
            wait(RSTN);
            
            forever begin
                @(posedge cs_change);
                $display($time, " [AW_RAM_CTRL] RAM access detected - waiving assertions");
                $assertoff(0, tb_top.ram_ctrl_checker_intf);
                
                @(negedge cs_change);
                $asserton(0, tb_top.ram_ctrl_checker_intf);
                $display($time, " [AW_RAM_CTRL] RAM access waiver completed");
            end
        end
    end
    
endinterface

// SRAM Checker Assertion Waiver Interface - ID: 5,6,7,8 (for SRAM1,2,3,4)
interface aw_signals_sram_checker_intf #(
    parameter int SRAM_ID = 1
)(
    input wire waiver_enable
);
    
    wire RSTN;
    assign RSTN = dut.I_RSTN;
    
    wire sram_cs = (SRAM_ID == 1) ? dut.w_cs1 :
                   (SRAM_ID == 2) ? dut.w_cs2 :
                   (SRAM_ID == 3) ? dut.w_cs3 :
                                    dut.w_cs4;
    
    wire sram_we = (SRAM_ID == 1) ? dut.w_we1 :
                   (SRAM_ID == 2) ? dut.w_we2 :
                   (SRAM_ID == 3) ? dut.w_we3 :
                                    dut.w_we4;
    
    wire critical_access = sram_cs && sram_we;
    
    initial begin
        $display($time, " [AW_SRAM%0d] SRAM checker assertion waiver initialized", SRAM_ID);
        case(SRAM_ID)
            1: $assertoff(0, tb_top.sram1_checker_intf);
            2: $assertoff(0, tb_top.sram2_checker_intf);
            3: $assertoff(0, tb_top.sram3_checker_intf);
            4: $assertoff(0, tb_top.sram4_checker_intf);
        endcase
        
        if (waiver_enable) begin
            wait(RSTN);
            case(SRAM_ID)
                1: $asserton(0, tb_top.sram1_checker_intf);
                2: $asserton(0, tb_top.sram2_checker_intf);
                3: $asserton(0, tb_top.sram3_checker_intf);
                4: $asserton(0, tb_top.sram4_checker_intf);
            endcase
            $display($time, " [AW_SRAM%0d] SRAM checker assertions enabled", SRAM_ID);
        end
    end
    
    initial begin
        if (waiver_enable) begin
            wait(RSTN);
            
            forever begin
                @(posedge critical_access);
                $display($time, " [AW_SRAM%0d] Critical SRAM access detected - waiving assertions", SRAM_ID);
                
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
                $display($time, " [AW_SRAM%0d] Critical SRAM access waiver completed", SRAM_ID);
            end
        end
    end
    
endinterface

// MUX Output Checker Assertion Waiver Interface - ID: 9
interface aw_signals_mux_output_checker_intf(
    input wire waiver_enable
);
    
    wire RSTN;
    assign RSTN = dut.I_RSTN;
    
    wire mirror_mode_cap = dut.w_mirror_mode_cap;
    wire blur_mode_cap = dut.w_blur_mode_cap;
    wire w_scaler_on = mirror_mode_cap || blur_mode_cap;
    
    logic w_scaler_on_prev, w_scaler_on_stable;
    logic [3:0] mode_stable_cnt;
    
    always @(posedge tb_top.SystemClock or negedge RSTN) begin
        if (!RSTN) begin
            w_scaler_on_prev <= 1'b0;
        end else begin
            w_scaler_on_prev <= w_scaler_on;
        end
    end
    
    always @(posedge tb_top.SystemClock or negedge RSTN) begin
        if (!RSTN) begin
            mode_stable_cnt <= 4'd0;
        end else begin
            if (w_scaler_on == w_scaler_on_prev) begin
                if (mode_stable_cnt < 4'd10) begin
                    mode_stable_cnt <= mode_stable_cnt + 1'b1;
                end
            end else begin
                mode_stable_cnt <= 4'd0;
            end
        end
    end
    
    always @(posedge tb_top.SystemClock or negedge RSTN) begin
        if (!RSTN) begin
            w_scaler_on_stable <= 1'b0;
        end else begin
            if (w_scaler_on == w_scaler_on_prev && mode_stable_cnt >= 4'd10) begin
                w_scaler_on_stable <= 1'b1;
            end else if (w_scaler_on != w_scaler_on_prev) begin
                w_scaler_on_stable <= 1'b0;
            end
        end
    end
    
    initial begin
        $display($time, " [AW_MUX_OUTPUT] MUX output checker assertion waiver initialized");
        $assertoff(0, tb_top.mux_output_checker_intf);
        
        if (waiver_enable) begin
            wait(RSTN);
            $asserton(0, tb_top.mux_output_checker_intf);
            $display($time, " [AW_MUX_OUTPUT] MUX output checker assertions enabled");
        end
    end
    
    initial begin
        if (waiver_enable) begin
            wait(RSTN);
            
            forever begin
                @(negedge w_scaler_on_stable);
                $display($time, " [AW_MUX_OUTPUT] Mode transition detected - waiving assertions");
                $assertoff(0, tb_top.mux_output_checker_intf);
                
                @(posedge w_scaler_on_stable);
                $asserton(0, tb_top.mux_output_checker_intf);
                $display($time, " [AW_MUX_OUTPUT] Mode transition stabilized - assertions enabled");
            end
        end
    end
    
endinterface

// Main Assertion Waiver Interface - Central Management
interface assertion_waiver_intf();

  wire RSTN;
  assign RSTN = dut.I_RSTN;
   
  logic aw_video_sync_out_enable;    
  logic aw_sfr_enable;
  logic aw_video_sync_enable;
  logic aw_ram_ctrl_enable;
  logic aw_sram1_enable;
  logic aw_sram2_enable;
  logic aw_sram3_enable;
  logic aw_sram4_enable;
  logic aw_mux_output_enable;

  bit aw_all, assertion_off;
  bit aw_1, aw_2, aw_3, aw_4, aw_5, aw_6, aw_7, aw_8, aw_9;

  initial begin
    aw_all         = $test$plusargs("AW_ALL");
    aw_1           = $test$plusargs("AW_1");
    aw_2           = $test$plusargs("AW_2");
    aw_3           = $test$plusargs("AW_3");
    aw_4           = $test$plusargs("AW_4");
    aw_5           = $test$plusargs("AW_5");
    aw_6           = $test$plusargs("AW_6");
    aw_7           = $test$plusargs("AW_7");
    aw_8           = $test$plusargs("AW_8");
    aw_9           = $test$plusargs("AW_9");

    aw_video_sync_out_enable = !(aw_all || aw_1);
    aw_sfr_enable            = !(aw_all || aw_2);
    aw_video_sync_enable     = !(aw_all || aw_3);
    aw_ram_ctrl_enable       = !(aw_all || aw_4);
    aw_sram1_enable          = !(aw_all || aw_5);
    aw_sram2_enable          = !(aw_all || aw_6);
    aw_sram3_enable          = !(aw_all || aw_7);
    aw_sram4_enable          = !(aw_all || aw_8);
    aw_mux_output_enable     = !(aw_all || aw_9);
  end


  // Interface instances with enable signals
  aw_signals_Video_Sync_Out_Checker_intf aw_video_sync_out(.waiver_enable(aw_video_sync_out_enable));
  aw_signals_sfr_checker_intf            aw_sfr(.waiver_enable(!aw_sfr_enable));
  aw_signals_video_sync_checker_intf     aw_video_sync(.waiver_enable(aw_video_sync_enable));
  aw_signals_ram_ctrl_checker_intf       aw_ram_ctrl(.waiver_enable(aw_ram_ctrl_enable));
  aw_signals_sram_checker_intf           #(.SRAM_ID(1)) aw_sram1(.waiver_enable(aw_sram1_enable));
  aw_signals_sram_checker_intf           #(.SRAM_ID(2)) aw_sram2(.waiver_enable(aw_sram2_enable));
  aw_signals_sram_checker_intf           #(.SRAM_ID(3)) aw_sram3(.waiver_enable(aw_sram3_enable));
  aw_signals_sram_checker_intf           #(.SRAM_ID(4)) aw_sram4(.waiver_enable(aw_sram4_enable));
  aw_signals_mux_output_checker_intf     aw_mux_output(.waiver_enable(aw_mux_output_enable));
    
  initial begin
    $display("====== Assertion Waiver Status ======");
    $display("aw_video_sync_out_enable : %0d", aw_video_sync_out_enable);
    $display("aw_sfr_enable            : %0d", aw_sfr_enable);
    $display("aw_video_sync_enable     : %0d", aw_video_sync_enable);
    $display("aw_ram_ctrl_enable       : %0d", aw_ram_ctrl_enable);
    $display("aw_sram1_enable          : %0d", aw_sram1_enable);
    $display("aw_sram2_enable          : %0d", aw_sram2_enable);
    $display("aw_sram3_enable          : %0d", aw_sram3_enable);
    $display("aw_sram4_enable          : %0d", aw_sram4_enable);
    $display("aw_mux_output_enable     : %0d", aw_mux_output_enable);
    $display("======================================");
  end

    initial begin

      // Display current waiver status  
      if (!aw_video_sync_out_enable)   $display($time, " [AW_GLOBAL]   AW_1 (Video Sync Out): DISABLED");
      if (!aw_sfr_enable)              $display($time, " [AW_GLOBAL]   AW_2 (SFR): DISABLED");
      if (!aw_video_sync_enable)       $display($time, " [AW_GLOBAL]   AW_3 (Video Sync): DISABLED");
      if (!aw_ram_ctrl_enable)         $display($time, " [AW_GLOBAL]   AW_4 (RAM Control): DISABLED");
      if (!aw_sram1_enable)            $display($time, " [AW_GLOBAL]   AW_5 (SRAM1): DISABLED");
      if (!aw_sram2_enable)            $display($time, " [AW_GLOBAL]   AW_6 (SRAM2): DISABLED");
      if (!aw_sram3_enable)            $display($time, " [AW_GLOBAL]   AW_7 (SRAM3): DISABLED");
      if (!aw_sram4_enable)            $display($time, " [AW_GLOBAL]   AW_8 (SRAM4): DISABLED");
      if (!aw_mux_output_enable)       $display($time, " [AW_GLOBAL]   AW_9 (MUX Output): DISABLED");
                                       $display($time, " [AW_GLOBAL] ========================================");

        
        wait(RSTN);
            $display($time, " [AW_GLOBAL] System ready - assertion waivers configured");
    end
    
endinterface



`endif 