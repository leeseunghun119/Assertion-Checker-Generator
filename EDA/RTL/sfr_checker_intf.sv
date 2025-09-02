interface sfr_checker_intf #(
    parameter string ASSERT_NAME = "SFR_CHECKER"
)(
    input logic i_CLK,
    input logic i_RST,
    input logic i_log_en,
    input logic i_VSYNC,
    input logic i_check_enable
);

    logic [15:0] exp_vsw,  exp_vbp,  exp_vact,  exp_vfp;
    logic [15:0] exp_hsw,  exp_hbp,  exp_hact,  exp_hfp;
    logic        exp_weight_wr_mode, exp_mirror_mode, exp_blur_mode;
    logic [3:0]  exp_w1,   exp_w2,   exp_w3,   exp_w4,   exp_w5;
    logic [3:0]  exp_w6,   exp_w7,   exp_w8,   exp_w9;

    logic [15:0] dut_vsw,  dut_vbp,  dut_vact,  dut_vfp;
    logic [15:0] dut_hsw,  dut_hbp,  dut_hact,  dut_hfp;
    logic        dut_weight_wr_mode, dut_mirror_mode, dut_blur_mode;
    logic [3:0]  dut_w1,   dut_w2,   dut_w3,   dut_w4,   dut_w5;
    logic [3:0]  dut_w6,   dut_w7,   dut_w8,   dut_w9;

    logic        vsync_edge;
    logic        vsync_prev;
    logic        capture_enable;

    assign dut_vsw             = dut.w_vsw;
    assign dut_vbp             = dut.w_vbp;
    assign dut_vact            = dut.w_vact;
    assign dut_vfp             = dut.w_vfp;
    assign dut_hsw             = dut.w_hsw;
    assign dut_hbp             = dut.w_hbp;
    assign dut_hact            = dut.w_hact;
    assign dut_hfp             = dut.w_hfp;
    assign dut_weight_wr_mode  = dut.w_weight_wr_mode;
    assign dut_mirror_mode     = dut.w_mirror_mode;
    assign dut_blur_mode       = dut.w_blur_mode;
    assign dut_w1              = dut.w_w1;
    assign dut_w2              = dut.w_w2;
    assign dut_w3              = dut.w_w3;
    assign dut_w4              = dut.w_w4;
    assign dut_w5              = dut.w_w5;
    assign dut_w6              = dut.w_w6;
    assign dut_w7              = dut.w_w7;
    assign dut_w8              = dut.w_w8;
    assign dut_w9              = dut.w_w9;

    assign vsync_edge = i_VSYNC && !vsync_prev;

    initial begin
        capture_enable = 1'b1;
    end

    always_ff @(posedge i_CLK or negedge i_RST) begin
        if (!i_RST) begin
            vsync_prev <= 1'b0;
        end else begin
            vsync_prev <= i_VSYNC;
        end
    end

    always_ff @(posedge i_CLK or negedge i_RST) begin
        if (!i_RST) begin
            exp_vsw             <= 16'h0;
            exp_vbp             <= 16'h0;
            exp_vact            <= 16'h0;
            exp_vfp             <= 16'h0;
            exp_hsw             <= 16'h0;
            exp_hbp             <= 16'h0;
            exp_hact            <= 16'h0;
            exp_hfp             <= 16'h0;
            exp_weight_wr_mode  <= 1'b0;
            exp_mirror_mode     <= 1'b0;
            exp_blur_mode       <= 1'b0;
            exp_w1              <= 4'h0;
            exp_w2              <= 4'h0;
            exp_w3              <= 4'h0;
            exp_w4              <= 4'h0;
            exp_w5              <= 4'h0;
            exp_w6              <= 4'h0;
            exp_w7              <= 4'h0;
            exp_w8              <= 4'h0;
            exp_w9              <= 4'h0;
        end else if (apb_if.i_PWRITE && apb_if.i_PSEL && apb_if.i_PEN) begin
            case (apb_if.i_PADDR[7:0])
                8'h00: exp_vsw             <= apb_if.i_PWDATA[15:0];
                8'h04: exp_vbp             <= apb_if.i_PWDATA[15:0];
                8'h08: exp_vact            <= apb_if.i_PWDATA[15:0];
                8'h0C: exp_vfp             <= apb_if.i_PWDATA[15:0];
                8'h10: exp_hsw             <= apb_if.i_PWDATA[15:0];
                8'h14: exp_hbp             <= apb_if.i_PWDATA[15:0];
                8'h18: exp_hact            <= apb_if.i_PWDATA[15:0];
                8'h1C: exp_hfp             <= apb_if.i_PWDATA[15:0];
                8'h20: begin
                    exp_weight_wr_mode     <= apb_if.i_PWDATA[0];
                    exp_mirror_mode        <= apb_if.i_PWDATA[1];
                    exp_blur_mode          <= apb_if.i_PWDATA[2];
                end
                8'h24: begin
                    exp_w1                 <= apb_if.i_PWDATA[3:0];
                    exp_w2                 <= apb_if.i_PWDATA[7:4];
                    exp_w3                 <= apb_if.i_PWDATA[11:8];
                end
                8'h28: begin
                    exp_w4                 <= apb_if.i_PWDATA[3:0];
                    exp_w5                 <= apb_if.i_PWDATA[7:4];
                    exp_w6                 <= apb_if.i_PWDATA[11:8];
                end
                8'h2C: begin
                    exp_w7                 <= apb_if.i_PWDATA[3:0];
                    exp_w8                 <= apb_if.i_PWDATA[7:4];
                    exp_w9                 <= apb_if.i_PWDATA[11:8];
                end
                default: ;
            endcase
            
            if (i_log_en) begin
                $display("[%s] APB auto-capture: ADDR=%h, DATA=%h at %0t", 
                        ASSERT_NAME, apb_if.i_PADDR, apb_if.i_PWDATA, $time);
            end
        end else if (vsync_edge && capture_enable) begin
            exp_vsw             <= dut_vsw;
            exp_vbp             <= dut_vbp;
            exp_vact            <= dut_vact;
            exp_vfp             <= dut_vfp;
            exp_hsw             <= dut_hsw;
            exp_hbp             <= dut_hbp;
            exp_hact            <= dut_hact;
            exp_hfp             <= dut_hfp;
            exp_weight_wr_mode  <= dut_weight_wr_mode;
            exp_mirror_mode     <= dut_mirror_mode;
            exp_blur_mode       <= dut_blur_mode;
            exp_w1              <= dut_w1;
            exp_w2              <= dut_w2;
            exp_w3              <= dut_w3;
            exp_w4              <= dut_w4;
            exp_w5              <= dut_w5;
            exp_w6              <= dut_w6;
            exp_w7              <= dut_w7;
            exp_w8              <= dut_w8;
            exp_w9              <= dut_w9;
            
            if (i_log_en) begin
                $display("[%s] SFR values captured on vsync at %0t", ASSERT_NAME, $time);
                $display("  Video timing: VSW=%h, VBP=%h, VACT=%h, VFP=%h", dut_vsw, dut_vbp, dut_vact, dut_vfp);
                $display("  Horiz timing: HSW=%h, HBP=%h, HACT=%h, HFP=%h", dut_hsw, dut_hbp, dut_hact, dut_hfp);
                $display("  Modes: WR=%b, MIR=%b, BLUR=%b", dut_weight_wr_mode, dut_mirror_mode, dut_blur_mode);
                $display("  Weights: W1=%h, W2=%h, W3=%h, W4=%h, W5=%h", dut_w1, dut_w2, dut_w3, dut_w4, dut_w5);
                $display("  Weights: W6=%h, W7=%h, W8=%h, W9=%h", dut_w6, dut_w7, dut_w8, dut_w9);
            end
        end
    end

    property p_vsw_check;
        @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
        $rose(i_VSYNC) |-> ##10 (dut_vsw == exp_vsw);
    endproperty

    property p_vbp_check;
        @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
        $rose(i_VSYNC) |-> ##10 (dut_vbp == exp_vbp);
    endproperty

    property p_vact_check;
        @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
        $rose(i_VSYNC) |-> ##10 (dut_vact == exp_vact);
    endproperty

    property p_vfp_check;
        @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
        $rose(i_VSYNC) |-> ##10 (dut_vfp == exp_vfp);
    endproperty

    property p_hsw_check;
        @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
        $rose(i_VSYNC) |-> ##10 (dut_hsw == exp_hsw);
    endproperty

    property p_hbp_check;
        @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
        $rose(i_VSYNC) |-> ##10 (dut_hbp == exp_hbp);
    endproperty

    property p_hact_check;
        @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
        $rose(i_VSYNC) |-> ##10 (dut_hact == exp_hact);
    endproperty

    property p_hfp_check;
        @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
        $rose(i_VSYNC) |-> ##10 (dut_hfp == exp_hfp);
    endproperty

    property p_weight_wr_mode_check;
        @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
        $rose(i_VSYNC) |-> ##10 (dut_weight_wr_mode == exp_weight_wr_mode);
    endproperty

    property p_mirror_mode_check;
        @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
        $rose(i_VSYNC) |-> ##10 (dut_mirror_mode == exp_mirror_mode);
    endproperty

    property p_blur_mode_check;
        @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
        $rose(i_VSYNC) |-> ##10 (dut_blur_mode == exp_blur_mode);
    endproperty

    property p_w1_check;
        @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
        $rose(i_VSYNC) |-> ##10 (dut_w1 == exp_w1);
    endproperty

    property p_w2_check;
        @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
        $rose(i_VSYNC) |-> ##10 (dut_w2 == exp_w2);
    endproperty

    property p_w3_check;
        @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
        $rose(i_VSYNC) |-> ##10 (dut_w3 == exp_w3);
    endproperty

    property p_w4_check;
        @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
        $rose(i_VSYNC) |-> ##10 (dut_w4 == exp_w4);
    endproperty

    property p_w5_check;
        @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
        $rose(i_VSYNC) |-> ##10 (dut_w5 == exp_w5);
    endproperty

    property p_w6_check;
        @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
        $rose(i_VSYNC) |-> ##10 (dut_w6 == exp_w6);
    endproperty

    property p_w7_check;
        @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
        $rose(i_VSYNC) |-> ##10 (dut_w7 == exp_w7);
    endproperty

    property p_w8_check;
        @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
        $rose(i_VSYNC) |-> ##10 (dut_w8 == exp_w8);
    endproperty

    property p_w9_check;
        @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
        $rose(i_VSYNC) |-> ##10 (dut_w9 == exp_w9);
    endproperty

    a_vsw_check:             assert property (p_vsw_check)
                             else $error("[%s] VSW mismatch at %0t: Expected=%h, Actual=%h", 
                                        ASSERT_NAME, $time, exp_vsw, dut_vsw);

    a_vbp_check:             assert property (p_vbp_check)
                             else $error("[%s] VBP mismatch at %0t: Expected=%h, Actual=%h", 
                                        ASSERT_NAME, $time, exp_vbp, dut_vbp);

    a_vact_check:            assert property (p_vact_check)
                             else $error("[%s] VACT mismatch at %0t: Expected=%h, Actual=%h", 
                                        ASSERT_NAME, $time, exp_vact, dut_vact);

    a_vfp_check:             assert property (p_vfp_check)
                             else $error("[%s] VFP mismatch at %0t: Expected=%h, Actual=%h", 
                                        ASSERT_NAME, $time, exp_vfp, dut_vfp);

    a_hsw_check:             assert property (p_hsw_check)
                             else $error("[%s] HSW mismatch at %0t: Expected=%h, Actual=%h", 
                                        ASSERT_NAME, $time, exp_hsw, dut_hsw);

    a_hbp_check:             assert property (p_hbp_check)
                             else $error("[%s] HBP mismatch at %0t: Expected=%h, Actual=%h", 
                                        ASSERT_NAME, $time, exp_hbp, dut_hbp);

    a_hact_check:            assert property (p_hact_check)
                             else $error("[%s] HACT mismatch at %0t: Expected=%h, Actual=%h", 
                                        ASSERT_NAME, $time, exp_hact, dut_hact);

    a_hfp_check:             assert property (p_hfp_check)
                             else $error("[%s] HFP mismatch at %0t: Expected=%h, Actual=%h", 
                                        ASSERT_NAME, $time, exp_hfp, dut_hfp);

    a_weight_wr_mode_check:  assert property (p_weight_wr_mode_check)
                             else $error("[%s] WEIGHT_WR_MODE mismatch at %0t: Expected=%b, Actual=%b", 
                                        ASSERT_NAME, $time, exp_weight_wr_mode, dut_weight_wr_mode);

    a_mirror_mode_check:     assert property (p_mirror_mode_check)
                             else $error("[%s] MIRROR_MODE mismatch at %0t: Expected=%b, Actual=%b", 
                                        ASSERT_NAME, $time, exp_mirror_mode, dut_mirror_mode);

    a_blur_mode_check:       assert property (p_blur_mode_check)
                             else $error("[%s] BLUR_MODE mismatch at %0t: Expected=%b, Actual=%b", 
                                        ASSERT_NAME, $time, exp_blur_mode, dut_blur_mode);

    a_w1_check:              assert property (p_w1_check)
                             else $error("[%s] W1 mismatch at %0t: Expected=%h, Actual=%h", 
                                        ASSERT_NAME, $time, exp_w1, dut_w1);

    a_w2_check:              assert property (p_w2_check)
                             else $error("[%s] W2 mismatch at %0t: Expected=%h, Actual=%h", 
                                        ASSERT_NAME, $time, exp_w2, dut_w2);

    a_w3_check:              assert property (p_w3_check)
                             else $error("[%s] W3 mismatch at %0t: Expected=%h, Actual=%h", 
                                        ASSERT_NAME, $time, exp_w3, dut_w3);

    a_w4_check:              assert property (p_w4_check)
                             else $error("[%s] W4 mismatch at %0t: Expected=%h, Actual=%h", 
                                        ASSERT_NAME, $time, exp_w4, dut_w4);

    a_w5_check:              assert property (p_w5_check)
                             else $error("[%s] W5 mismatch at %0t: Expected=%h, Actual=%h", 
                                        ASSERT_NAME, $time, exp_w5, dut_w5);

    a_w6_check:              assert property (p_w6_check)
                             else $error("[%s] W6 mismatch at %0t: Expected=%h, Actual=%h", 
                                        ASSERT_NAME, $time, exp_w6, dut_w6);

    a_w7_check:              assert property (p_w7_check)
                             else $error("[%s] W7 mismatch at %0t: Expected=%h, Actual=%h", 
                                        ASSERT_NAME, $time, exp_w7, dut_w7);

    a_w8_check:              assert property (p_w8_check)
                             else $error("[%s] W8 mismatch at %0t: Expected=%h, Actual=%h", 
                                        ASSERT_NAME, $time, exp_w8, dut_w8);

    a_w9_check:              assert property (p_w9_check)
                             else $error("[%s] W9 mismatch at %0t: Expected=%h, Actual=%h", 
                                        ASSERT_NAME, $time, exp_w9, dut_w9);

endinterface
