interface video_sync_out_checker_intf #(
  parameter ASSERT_NAME = "VIDEO_SYNC_OUT_CHECKER"
)();

  wire               i_CLK               = tb_top.SystemClock;
  wire               i_RST               = tb_top.nReset;
  wire               i_log_en            = 1'b1;
  
  wire               i_vsync_sync        = dut.w_vsync_sync;
  wire               i_mirror_mode_cap   = dut.w_mirror_mode_cap;
  wire               i_blur_mode_cap     = dut.w_blur_mode_cap;
  
  wire [15:0]        i_exp_vsw           = dut.w_vsw;
  wire [15:0]        i_exp_hsw           = dut.w_hsw;
  wire [15:0]        i_exp_vtotal        = dut.w_vsw + dut.w_vbp + dut.w_vact + dut.w_vfp;
  wire [15:0]        i_exp_htotal        = dut.w_hsw + dut.w_hbp + dut.w_hact + dut.w_hfp;
  
  wire               i_o_vsync           = dut.w_vsync_after_scale;
  wire               i_o_hsync           = dut.w_hsync_after_scale;
  
  wire               i_check_enable      = 1'b1;

  logic [15:0]       o_vsync_width_cnt, o_hsync_width_cnt;
  logic              o_vsync_active, o_hsync_active;
  logic              o_vsync_prev, o_hsync_prev;
  logic              o_vsync_edge, o_hsync_edge;
  
  assign o_vsync_edge = i_o_vsync && !o_vsync_prev;
  assign o_hsync_edge = i_o_hsync && !o_hsync_prev;
  
  always @(posedge i_CLK or negedge i_RST) begin
    if (!i_RST) begin
      o_vsync_prev <= 1'b0;
    end else begin
      o_vsync_prev <= i_o_vsync;
    end
  end
  
  always @(posedge i_CLK or negedge i_RST) begin
    if (!i_RST) begin
      o_hsync_prev <= 1'b0;
    end else begin
      o_hsync_prev <= i_o_hsync;
    end
  end
  
  always @(posedge i_CLK or negedge i_RST) begin
    if (!i_RST) begin
      o_vsync_width_cnt <= 16'd0;
    end else begin
      if (o_vsync_edge) begin
        o_vsync_width_cnt <= 16'd1;
      end else if (o_vsync_active && i_o_vsync) begin
        o_vsync_width_cnt <= o_vsync_width_cnt + 1'b1;
      end
    end
  end
  
  always @(posedge i_CLK or negedge i_RST) begin
    if (!i_RST) begin
      o_vsync_active <= 1'b0;
    end else begin
      if (o_vsync_edge) begin
        o_vsync_active <= 1'b1;
      end else if (o_vsync_active && !i_o_vsync) begin
        o_vsync_active <= 1'b0;
      end
    end
  end
  
  always @(posedge i_CLK or negedge i_RST) begin
    if (!i_RST) begin
      o_hsync_width_cnt <= 16'd0;
    end else begin
      if (o_hsync_edge) begin
        o_hsync_width_cnt <= 16'd1;
      end else if (o_hsync_active && i_o_hsync) begin
        o_hsync_width_cnt <= o_hsync_width_cnt + 1'b1;
      end
    end
  end
  
  always @(posedge i_CLK or negedge i_RST) begin
    if (!i_RST) begin
      o_hsync_active <= 1'b0;
    end else begin
      if (o_hsync_edge) begin
        o_hsync_active <= 1'b1;
      end else if (o_hsync_active && !i_o_hsync) begin
        o_hsync_active <= 1'b0;
      end
    end
  end

  property sync_generation;
    @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
    $rose(i_mirror_mode_cap || i_blur_mode_cap) |-> ##[1:100] $rose(i_o_vsync);
  endproperty
  
  SYNC_GENERATION: assert property (sync_generation)
    else $error("[%s] Sync signals not generated when modes are active!", ASSERT_NAME);
  
  property no_sync_when_disabled;
    @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
    (!i_mirror_mode_cap && !i_blur_mode_cap) |-> (!i_o_vsync && !i_o_hsync);
  endproperty
  
  NO_SYNC_WHEN_DISABLED: assert property (no_sync_when_disabled)
    else $error("[%s] Sync signals generated when modes are disabled!", ASSERT_NAME);
  
  property vsync_timing;
    @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
    $rose(i_vsync_sync) |-> ##[1:$] $rose(i_o_vsync);
  endproperty
  
  VSYNC_TIMING: assert property (vsync_timing)
    else $error("[%s] VSYNC timing error! Expected within reasonable time", ASSERT_NAME);
  
  property output_vsync_width;
    @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
    $fell(i_o_vsync) |-> (o_vsync_width_cnt >= 1) && (o_vsync_width_cnt <= 50);
  endproperty
  
  OUTPUT_VSYNC_WIDTH: assert property (output_vsync_width)
    else $error("[%s] Output VSYNC width error! Expected=1-50, Actual=%d", ASSERT_NAME, o_vsync_width_cnt);
  
  property output_hsync_width;
    @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
    $fell(i_o_hsync) |-> (o_hsync_width_cnt >= 1) && (o_hsync_width_cnt <= 20);
  endproperty
  
  OUTPUT_HSYNC_WIDTH: assert property (output_hsync_width)
    else $error("[%s] Output HSYNC width error! Expected=1-20, Actual=%d", ASSERT_NAME, o_hsync_width_cnt);

endinterface