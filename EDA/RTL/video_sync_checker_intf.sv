interface video_sync_checker_intf #(
  parameter ASSERT_NAME = "VIDEO_SYNC_CHECKER"
)();

  wire               i_CLK               = tb_top.SystemClock;
  wire               i_RST               = tb_top.nReset;
  wire               i_log_en            = 1'b1;
  
  wire               i_VSYNC             = dut.I_VSYNC;
  wire               i_HSYNC             = dut.I_HSYNC;
  wire               i_DEN               = dut.I_DEN;
  wire [7:0]         i_DATA              = dut.I_DATA;
  
  wire [15:0]        i_exp_vsync_count   = dut.w_vact;
  wire [15:0]        i_exp_hsync_count   = dut.w_hact;
  wire [15:0]        i_exp_data_count    = dut.w_vact * dut.w_hact;
  wire [15:0]        i_exp_vsw_width_cnt = dut.w_vsw;
  wire [15:0]        i_exp_hsw_width_cnt = dut.w_hsw;
  wire [15:0]        i_exp_htotal_cnt    = dut.w_hsw + dut.w_hfp + dut.w_hbp + dut.w_hact;
  
  wire               i_check_enable      = 1'b1;
  
  logic [15:0]       hsync_cnt, data_cnt;
  logic              vsync_prev, hsync_prev, frame_start;
  logic              vsync_edge, hsync_edge;
  logic [15:0]       vsync_width_cnt, hsync_width_cnt;

  
  assign vsync_edge = i_VSYNC && !vsync_prev;
  assign hsync_edge = i_HSYNC && !hsync_prev;
  assign frame_start = vsync_edge;
  
  always @(posedge i_CLK or negedge i_RST) begin
    if (!i_RST) begin
      vsync_prev <= 1'b0;
    end else begin
      vsync_prev <= i_VSYNC;
    end
  end
  
  always @(posedge i_CLK or negedge i_RST) begin
    if (!i_RST) begin
      hsync_prev <= 1'b0;
    end else begin
      hsync_prev <= i_HSYNC;
    end
  end
  
  always @(posedge i_CLK or negedge i_RST) begin
    if (!i_RST) begin
      hsync_cnt <= 16'd0;
    end else begin
      if (frame_start) begin
        hsync_cnt <= 16'd0;
      end else if (hsync_edge) begin
        hsync_cnt <= hsync_cnt + 1'b1;
      end
    end
  end
  
  always @(posedge i_CLK or negedge i_RST) begin
    if (!i_RST) begin
      data_cnt <= 16'd0;
    end else begin
      if (frame_start) begin
        data_cnt <= 16'd0;
      end else if (i_DEN) begin
        data_cnt <= data_cnt + 1'b1;
      end
    end
  end
  
  always @(posedge i_CLK or negedge i_RST) begin
    if (!i_RST) begin
      vsync_width_cnt <= 16'd0;
    end else begin
      if (vsync_edge) begin
        vsync_width_cnt <= 16'd1;
      end else if (i_VSYNC) begin
        vsync_width_cnt <= vsync_width_cnt + 1'b1;
      end
    end
  end
  
  
  always @(posedge i_CLK or negedge i_RST) begin
    if (!i_RST) begin
      hsync_width_cnt <= 16'd0;
    end else begin
      if (hsync_edge) begin
        hsync_width_cnt <= 16'd1;
      end else if (i_HSYNC) begin
        hsync_width_cnt <= hsync_width_cnt + 1'b1;
      end
    end
  end
  
  
  property hsync_count_check;
    @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
    frame_start |-> ##1 (hsync_cnt >= (i_exp_hsync_count - 2)) && 
                        (hsync_cnt <= (i_exp_hsync_count + 2));
  endproperty
  
  HSYNC_COUNT_CHECK: assert property (hsync_count_check)
    else $error("[%s] HSYNC count mismatch! Expected=%d, Actual=%d", 
               ASSERT_NAME, i_exp_hsync_count, hsync_cnt);
  
  property data_count_check;
    @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
    frame_start |-> ##1 (data_cnt >= (i_exp_data_count - 5)) && 
                        (data_cnt <= (i_exp_data_count + 5));
  endproperty
  
  DATA_COUNT_CHECK: assert property (data_count_check)
    else $error("[%s] Data count mismatch! Expected=%d, Actual=%d", 
               ASSERT_NAME, i_exp_data_count, data_cnt);

  property vsync_width_check;
    @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
    $fell(i_VSYNC) |-> (vsync_width_cnt >= i_exp_htotal_cnt * i_exp_vsw_width_cnt - 1) && (vsync_width_cnt <= i_exp_htotal_cnt * i_exp_vsw_width_cnt + 2);
  endproperty
  
  VSYNC_WIDTH_CHECK: assert property (vsync_width_check)
    else $error("[%s] VSYNC width error! Expected=%d, Actual=%d", ASSERT_NAME, i_exp_htotal_cnt * i_exp_vsw_width_cnt, vsync_width_cnt);
  
  property hsync_width_check;
    @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
    $fell(i_HSYNC) |-> (hsync_width_cnt >= i_exp_hsw_width_cnt - 1) && (hsync_width_cnt <= i_exp_hsw_width_cnt + 2);
  endproperty
  
  HSYNC_WIDTH_CHECK: assert property (hsync_width_check)
    else $error("[%s] HSYNC width error! Expected=%d, Actual=%d", ASSERT_NAME, hsync_width_cnt, hsync_width_cnt);

endinterface