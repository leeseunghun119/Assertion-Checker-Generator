interface mux_output_checker_intf #(
  parameter ASSERT_NAME = "MUX_OUTPUT_CHECKER"
)();

  wire               i_CLK               = tb_top.SystemClock;
  wire               i_RST               = tb_top.nReset;
  wire               i_log_en            = 1'b1;
  
  wire               i_mirror_mode_cap   = dut.u_mux_output.i_mirror_mode_cap;
  wire               i_blur_mode_cap     = dut.u_mux_output.i_blur_mode_cap;
  
  wire               i_vsync_bypass      = dut.u_mux_output.i_vsync_bypass;
  wire               i_hsync_bypass      = dut.u_mux_output.i_hsync_bypass;
  wire               i_den_bypass        = dut.u_mux_output.i_den_bypass;
  wire [7:0]         i_data_bypass       = dut.u_mux_output.i_data_bypass;
  
  wire               i_vsync_scaler      = dut.u_mux_output.i_vsync_scaler;
  wire               i_hsync_scaler      = dut.u_mux_output.i_hsync_scaler;
  wire               i_den_scaler        = dut.u_mux_output.i_den_scaler;
  wire [7:0]         i_data_scaler       = dut.u_mux_output.i_data_scaler;
  
  wire               i_o_vsync           = dut.u_mux_output.o_vsync;
  wire               i_o_hsync           = dut.u_mux_output.o_hsync;
  wire               i_o_den             = dut.u_mux_output.o_den;
  wire [7:0]         i_o_data            = dut.u_mux_output.o_data;
  
  wire               i_check_enable      = 1'b1;
  
  wire               w_scaler_on         = i_mirror_mode_cap || i_blur_mode_cap;

  property scaler_vsync_check;
    @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
    w_scaler_on |=> (i_o_vsync == $past(i_vsync_scaler));
  endproperty
  
  SCALER_VSYNC_CHECK: assert property (scaler_vsync_check)
    else $error("[%s] Scaler VSYNC mismatch! Expected=%b, Actual=%b", 
               ASSERT_NAME, $past(i_vsync_scaler), i_o_vsync);
  
  property scaler_hsync_check;
    @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
    w_scaler_on |=> (i_o_hsync == $past(i_hsync_scaler));
  endproperty
  
  SCALER_HSYNC_CHECK: assert property (scaler_hsync_check)
    else $error("[%s] Scaler HSYNC mismatch! Expected=%b, Actual=%b", 
               ASSERT_NAME, $past(i_hsync_scaler), i_o_hsync);
  
  property scaler_den_check;
    @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
    w_scaler_on |=> (i_o_den == $past(i_den_scaler));
  endproperty
  
  SCALER_DEN_CHECK: assert property (scaler_den_check)
    else $error("[%s] Scaler DEN mismatch! Expected=%b, Actual=%b", 
               ASSERT_NAME, $past(i_den_scaler), i_o_den);
  
  property scaler_data_check;
    @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
    w_scaler_on |=> (i_o_data == $past(i_data_scaler));
  endproperty
  
  SCALER_DATA_CHECK: assert property (scaler_data_check)
    else $error("[%s] Scaler DATA mismatch! Expected=%h, Actual=%h", 
               ASSERT_NAME, $past(i_data_scaler), i_o_data);
  
  property bypass_vsync_check;
    @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
    !w_scaler_on |=> ##1 (i_o_vsync == $past(i_vsync_bypass, 2));
  endproperty
  
  BYPASS_VSYNC_CHECK: assert property (bypass_vsync_check)
    else $error("[%s] Bypass VSYNC mismatch! Expected=%b, Actual=%b", 
               ASSERT_NAME, $past(i_vsync_bypass, 2), i_o_vsync);
  
  property bypass_hsync_check;
    @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
    !w_scaler_on |=> ##1 (i_o_hsync == $past(i_hsync_bypass, 2));
  endproperty
  
  BYPASS_HSYNC_CHECK: assert property (bypass_hsync_check)
    else $error("[%s] Bypass HSYNC mismatch! Expected=%b, Actual=%b", 
               ASSERT_NAME, $past(i_hsync_bypass, 2), i_o_hsync);
  
  property bypass_den_check;
    @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
    !w_scaler_on |=> ##1 (i_o_den == $past(i_den_bypass, 2));
  endproperty
  
  BYPASS_DEN_CHECK: assert property (bypass_den_check)
    else $error("[%s] Bypass DEN mismatch! Expected=%b, Actual=%b", 
               ASSERT_NAME, $past(i_den_bypass, 2), i_o_den);
  
  property bypass_data_check;
    @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
    !w_scaler_on |=> ##1 (i_o_data == $past(i_data_bypass, 2));
  endproperty
  
  BYPASS_DATA_CHECK: assert property (bypass_data_check)
    else $error("[%s] Bypass DATA mismatch! Expected=%h, Actual=%h", 
               ASSERT_NAME, $past(i_data_bypass, 2), i_o_data);

endinterface