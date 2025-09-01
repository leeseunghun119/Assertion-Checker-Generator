hw_if  hw_intf(SystemClock, nReset);
//apb interface 
apb_if apb_if(.PCLK(SystemClock), .PRSTN(nReset));

assign dut.I_CLK		= SystemClock	  ;
assign dut.I_RSTN		= nReset		  ;
assign dut.I_VSYNC		= hw_intf.I_VSYNC ;
assign dut.I_HSYNC		= hw_intf.I_HSYNC ;
assign dut.I_DEN		= hw_intf.I_DEN   ;
assign dut.I_DATA		= hw_intf.I_DATA  ;

assign hw_intf.O_VSYNC	= dut.O_VSYNC	  ;
assign hw_intf.O_HSYNC	= dut.O_HSYNC	  ;
assign hw_intf.O_DEN	= dut.O_DEN		  ;
assign hw_intf.O_DATA	= dut.O_DATA	  ;

assign dut.PCLK 		= apb_if.PCLK	  ;
assign dut.PRSTN 		= apb_if.PRSTN	  ;
assign dut.i_PSEL 		= apb_if.i_PSEL	  ;
assign dut.i_PEN 		= apb_if.i_PEN	  ;
assign dut.i_PWRITE 	= apb_if.i_PWRITE ;
assign dut.i_PADDR 		= apb_if.i_PADDR  ;
assign dut.i_PWDATA 	= apb_if.i_PWDATA ;
assign apb_if.o_PRDATA 	= dut.o_PRDATA    ;

// Checker Interface Instances
sfr_checker_intf #(.ASSERT_NAME("SFR_CHECKER")) sfr_checker_intf(
    .i_CLK(SystemClock),
    .i_RST(nReset),
    .i_log_en(1'b1),
    .i_VSYNC(hw_intf.I_VSYNC),
    .i_check_enable(1'b1)
);

video_sync_checker_intf #(.ASSERT_NAME("VIDEO_SYNC_CHECKER")) video_sync_checker_intf();

ram_ctrl_checker_intf #(.ASSERT_NAME("RAM_CTRL_CHECKER")) ram_ctrl_checker_intf();

sram_checker_intf #(.ASSERT_NAME("SRAM1_CHECKER"), .SRAM_ID(1)) sram1_checker_intf();

sram_checker_intf #(.ASSERT_NAME("SRAM2_CHECKER"), .SRAM_ID(2)) sram2_checker_intf();

sram_checker_intf #(.ASSERT_NAME("SRAM3_CHECKER"), .SRAM_ID(3)) sram3_checker_intf();

sram_checker_intf #(.ASSERT_NAME("SRAM4_CHECKER"), .SRAM_ID(4)) sram4_checker_intf();

video_sync_out_checker_intf #(.ASSERT_NAME("VIDEO_SYNC_OUT_CHECKER")) video_sync_out_checker_intf();

mux_output_checker_intf #(.ASSERT_NAME("MUX_OUTPUT_CHECKER")) mux_output_checker_intf();

assertion_waiver_intf aw_intf();