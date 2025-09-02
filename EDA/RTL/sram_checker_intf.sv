interface sram_checker_intf #(
  parameter ASSERT_NAME = "SRAM_CHECKER",
  parameter SRAM_ID = 1
)();

  wire               i_CLK               = tb_top.SystemClock;
  wire               i_RST               = tb_top.nReset;
  wire               i_log_en            = 1'b1;
  
  wire               i_cs                = (SRAM_ID == 1) ? dut.w_cs1 :
                                           (SRAM_ID == 2) ? dut.w_cs2 :
                                           (SRAM_ID == 3) ? dut.w_cs3 :
                                                            dut.w_cs4;
  
  wire               i_we                = (SRAM_ID == 1) ? dut.w_we1 :
                                           (SRAM_ID == 2) ? dut.w_we2 :
                                           (SRAM_ID == 3) ? dut.w_we3 :
                                                            dut.w_we4;
  
  wire [15:0]        i_addr              = (SRAM_ID == 1) ? dut.w_addr1 :
                                           (SRAM_ID == 2) ? dut.w_addr2 :
                                           (SRAM_ID == 3) ? dut.w_addr3 :
                                                            dut.w_addr4;
  
  wire [7:0]         i_din               = (SRAM_ID == 1) ? dut.w_din1 :
                                           (SRAM_ID == 2) ? dut.w_din2 :
                                           (SRAM_ID == 3) ? dut.w_din3 :
                                                            dut.w_din4;
  
  wire [7:0]         i_dout              = (SRAM_ID == 1) ? dut.w_dout1 :
                                           (SRAM_ID == 2) ? dut.w_dout2 :
                                           (SRAM_ID == 3) ? dut.w_dout3 :
                                                            dut.w_dout4;
  
  wire               i_check_enable      = 1'b1;

  property memory_enable_check;
    @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
    i_we |-> i_cs;
  endproperty
  
  MEMORY_ENABLE_CHECK: assert property (memory_enable_check)
    else $error("[%s] Memory enable violation! WE=%b without CS=%b", ASSERT_NAME, i_we, i_cs);
  
  property address_check;
    @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
    i_cs |-> (i_addr < 16'h1000);
  endproperty
  
  ADDRESS_CHECK: assert property (address_check)
    else $error("[%s] Address range violation! Addr=%h, Max=0xFFF", ASSERT_NAME, i_addr);
  
  property read_data_check;
    @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
    (i_cs && !i_we) |-> ##1 !$isunknown(i_dout);
  endproperty
  
  READ_DATA_CHECK: assert property (read_data_check)
    else $error("[%s] Read data unknown! Addr=%h, Data=%h", ASSERT_NAME, i_addr, i_dout);
  
  property write_data_stability;
    @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
    (i_cs && i_we) |-> !$isunknown(i_din);
  endproperty
  
  WRITE_DATA_STABILITY: assert property (write_data_stability)
    else $error("[%s] Write data unknown! Addr=%h, Data=%h", ASSERT_NAME, i_addr, i_din);

endinterface