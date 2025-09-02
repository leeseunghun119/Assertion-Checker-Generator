interface ram_ctrl_checker_intf #(
  parameter ASSERT_NAME = "RAM_CTRL_CHECKER"
)();

  // Internal wire assignments - accessing global signals
  wire               i_CLK               = tb_top.SystemClock;
  wire               i_RST               = tb_top.nReset;
  wire               i_log_en            = 1'b1;
  
  // RAM Control signals
  wire               i_cs1               = dut.w_cs1;
  wire               i_cs2               = dut.w_cs2;
  wire               i_cs3               = dut.w_cs3;
  wire               i_cs4               = dut.w_cs4;
  wire               i_we1               = dut.w_we1;
  wire               i_we2               = dut.w_we2;
  wire               i_we3               = dut.w_we3;
  wire               i_we4               = dut.w_we4;
  wire [15:0]        i_addr1             = dut.w_addr1;
  wire [15:0]        i_addr2             = dut.w_addr2;
  wire [15:0]        i_addr3             = dut.w_addr3;
  wire [15:0]        i_addr4             = dut.w_addr4;
  wire [7:0]         i_din1              = dut.w_din1;
  wire [7:0]         i_din2              = dut.w_din2;
  wire [7:0]         i_din3              = dut.w_din3;
  wire [7:0]         i_din4              = dut.w_din4;
  wire [7:0]         i_dout1             = dut.w_dout1;
  wire [7:0]         i_dout2             = dut.w_dout2;
  wire [7:0]         i_dout3             = dut.w_dout3;
  wire [7:0]         i_dout4             = dut.w_dout4;
  
  // Check enable
  wire               i_check_enable      = 1'b1;
  
  // Mode signals for blur operation
  wire               i_blur_mode         = dut.w_blur_mode_cap;
  wire               i_mirror_mode       = dut.w_mirror_mode_cap;

  // SVA Assertions - Focus on meaningful checks for video processing
  
  // Allow multiple RAM selection for blur mode (including all 4 RAMs for complex processing)
  // but ensure at most one write operation at a time for data integrity
  property single_write_operation;
    @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
    $onehot0({(i_cs1 && i_we1), (i_cs2 && i_we2), (i_cs3 && i_we3), (i_cs4 && i_we4)});
  endproperty
  
  SINGLE_WRITE_OPERATION: assert property (single_write_operation)
    else $error("[%s] Multiple write operations! WE1=%b, WE2=%b, WE3=%b, WE4=%b", 
               ASSERT_NAME, (i_cs1 && i_we1), (i_cs2 && i_we2), (i_cs3 && i_we3), (i_cs4 && i_we4));
  
  // Check valid address ranges when CS is active
  property valid_address_ram1;
    @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
    i_cs1 |-> (i_addr1 < 16'h1000);
  endproperty
  
  VALID_ADDRESS_RAM1: assert property (valid_address_ram1)
    else $error("[%s] Invalid address on RAM1! Addr=%h", ASSERT_NAME, i_addr1);
  
  property valid_address_ram2;
    @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
    i_cs2 |-> (i_addr2 < 16'h1000);
  endproperty
  
  VALID_ADDRESS_RAM2: assert property (valid_address_ram2)
    else $error("[%s] Invalid address on RAM2! Addr=%h", ASSERT_NAME, i_addr2);
  
  property valid_address_ram3;
    @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
    i_cs3 |-> (i_addr3 < 16'h1000);
  endproperty
  
  VALID_ADDRESS_RAM3: assert property (valid_address_ram3)
    else $error("[%s] Invalid address on RAM3! Addr=%h", ASSERT_NAME, i_addr3);
  
  property valid_address_ram4;
    @(posedge i_CLK) disable iff (!i_RST || !i_check_enable)
    i_cs4 |-> (i_addr4 < 16'h1000);
  endproperty
  
  VALID_ADDRESS_RAM4: assert property (valid_address_ram4)
    else $error("[%s] Invalid address on RAM4! Addr=%h", ASSERT_NAME, i_addr4);
  
  
endinterface 