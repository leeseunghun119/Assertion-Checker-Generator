`timescale 1ns/1ns


`include "uvm_macros.svh"
`include "hw_pkg.sv"
`include "apb_if.sv"

module tb_top;
  import uvm_pkg::*;
  import hw_pkg::*;  

  // Clock, Reset generation
  reg nReset;
  reg SystemClock = 0;
  
  always #10 SystemClock = ~SystemClock;

  initial begin
    #10 nReset = 0;
    #30 nReset = 1;
  end

//  LINE_BUF_CTRL_TOP dut();
  IP_BLUR_SCALER_TOP dut();

  // Instantiate interface module
  `include "intf_insts.sv"

  

  
  initial begin
    // Set interface into uvm_config_db
    uvm_config_db#(virtual hw_if)::set(null, "uvm_test_top.tb.hw_env.hw_agent*", "vif", hw_intf);  
    uvm_config_db#(virtual hw_if)::set(null, "uvm_test_top.tb.hw_env.hw_sb*", "vif", hw_intf);  
    uvm_config_db#(virtual hw_if)::set(null, "uvm_test_top.tb.vseqr*", "vif", hw_intf);
  	uvm_config_db#(virtual apb_if)::set(null,"*", "apb_if", apb_if);    
    
    run_test("hw_basic_test_c");
  end

  // Dump waves
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars(0, tb_top);
  end

endmodule