package hw_pkg;
	import uvm_pkg::*;
	`include "uvm_macros.svh"

	`include "my_reg_block.sv"
	`include "apb_item.sv"
	`include "apb_adapter.sv"
	`include "apb_sequencer.sv"
	`include "apb_driver.sv"
	//`include "apb_if.sv"

	`include "hw_transfer.sv"
	`include "hw_sequencer.sv"

	`include "vseqr.sv"
	`include "hw_driver.sv"
	`include "hw_monitor.sv"
	`include "hw_agent.sv"
	`include "hw_sb.sv"

	`include "hw_env.sv"
	
	`include "tb.sv"

	`include "hw_basic_test.sv"
	`include "hw_seq_item.sv"
	`include "hw_seq_lib.sv"
	`include "hw_vseq_lib.sv"





endpackage