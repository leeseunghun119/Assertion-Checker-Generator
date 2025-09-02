`define MAX_SIZE 6
`define DATA_SIZE 8

class hw_drv_pkt_c extends uvm_sequence_item;

  rand bit I_VSYNC;
  rand bit I_HSYNC;
  rand bit I_DEN;
  rand bit [`DATA_SIZE-1:0] I_DATA;
 
  `uvm_object_utils_begin(hw_drv_pkt_c)
  	`uvm_field_int(I_VSYNC, UVM_DEFAULT)
  	`uvm_field_int(I_HSYNC, UVM_DEFAULT)
  	`uvm_field_int(I_DEN, UVM_DEFAULT)
  	`uvm_field_int(I_DATA, UVM_DEFAULT)
  `uvm_object_utils_end
  
  function new (string name="hw_drv_pkt_c");
	super.new(name);
  endfunction
  
endclass



class hw_mon_pkt_c extends uvm_sequence_item;

  rand bit I_VSYNC;
  rand bit I_HSYNC;
  rand bit I_DEN;
  rand bit [`DATA_SIZE-1:0] I_DATA;
  
  rand bit O_VSYNC;
  rand bit O_HSYNC;
  rand bit O_DEN;
  rand bit [`DATA_SIZE*3-1:0] O_DATA;
  
  `uvm_object_utils_begin(hw_mon_pkt_c)
  	`uvm_field_int(I_VSYNC, UVM_DEFAULT)
  	`uvm_field_int(I_HSYNC, UVM_DEFAULT)
  	`uvm_field_int(I_DEN, UVM_DEFAULT)
  	`uvm_field_int(I_DATA, UVM_DEFAULT)
  	`uvm_field_int(O_VSYNC, UVM_DEFAULT)
  	`uvm_field_int(O_HSYNC, UVM_DEFAULT)
  	`uvm_field_int(O_DEN, UVM_DEFAULT)
  	`uvm_field_int(O_DATA, UVM_DEFAULT)
  `uvm_object_utils_end
  
  function new (string name="hw_mon_pkt_c");
	super.new(name);
  endfunction
  
endclass