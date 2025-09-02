class apb_item extends uvm_sequence_item;
  
  `uvm_object_utils(apb_item)
  
  // Field
  rand logic			i_PSEL;
  rand logic			i_PEN;
  rand logic			i_PWRITE;
  rand logic	[31:0] 	i_PADDR;
  rand logic	[31:0] 	i_PWDATA;
  rand logic 	[31:0] 	o_PRDATA;
  
  // Constructor
  function new(string name = "apb_item");
    super.new(name);
  endfunction
  
  // constraint
  constraint addr { i_PADDR inside {0,4}; }
  
endclass