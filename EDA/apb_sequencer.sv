class apb_sequencer extends uvm_sequencer#(apb_item);
  
  // reg_block
  
  `uvm_component_utils(apb_sequencer)
  
  // Interface
  virtual interface apb_if 	apb_if;
  
  // Constructor
  function new(string name = "apb_sequencer" , uvm_component parent);
    super.new(name, parent);
  endfunction
  
  // Build phase
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if(!uvm_config_db#(virtual apb_if)::get(this, "", "apb_if", apb_if))
      `uvm_fatal("NO APB_IF", "uvm_config_db::get failed")
  endfunction
  
endclass