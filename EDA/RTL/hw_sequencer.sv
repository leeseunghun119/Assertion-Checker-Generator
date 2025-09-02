class hw_sequencer_c extends uvm_sequencer#(hw_drv_pkt_c);
  
  // reg_block
  my_reg_block my_reg_block1;
  
  `uvm_component_utils(hw_sequencer_c)

  function new(string name, uvm_component parent);
	super.new(name, parent);
  endfunction
 
  
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
     `uvm_info(get_type_name(), $sformatf("build_phase() starts.."), UVM_LOW)
 	//if(!uvm_config_db#(virtual my_interface)::get(this, "", "vif", vif))
    //  `uvm_fatal("NOVIF", "uvm_config_db::get failed")
    my_reg_block1 	= my_reg_block::type_id::create("my_reg_block1");    
  endfunction
  
endclass