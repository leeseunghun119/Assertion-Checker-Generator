// Test class
class hw_basic_test_c extends uvm_test;
  `uvm_component_utils(hw_basic_test_c)
  
  tb_c	tb;
 
  function new (string name, uvm_component parent);
	super.new(name, parent);
  endfunction  
  
  function void build_phase(uvm_phase phase);
	super.build_phase(phase);
      	
    tb = tb_c::type_id::create("tb", this);

    uvm_config_db#(uvm_object_wrapper)::set(this, "tb.vseqr.run_phase", "default_sequence", hw_basic_vseq_c::type_id::get());
  endfunction
  
  virtual function void start_of_simulation_phase(uvm_phase phase);
    super.start_of_simulation_phase(phase);
    
    uvm_top.print_topology();
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    `uvm_info(get_type_name(), $sformatf("run_phase() starts.."), UVM_LOW)
    
    //phase.raise_objection(this);
    //hw_basic_vseq = hw_basic_vseq_c::type_id::create("hw_basic_vseq");
    //hw_basic_vseq.start(tb.vseqr);
      //ERROR: hw_basic_vseq.start(tb.vseqr.hw_seqr);
    //phase.drop_objection(this);
    
    `uvm_info(get_type_name(), $sformatf("run_phase() ends.."), UVM_LOW)
  endtask
  

  
endclass