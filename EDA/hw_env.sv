//`include "vseqr.sv"
class hw_env_c extends uvm_env;
  `uvm_component_utils(hw_env_c)
  
  hw_agent_c	hw_agent;
  hw_sb_c		hw_sb;

  //vseqr_c       vseqr;


  
  function new(string name, uvm_component parent);
	super.new(name, parent);
  endfunction  
  
  function void build_phase(uvm_phase phase);
	super.build_phase(phase);
    `uvm_info(get_type_name(), $sformatf("build_phase() starts.."), UVM_LOW)
    hw_agent = hw_agent_c::type_id::create("hw_agent", this);
    hw_sb = hw_sb_c::type_id::create("hw_sb", this);   
    
    // virtual sequencer
    //vseqr 			= vseqr_c::type_id::create("vseqr", this);

   
  endfunction  
  
  
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
	  // scoreboard의 analysis port와 monitor의 analysis port를 연결
    hw_agent.hw_monitor.in_data_port.connect(hw_sb.in_hw_imp_port);
    hw_agent.hw_monitor.out_data_port.connect(hw_sb.out_hw_imp_port);	
	

   
  endfunction
  
  
endclass