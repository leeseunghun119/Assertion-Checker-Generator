class tb_c extends uvm_env;
  `uvm_component_utils(tb_c)
  
  vseqr_c		vseqr;
  hw_env_c	hw_env;
  
    // APB
  my_reg_block 	m_reg_block;
  apb_sequencer apb_seqr;
  apb_adapter	apb_adapter1;
  apb_driver 	apb_driver1;
  

  function new(string name, uvm_component parent);
	super.new(name, parent);
  endfunction    
  
  function void build_phase(uvm_phase phase);
	super.build_phase(phase);
    `uvm_info(get_full_name(), $sformatf("build_phase() starts.."), UVM_LOW)
    
    vseqr = vseqr_c::type_id::create("vseqr", this);
    hw_env = hw_env_c::type_id::create("hw_env", this);
    
     // apb
    m_reg_block		= my_reg_block::type_id::create("m_reg_block", this);
    m_reg_block.build();
    apb_seqr		= apb_sequencer::type_id::create("apb_seqr", this);
    apb_adapter1 	= apb_adapter::type_id::create("apb_adapter1",,get_full_name);
    apb_driver1	 	= apb_driver::type_id::create("apb_driver1", this);    
    
  endfunction
  
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    
    `uvm_info(get_type_name(), $sformatf("connect_phase() starts.."), UVM_LOW)
    if(!$cast(vseqr.hw_seqr, hw_env.hw_agent.hw_sequencer)) begin
      `uvm_error(get_type_name(), "vseqr.hw_seqr is incompatible type.");
    end
    
     // apb
    m_reg_block.default_map.set_sequencer( .sequencer(apb_seqr), .adapter(apb_adapter1));
    m_reg_block.default_map.set_auto_predict(1);
    m_reg_block.default_map.set_base_addr(0);
    m_reg_block.add_hdl_path("tb.DUT.SFR");
   // hw_agent.hw_sequencer.my_reg_block1 = m_reg_block;
       
    vseqr.apb_seqr = apb_seqr; 
    vseqr.m_reg_block = m_reg_block;
    apb_driver1.seq_item_port.connect( apb_seqr.seq_item_export );
    
    `uvm_info(get_type_name(), $sformatf("connect_phase() ends.."), UVM_LOW)
  endfunction
  
  
  
endclass