class vseqr_c extends uvm_sequencer;


  `uvm_component_utils(vseqr_c)
  

      // reg_block

   // reg block

  
  virtual interface hw_if	  vif;
  virtual interface apb_if 	  apb_if;  

   hw_sequencer_c	hw_seqr;
   apb_sequencer apb_seqr;     
    my_reg_block m_reg_block; 
 
  
  function new(string name, uvm_component parent);
	super.new(name, parent);
  endfunction      

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info(get_type_name(), $sformatf("build_phase() starts.."), UVM_LOW)
    
    //hw_seqr = hw_sequencer_c::type_id::create("hw_seqr", this);



    
  endfunction
  
  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
      
   
    //Get interface from uvm_config_db
    if (!uvm_config_db#(virtual hw_if)::get(this, "", "vif", vif)) begin
      `uvm_fatal(get_type_name(), {"virtual interface must be set for: ", get_full_name(), ".vif"})
    end 
    
     if(!uvm_config_db#(virtual apb_if)::get(this, "", "apb_if", apb_if))
      `uvm_fatal("NO APB_IF", "uvm_config_db::get failed")   
 
  endfunction
    
endclass