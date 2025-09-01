class hw_agent_c extends uvm_agent;
  `uvm_component_utils(hw_agent_c)

  //protected uvm_active_passive_enum is_active = UVM_ACTIVE;
  uvm_active_passive_enum is_active = UVM_ACTIVE;  
  
  hw_sequencer_c	hw_sequencer;
  hw_driver_c		hw_driver;
  hw_monitor_c	hw_monitor;

  
  function new(string name, uvm_component parent);
	super.new(name, parent);
  endfunction
 
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info(get_type_name(), $sformatf("build_phase() starts.."), UVM_LOW)
    if (is_active == UVM_ACTIVE) begin
      `uvm_info(get_type_name(), $sformatf("is_active = UVM_ACTIVE"), UVM_LOW)
      hw_sequencer = hw_sequencer_c::type_id::create("hw_sequencer", this);
      hw_driver = hw_driver_c::type_id::create("hw_driver", this);      
    end
    hw_monitor = hw_monitor_c::type_id::create("hw_monitor", this);
    
  endfunction
  
  function void connect_phase (uvm_phase phase);
    super.connect_phase(phase);
    
    if (is_active == UVM_ACTIVE) begin
      hw_driver.seq_item_port.connect(hw_sequencer.seq_item_export);
    end
  endfunction      
      
      

endclass