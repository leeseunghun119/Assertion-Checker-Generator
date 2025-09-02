class hw_driver_c extends uvm_driver#(hw_drv_pkt_c);
  `uvm_component_utils(hw_driver_c)
  
  virtual interface hw_if	 vif;
  
  function new(string name, uvm_component parent);
	super.new(name, parent);
  endfunction
 
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
     `uvm_info(get_type_name(), $sformatf("build_phase() starts.."), UVM_LOW)
    
    //Get interface from uvm_config_db
    if (!uvm_config_db#(virtual hw_if)::get(this, "", "vif", vif)) begin
      `uvm_fatal(get_type_name(), {"virtual interface must be set for: ", get_full_name(), ".vif"})
    end
  endfunction
    
    
  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    `uvm_info(get_type_name(), $sformatf("run_phase() starts.."), UVM_LOW)
    
    reset_signals();
    forever begin
      fork
        begin
          reset_signals();
        end
        begin
          drive_signals();
        end
      join_any
      disable fork;
      
      drive_signals();
    end
  endtask
  
  virtual task reset_signals();
    @(negedge vif.RSTN);
    vif.I_VSYNC 	= 'h0;
    vif.I_HSYNC 	= 'h0;
    vif.I_DEN 		= 'h0;
    vif.I_DATA  	= 'h0;
  endtask
    
  virtual task drive_signals();
    //`uvm_info(get_type_name(), $sformatf("drive interface signals."), UVM_LOW)
    seq_item_port.get_next_item(req);
    @(posedge vif.CLK);
    vif.I_VSYNC 	= req.I_VSYNC;
    vif.I_HSYNC 	= req.I_HSYNC;
    vif.I_DEN 		= req.I_DEN;
    vif.I_DATA	 	= req.I_DATA;

    seq_item_port.item_done();
  endtask
      
endclass