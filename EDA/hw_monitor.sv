class hw_monitor_c extends uvm_monitor;
  `uvm_component_utils(hw_monitor_c)

  uvm_analysis_port#(hw_mon_pkt_c) in_data_port; // TLM port broadcast mode
  uvm_analysis_port#(hw_mon_pkt_c) out_data_port; // TLM port broadcast mode
  
  virtual interface hw_if 	vif;
  hw_mon_pkt_c 				pkt;
  
  function new(string name, uvm_component parent);
	super.new(name, parent);
    
    in_data_port = new("in_data_port", this);
    out_data_port = new("out_data_port", this);
  endfunction
 
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
	 `uvm_info(get_type_name(), $sformatf("build_phase() starts.."), UVM_LOW)
    
    if (!uvm_config_db#(virtual hw_if)::get(this, "", "vif", vif)) begin
      `uvm_fatal(get_type_name(), {"virtual interface must be set for: ", get_full_name(), ".vif"})          
    end
    
    
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    pkt = hw_mon_pkt_c::type_id::create("pkt");
	
    //@(posedge vif.RSTN);
    forever begin
      @(posedge vif.CLK);
      in_data();
      out_data();
    end
    
  endtask
    
    task in_data();
      pkt.I_VSYNC = vif.I_VSYNC ;
      pkt.I_HSYNC = vif.I_HSYNC ;
      pkt.I_DEN   = vif.I_DEN ;
      pkt.I_DATA  = vif.I_DATA;
      
      in_data_port.write(pkt);
    endtask :in_data
    
    task out_data();
      pkt.O_VSYNC = vif.O_VSYNC ;
      pkt.O_HSYNC = vif.O_HSYNC ;
      pkt.O_DEN   = vif.O_DEN ;
      pkt.O_DATA  = vif.O_DATA ;
      
      out_data_port.write(pkt);
    endtask :out_data
  

endclass