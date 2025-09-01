class apb_driver extends uvm_driver #(apb_item);
  
  `uvm_component_utils(apb_driver)
  
  // Interface
  virtual interface apb_if apb_if;
  
  // Constructor
  function new(string name="apb_driver", uvm_component parent);
    super.new(name, parent);
  endfunction
  
  // Build Phase
  function void build_phase(uvm_phase phase);
    if( !uvm_config_db #(virtual apb_if)::get(this, "", "apb_if", apb_if) )
      `uvm_error("", "uvm_config_db::get failed")
  endfunction
  
  // Run Phase
  task run_phase(uvm_phase phase);
    
    apb_if.i_PSEL 	= 0;
    apb_if.i_PEN 	= 0;
    apb_if.i_PWRITE	= 0;
    apb_if.i_PADDR 	= 0;
    apb_if.i_PWDATA	= 0;
    
    @(posedge apb_if.PRSTN);
    
    forever begin
      @(posedge apb_if.PCLK);
      seq_item_port.get_next_item(req);
      
      apb_if.i_PSEL 	= 1;
      apb_if.i_PEN 		= 0;
      apb_if.i_PWRITE	= req.i_PWRITE;
      apb_if.i_PADDR 	= req.i_PADDR;
      apb_if.i_PWDATA 	= req.i_PWDATA;
      
      @(posedge apb_if.PCLK);
      apb_if.i_PEN 		= 1;
      @(posedge apb_if.PCLK);
      apb_if.i_PSEL 	= 0;
      apb_if.i_PEN 		= 0;
      req.o_PRDATA 		= apb_if.o_PRDATA;
      
      seq_item_port.item_done();
    end
  endtask
      
endclass