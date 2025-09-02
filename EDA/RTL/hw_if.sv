interface hw_if(input CLK, input RSTN);
  
    bit	I_VSYNC;
    bit I_HSYNC;
    bit I_DEN;
  
  	logic [7:0]	 I_DATA;
  	logic [7:0]  O_DATA;
  
  	bit O_VSYNC;  
  	bit O_HSYNC;  
  	bit O_DEN;  
  
endinterface