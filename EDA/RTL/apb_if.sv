interface apb_if(input logic PCLK, input logic PRSTN);
 
  // Input
  logic				i_PSEL;
  logic				i_PEN;
  logic				i_PWRITE;
  logic		[31:0] 	i_PADDR;
  logic		[31:0] 	i_PWDATA;
  
  // output
  logic 	[31:0] 	o_PRDATA;
  
endinterface