module apb_sfr_ctrl(
  input 				PRSTN,
  input 				PCLK,
  input 				i_PSEL,
  input 				i_PEN,
  input 				i_PWRITE,
  input 		[31:0] 	i_PADDR,
  input 		[31:0] 	i_PWDATA,
  output reg 	[31:0] 	o_PRDATA,
  
  output reg 			o_weight_wr_mode,
  output reg 			o_mirror_mode,
  output reg 			o_blur_mode,
  
  output reg 	[3:0]   o_w1,
  output reg 	[3:0] 	o_w2,
  output reg 	[3:0]   o_w3, 
 
  output reg 	[3:0]   o_w4,
  output reg 	[3:0] 	o_w5,
  output reg 	[3:0]   o_w6, 
  
  output reg 	[3:0]   o_w7,
  output reg 	[3:0] 	o_w8,
  output reg 	[3:0]   o_w9,
  
  
  
  output reg		[15:0]	o_vsw,
  output reg		[15:0]	o_vbp,  
  output reg		[15:0]	o_vact,   
  output reg		[15:0]	o_vfp,
  output reg		[15:0]	o_hsw,
  output reg		[15:0]	o_hbp,   
  output reg		[15:0]	o_hact,    
  output reg		[15:0]	o_hfp
  

  
  

);
  
  wire APB_write 	= i_PSEL & i_PEN & i_PWRITE;
  wire APB_read 	= i_PSEL & i_PEN & ~i_PWRITE;
  
  // SFR
  reg [31:0] my_reg1; 	// offset : 0x00
  reg [31:0] my_reg2;	// offset : 0x04
  reg [31:0] my_reg3; 	// offset : 0x08
  reg [31:0] my_reg4;	// offset : 0x0c  
  reg [31:0] my_reg5; 	// offset : 0x10
  reg [31:0] my_reg6;	// offset : 0x14 
  reg [31:0] my_reg7; 	// offset : 0x18
  reg [31:0] my_reg8;	// offset : 0x1c 
 // reg [31:0] my_reg9;	// offset : 0x20   
  
  
  
  // assign Field
  assign o_vsw  = my_reg1[31:16];
  assign o_hsw  = my_reg1[15:0];  
  assign o_vbp  = my_reg2[31:16];
  assign o_hbp  = my_reg2[15:0];
  assign o_vact = my_reg3[31:16];
  assign o_hact = my_reg3[15:0];
  assign o_vfp  = my_reg4[31:16];  
  assign o_hfp  = my_reg4[15:0];
  assign o_weight_wr_mode 	= my_reg5[8];
  assign o_mirror_mode 		= my_reg5[4];
  assign o_blur_mode 		= my_reg5[0];
  assign o_w1 		= my_reg6[19:16];  
  assign o_w2 		= my_reg6[11:8];  
  assign o_w3 		= my_reg6[3:0];    
  assign o_w4 		= my_reg7[19:16];  
  assign o_w5		= my_reg7[11:8];  
  assign o_w6 		= my_reg7[3:0]; 
  assign o_w7 		= my_reg8[19:16];  
  assign o_w8		= my_reg8[11:8];  
  assign o_w9 		= my_reg8[3:0];   
  


  // WRITE
  always @(posedge PCLK or negedge PRSTN) begin
    if(!PRSTN) begin
      my_reg1 <= 0;
      my_reg2 <= 0;
      my_reg3 <= 0;
      my_reg4 <= 0;
      my_reg5 <= 0;
      my_reg6 <= 0;
      my_reg7 <= 0;
      my_reg8 <= 0;
    //  my_reg9 <= 0;
     
    end
    else begin
      if(APB_write) begin
        case(i_PADDR)
          'h0 : my_reg1 <= i_PWDATA;
          'h4 : my_reg2 <= i_PWDATA;
          'h8 : my_reg3 <= i_PWDATA;
          'hc : my_reg4 <= i_PWDATA;
          'h10 : my_reg5 <= i_PWDATA;
          'h14 : my_reg6 <= i_PWDATA;          
          'h18 : my_reg7 <= i_PWDATA;
          'h1c : my_reg8 <= i_PWDATA;          
        //  'h20 : my_reg9 <= i_PWDATA;
        endcase
      end
    end
  end
  
  // READ
  always @(*) begin
    if(!PRSTN) begin
      o_PRDATA 	= 32'b0;
    end
    else if(APB_read) begin
      case(i_PADDR)
        'h0 : o_PRDATA = my_reg1;
        'h4 : o_PRDATA = my_reg2;
        'h8 : o_PRDATA = my_reg3;
        'hc : o_PRDATA = my_reg4;        
        'h10 : o_PRDATA = my_reg5;
        'h14 : o_PRDATA = my_reg6;        
        'h18 : o_PRDATA = my_reg7;
        'h1c : o_PRDATA = my_reg8;        
     //   'h20 : o_PRDATA = my_reg9;              
      endcase
    end
  end
  
endmodule