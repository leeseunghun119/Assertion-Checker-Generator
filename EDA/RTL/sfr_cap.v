module sfr_cap #(parameter PARAM_WIDTH =16, WEIGHT_WIDTH = 4)
(
  	input								I_CLK,
	input 								I_RSTN,  
  	input								i_vsync_sync,
  	input								i_weight_wr_mode,
    input								i_mirror_mode,
    input								i_blur_mode,
  
  	input [WEIGHT_WIDTH-1:0]			i_w1,
  	input [WEIGHT_WIDTH-1:0]			i_w2,
  	input [WEIGHT_WIDTH-1:0]			i_w3,
  	input [WEIGHT_WIDTH-1:0]			i_w4,
  	input [WEIGHT_WIDTH-1:0]			i_w5,
  	input [WEIGHT_WIDTH-1:0]			i_w6,
  	input [WEIGHT_WIDTH-1:0]			i_w7,
  	input [WEIGHT_WIDTH-1:0]			i_w8,
  	input [WEIGHT_WIDTH-1:0]			i_w9,  
  	input [PARAM_WIDTH-1:0]				i_hsw,
  	input [PARAM_WIDTH-1:0]				i_hact,
  	input [PARAM_WIDTH-1:0]				i_hfp,
  	input [PARAM_WIDTH-1:0]				i_hbp,
  	input [PARAM_WIDTH-1:0]				i_vsw,
  	input [PARAM_WIDTH-1:0]				i_vact,
  	input [PARAM_WIDTH-1:0]				i_vfp,
  	input [PARAM_WIDTH-1:0]				i_vbp,
 
 	output reg							o_weight_wr_mode_cap,
  	output reg							o_mirror_mode_cap,
  	output reg							o_blur_mode_cap,
  	output reg [WEIGHT_WIDTH-1:0]		o_w1_cap,
  	output reg [WEIGHT_WIDTH-1:0]		o_w2_cap,
  	output reg [WEIGHT_WIDTH-1:0]		o_w3_cap,
  	output reg [WEIGHT_WIDTH-1:0]		o_w4_cap,
  	output reg [WEIGHT_WIDTH-1:0]		o_w5_cap,
  	output reg [WEIGHT_WIDTH-1:0]		o_w6_cap,
  	output reg [WEIGHT_WIDTH-1:0]		o_w7_cap,
  	output reg [WEIGHT_WIDTH-1:0]		o_w8_cap,
  	output reg [WEIGHT_WIDTH-1:0]		o_w9_cap,
  	output reg [PARAM_WIDTH-1:0]		o_hsw_cap,
  	output reg [PARAM_WIDTH-1:0]		o_hact_cap,
  	output reg [PARAM_WIDTH-1:0]		o_hfp_cap,
  	output reg [PARAM_WIDTH-1:0]		o_hbp_cap,
  	output reg [PARAM_WIDTH-1:0]		o_vsw_cap,
  	output reg [PARAM_WIDTH-1:0]		o_vact_cap,
  	output reg [PARAM_WIDTH-1:0]		o_vfp_cap,
  	output reg [PARAM_WIDTH-1:0]		o_vbp_cap,  
  	output reg [PARAM_WIDTH-1:0]		o_htotal,  
  	output reg [PARAM_WIDTH-1:0]		o_vtotal    
  
);

  	wire [PARAM_WIDTH-1:0]		w_htotal;
  	wire [PARAM_WIDTH-1:0]		w_vtotal;
  	wire 						w_vsync_edge;
  
  	reg							r_vsync_dly;
  
  	// edge detector
  
  	always @(posedge I_CLK or negedge I_RSTN) begin
      	if	(!I_RSTN) r_vsync_dly <= 'b0;
    	else		  r_vsync_dly <= i_vsync_sync;    
  	end 
  
  	assign	w_vsync_edge	= i_vsync_sync && !r_vsync_dly;
  
  
  	// capture
  	always @(posedge I_CLK or negedge I_RSTN) begin
      	if (!I_RSTN) begin
          	o_weight_wr_mode_cap <= 'd0;
            o_mirror_mode_cap	 <= 'd0;
            o_blur_mode_cap	 	 <= 'd0;
            o_w1_cap			 <= 'd0;
            o_w2_cap			 <= 'd0;
            o_w3_cap			 <= 'd0;
            o_w4_cap			 <= 'd0;
            o_w5_cap			 <= 'd0;
            o_w6_cap			 <= 'd0;
            o_w7_cap			 <= 'd0;
            o_w8_cap			 <= 'd0;
            o_w9_cap			 <= 'd0;
            o_hsw_cap			 <= 'd0;   
            o_hact_cap			 <= 'd0;     
            o_hfp_cap			 <= 'd0;     
            o_hbp_cap			 <= 'd0;     
            o_vsw_cap			 <= 'd0;     
            o_vact_cap			 <= 'd0;     
            o_vfp_cap			 <= 'd0;     
            o_vbp_cap			 <= 'd0;     
            o_htotal			 <= 'd0;     
            o_vtotal			 <= 'd0; 
      	end  
      	else if(w_vsync_edge)begin
          	o_weight_wr_mode_cap <= i_weight_wr_mode;
            o_mirror_mode_cap	 <= i_mirror_mode;
            o_blur_mode_cap		 <= i_blur_mode;
            o_w1_cap			 <= i_w1;
            o_w2_cap			 <= i_w2;
            o_w3_cap			 <= i_w3;
            o_w4_cap			 <= i_w4;
            o_w5_cap			 <= i_w5;
            o_w6_cap			 <= i_w6;
            o_w7_cap			 <= i_w7;
            o_w8_cap			 <= i_w8;
            o_w9_cap			 <= i_w9;
            o_hsw_cap			 <= i_hsw;   
            o_hact_cap			 <= i_hact;     
            o_hfp_cap			 <= i_hfp;     
            o_hbp_cap			 <= i_hbp;     
            o_vsw_cap			 <= i_vsw;     
            o_vact_cap			 <= i_vact;     
            o_vfp_cap			 <= i_vfp;     
            o_vbp_cap			 <= i_vbp;     
            o_htotal			 <= w_htotal;     
            o_vtotal			 <= w_vtotal; 
        end
  	end   
  	
  	assign	w_htotal = i_hsw + i_hbp + i_hact + i_hfp - 'd1;
   	assign	w_vtotal = i_vsw + i_vbp + i_vact + i_vfp - 'd1;
  
endmodule
