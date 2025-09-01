module out_sync_gen
(
	input clk,
	input i_resetn,
	input i_vsync,								// from line ctrl block
	input i_hsync,								
	input i_de,
	input [5:0] i_hsw,		//from top module
	input [5:0] i_vsw,
  	input i_hsync_cnt,
  	input i_hsync_edge,
  	input i_vsync_cnt,
  	input i_VTOT,
  	input i_V_ACTIVE_TH,
  	input i_V_WAIT_TH,
  	input i_H_ACTIVE_TH,
  	input i_H_WAIT_TH,
	output o_vsync_final,
	output o_hsync_final,
	output o_de_final
  	
);
reg [8:0] i_hsync_cnt; 							//hsync counter per clk
reg [8:0] i_vsync_cnt; 							//hsync counter per line
reg hsync_temp;									//result 1 line buffer hsync
reg vsync_temp;									//result 1 line buffer vsync
reg de_temp;									//result 1 line buffer de
reg i_hsync_edge;  								//hsync edge pulse 1 clk


  
reg [8:0] i_VTOT;
reg [8:0] i_V_ACTIVE_TH;
reg [8:0] i_H_ACTIVE_TH;
reg [8:0] i_H_WAIT_TH;
reg [8:0] i_V_WAIT_TH;
  
  
///////////////////////////////////////////////
//// 1-line buffer  hsync generate		    ///
///////////////////////////////////////////////
  
always @(posedge clk, negedge i_resetn) begin
	if(!i_resetn) begin
		hsync_temp <= 0; 
	end
  	else if((i_hsync_cnt <= i_hsw )&&(i_vsync_cnt>1)&&(i_vsync_cnt <= i_VTOT+1 )) begin
		hsync_temp <= 1;
	end
	else begin
		hsync_temp <= 0;
	end
end


  
///////////////////////////////////////////////
////  1-line buffer vsync                  ////
///////////////////////////////////////////////
always @(posedge clk, negedge i_resetn) begin
	if(!i_resetn) begin
		vsync_temp <= 0;
	end
  	else if((i_vsync_cnt > 1) && (i_vsync_cnt <= i_vsw + 1)) begin
		vsync_temp <= 1;
	end
	else begin
		vsync_temp <= 0;
	end
end
/////////////////////////////////////////////////////////////////////////////////////////////////////////
////  1-line buffer de : vsync_cnt for 1 line delay de, hsync_cnt for vsync & hsync active range de==1//
/////////////////////////////////////////////////////////////////////////////////////////////////////////
always @(posedge clk, negedge i_resetn) begin
	if(!i_resetn) begin
		de_temp <= 0;
	end
  	else if((i_hsync_cnt <= i_H_ACTIVE_TH)&&(i_hsync_cnt > i_H_WAIT_TH) && (i_vsync_cnt > i_V_WAIT_TH + 1) && (i_vsync_cnt <= i_V_ACTIVE_TH + 1)) begin 
		de_temp <= 1;
	end
	else begin
		de_temp <= 0;
	end
end

  
assign o_hsync_final = hsync_temp;		//result -> output
assign o_vsync_final = vsync_temp;
assign o_de_final = de_temp;  


endmodule