module LINE_CTRL
(
	input clk,								//clock 
	input resetn,							//active low reset
	input i_vsync, 							//input vsync
	input i_hsync,							//input hsync
	input i_de,								//input de
	input [5:0] i_VSW,i_VBP,i_VACT,i_VFP,	//vsync porch value parameter input
	input [5:0] i_HSW,i_HBP,i_HACT,i_HFP,	//hsync porch value parameter inpu
	input [9:0] i_r,i_g,i_b,				//input rgb data
	output o_cs1, o_cs2,					//sram control signal CHIP SELECT
	output o_we1, o_we2,   					//sram control signal WRITE Enable
	output [5:0] o_addr1,					//SRAM1 control signal address
	output [5:0] o_addr2,					//SRAM2 control signal address
	output [29:0] o_rgb,					//data output - just concetenate
  	output o_mem_sel,					//mux control signal
 	output o_vsync,							//output vsync - just bypass
  	output o_hsync,							//output hsync - just bypass
  	output o_de,							//output de    - just bypass
  	output [8:0] o_hsync_cnt,					//pixel counter
  	output [8:0] o_vsync_cnt,
  	output o_hsync_edge,
    output [8:0] o_VTOT,
    output [8:0] o_V_ACTIVE_TH,
    output [8:0] o_V_WAIT_TH,
    output [8:0] o_H_ACTIVE_TH,
    output [8:0] o_H_WAIT_TH
);
  
  
reg [3:0] c_state, n_state;					//state divide reg
reg selector;								//selector is made for distinguish odd even case
reg i_de;									//i_de input i_de
reg o_mem_sel;						//for mux sel
reg [8:0] hsync_cnt;						//hsync_cnt is for last state -> idle
reg [8:0] vsync_cnt;
reg [5:0] addr_cnt;						//adrr_cnt is for addr data send
reg hsync_cnt_en;
reg addr_cnt_en;							//addr_cnt control
reg de_d;									//de 1 clk delay signal for edge detect
reg hsync_d;								//hsync 1 clk delay signal
reg vsync_d;  
reg [9:0] i_r, i_g, i_b;					//input data
reg [9:0] i_r_d, i_g_d, i_b_d;				//1 clk delay input data


reg o_cs1_temp,o_cs2_temp;					//result reg
reg o_we1_temp,o_we2_temp;
reg [5:0] o_addr1_temp;
reg [5:0] o_addr2_temp;
reg [29:0] o_rgb_temp;
reg o_cs1,o_cs2;							//output reg
reg o_we1,o_we2;
reg [5:0] o_addr1;
reg [5:0] o_addr2;
reg [29:0] o_rgb;
 

  
wire vsync_edge;							//vsync edge pulse 1clk start edge
wire de_edge;								//de edge pulse 1clk start edge
wire hsync_edge;							//hsync edge pulse 1clk start edge
assign de_edge = i_de & ~de_d;				//start signal generate
assign hsync_edge = i_hsync & ~hsync_d;		//start signal generate
assign vsync_edge = i_vsync & ~vsync_d;
  
  
  
wire [8:0] HTOT;
wire [8:0] HBLK;
wire [8:0] H_ACTIVE_TH;
wire [8:0] H_WAIT_TH;
wire [8:0] VTOT;
wire [8:0] V_ACTIVE_TH;
wire [8:0] V_WAIT_TH;
assign HTOT = i_HSW + i_HBP + i_HACT + i_HFP;
assign HBLK =  i_HSW + i_HBP + i_HFP;
assign H_ACTIVE_TH = i_HSW + i_HBP + i_HACT; 
assign H_WAIT_TH = i_HSW + i_HBP;
assign VTOT = i_VSW + i_VBP + i_VACT + i_VFP;
assign V_ACTIVE_TH = i_VSW + i_VBP + i_VACT;
assign V_WAIT_TH = i_VSW + i_VBP;
  
assign o_hsync_cnt = hsync_cnt;					//pixel counter
assign o_vsync_cnt = vsync_cnt;
assign o_hsync_edge = hsync_edge;
assign o_VTOT = VTOT;
assign o_V_ACTIVE_TH = V_ACTIVE_TH;
assign o_V_WAIT_TH = V_WAIT_TH;
assign o_H_ACTIVE_TH = H_ACTIVE_TH;
assign o_H_WAIT_TH = H_WAIT_TH;

assign o_vsync = i_vsync;					//bypass   to out_sync_gen
assign o_hsync = i_hsync;					//bypass   to out_sync_gen
assign o_de = i_de;							//bypass   to out_sync_gen
  
/////////////////////////////////////////////
////////        localparam            ///////
/////////////////////////////////////////////
localparam IDLE_ST = 3'd0;
localparam FIRST_ST = 3'd1;
localparam WAIT_ST = 3'd2;
localparam EVEN_ST = 3'd3;
localparam ODD_ST = 3'd4;
localparam LAST_ST = 3'd5;
  
  
  
///////////////////////////////////////////////
//////    vsync 1 clk delay                ////
///////////////////////////////////////////////
always @(posedge clk, negedge resetn) begin
  if(!resetn) begin
  	vsync_d <= 0; 
  end
  
  else begin
  	vsync_d <= i_vsync; 
  end
end
  
///////////////////////////////////////////////
//////    hsync enable gen                 ////
///////////////////////////////////////////////
  
always @(posedge clk, negedge resetn) begin
	if(!resetn) begin
    	hsync_cnt_en <= 0; 
  	end
  	else if(vsync_edge && hsync_edge) begin
      	hsync_cnt_en <= 1;
  	end
  	else if(vsync_cnt > VTOT + 1) begin
    	hsync_cnt_en <= 0;
  	end
end
  
  
  
///////////////////////////////////////////////
////  vsync_cnt2 : counter per hsync       ////
///////////////////////////////////////////////
  
always @(posedge clk, negedge resetn) begin
    if(!resetn) begin
      	vsync_cnt <= 0;
    end
  	else if(vsync_edge) begin
    	vsync_cnt <= 1;
  	end
    else if(hsync_edge) begin
     	vsync_cnt <= vsync_cnt +1;
  	end
  	else if(hsync_cnt == HTOT) begin
  		vsync_cnt <= vsync_cnt + 1;
  	end
  	
end
  

///////////////////////////////////////////////
////  1-clk delay hsync                    ////
///////////////////////////////////////////////
  
always @(posedge clk, negedge resetn) begin
	if(!resetn) begin
		hsync_d <= 0;
	end
	else begin
		hsync_d <= i_hsync;
	end
end  
////////////////////////////////////////////
///////// de 1clk delay for start edge   ///
////////////////////////////////////////////
always @(posedge clk, negedge resetn) begin
	if(!resetn) begin
		de_d <= 0;
	end
	else begin
		de_d <= i_de;   
	end
end
///////////////////////////////////////////
/////// DATA DELAY                      ///
///////////////////////////////////////////
always @(posedge clk, negedge resetn) begin
	if(!resetn) begin
		i_r_d <= 0;
		i_g_d <= 0;
		i_b_d <= 0;
	end
	else begin
		i_r_d <= i_r;
		i_g_d <= i_g;
		i_b_d <= i_b;
	end
end

///////////////////////////////////////////
///  address counter 1 & 2              ///
/////////////////////////////////////////// 
always @(posedge clk, negedge resetn) begin
	if(!resetn) begin
		addr_cnt <= 0;
	end
	else if(addr_cnt_en) begin
		addr_cnt <= addr_cnt +1;
	end
	else begin
		addr_cnt <= 0;
	end
end

///////////////////////////////////////////
///             hsync_cnt               ///
///////////////////////////////////////////
always @(posedge clk, negedge resetn) begin
	if(!resetn) begin
			hsync_cnt <= 1;
	end
  	else if(!hsync_cnt_en) begin
    		hsync_cnt <= 1;
  	end
  	else if(hsync_edge) begin
			hsync_cnt <= 1;
	end
  	else if(hsync_cnt == HTOT) begin
  		hsync_cnt <= 1;
    end
  	else begin
      	hsync_cnt <= hsync_cnt + 1;
    end
    
end
  


///////////////////////////////////////////
///             selector                ///
///////////////////////////////////////////
always @(posedge clk, negedge resetn) begin
	if(!resetn) begin
			selector <= 0;  
	end
	else if(de_edge) begin
		selector <= ~selector;
	end
	else begin
		selector <= selector;
	end
end



///////////////////////////////////////////
///             fsm                     ///
///////////////////////////////////////////
always@(posedge clk, negedge resetn) begin
	if(!resetn) begin
		c_state <= IDLE_ST;
		n_state <= IDLE_ST;
	end
	else begin
		c_state <= n_state;
	end
end

always @(*) begin
	case(c_state)
		IDLE_ST:begin
					if(i_de==1) begin
						n_state = FIRST_ST;
					end
					else begin
						n_state = IDLE_ST;
					end
				end
		FIRST_ST:begin
          			if(hsync_cnt == H_ACTIVE_TH) begin 
						n_state = WAIT_ST;
					end  
					else begin
						n_state = FIRST_ST;
					end
				end
		WAIT_ST:begin
          			if(i_de == 1 && (hsync_cnt == H_WAIT_TH) && selector ==1) begin
						n_state = EVEN_ST;
					end
          			else if(i_de == 1 && (hsync_cnt == H_WAIT_TH) && selector ==0) begin
						n_state = ODD_ST;
					end
         			 else if((hsync_cnt == H_WAIT_TH)&& i_de == 0)begin
						n_state = LAST_ST;
					end
					else begin
						n_state = WAIT_ST;
					end
				end
		EVEN_ST:begin
          			if(hsync_cnt == H_ACTIVE_TH) begin 
						n_state = WAIT_ST;
					end   
					else begin
						n_state = EVEN_ST;
					end
				end
		ODD_ST:begin
          			if(hsync_cnt == H_ACTIVE_TH) begin 
						n_state = WAIT_ST;
					end   
					else begin
						n_state = ODD_ST;
					end
				end
		LAST_ST:begin
          			if(hsync_cnt == H_ACTIVE_TH) begin
						n_state = IDLE_ST;
					end   
					else begin
						n_state = LAST_ST;
					end
				end
		default:c_state = IDLE_ST;
	endcase
end


always @(*) begin
	case(c_state)
		IDLE_ST:begin
					addr_cnt_en = 0;
					o_addr1_temp = addr_cnt;
					o_addr2_temp = addr_cnt;
					selector = 0;
					o_cs1_temp = 1'b0;
					o_we1_temp = 1'b0;
					o_cs2_temp = 1'b0;
					o_we2_temp = 1'b0;
					o_rgb_temp = 30'b0;
				end

		FIRST_ST:begin
					addr_cnt_en = 1;
					o_cs1_temp = 1'b1;
					o_we1_temp = 1'b1;
					o_cs2_temp = 1'b0;
					o_we2_temp = 1'b0;
					o_addr1_temp = addr_cnt;
					o_rgb_temp = {i_r_d, i_g_d, i_b_d};
					o_mem_sel = 1'b0;
				end

		WAIT_ST:begin
					addr_cnt_en = 0;
					o_addr1_temp = addr_cnt;
					o_addr2_temp = addr_cnt;
					o_cs1_temp = 1'b0;
					o_we1_temp = 1'b0;
					o_cs2_temp = 1'b0;
					o_we2_temp = 1'b0;
					o_rgb_temp = 30'b0;
				end

		EVEN_ST:begin
					addr_cnt_en = 1;
					o_cs1_temp = 1'b1;
					o_we1_temp = 1'b0;
					o_cs2_temp = 1'b1;
					o_we2_temp = 1'b1;
					o_addr1_temp = addr_cnt;
					o_addr2_temp = addr_cnt;
					o_rgb_temp = {i_r_d, i_g_d, i_b_d};
					o_mem_sel = 1'b0;
				end 

		ODD_ST:begin
					addr_cnt_en = 1;
					o_cs1_temp = 1'b1;
					o_we1_temp = 1'b1;
					o_cs2_temp = 1'b1;
					o_we2_temp = 1'b0;
					o_addr1_temp = addr_cnt;
					o_addr2_temp = addr_cnt;
					o_rgb_temp = {i_r_d, i_g_d, i_b_d};
					o_mem_sel = 1'b1;
				end

		LAST_ST:begin
					if(selector) begin
						addr_cnt_en = 1;
						o_cs1_temp = 1'b1;
						o_we1_temp = 1'b0;
						o_cs2_temp = 1'b0;
						o_we2_temp = 1'b0;
						o_addr1_temp = addr_cnt;
						o_mem_sel = 1'b0;
					end
					else begin
						addr_cnt_en = 1;
						o_cs1_temp = 1'b0;
						o_we1_temp = 1'b0;
						o_cs2_temp = 1'b1;
						o_we2_temp = 1'b0;
						o_addr2_temp = addr_cnt;
						o_mem_sel = 1'b1;
					end
				end
	endcase

end


always @(posedge clk, negedge resetn) begin
	if(!resetn) begin
		o_cs1_temp <= 0;
		o_cs2_temp <= 0;
		o_we1_temp <= 0;
		o_we2_temp <= 0;
		o_addr1_temp <= 0;
		o_addr2_temp <= 0;
		o_rgb_temp <= 0;
	end
	else begin
		o_cs1 <= o_cs1_temp;
		o_cs2 <= o_cs2_temp;
		o_we1 <= o_we1_temp;
		o_we2 <= o_we2_temp;
      	o_addr1 <= o_addr1_temp;
      	o_addr2 <= o_addr2_temp;
      	o_rgb <= o_rgb_temp;

	end
end

 
endmodule