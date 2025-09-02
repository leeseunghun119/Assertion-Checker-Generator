module mux_sram_read #(parameter DATA_WIDTH = 8)
(
  	input							I_CLK,
	input 							I_RSTN,
  	input [ 3:0]					i_sel,
  
  	input [DATA_WIDTH-1:0]			i_read_din1,  
  	input [DATA_WIDTH-1:0]			i_read_din2,  
  	input [DATA_WIDTH-1:0]			i_read_din3,  
  	input [DATA_WIDTH-1:0]			i_read_din4,    
    
  	output [DATA_WIDTH-1:0]			o_read_dout1,
  	output [DATA_WIDTH-1:0]			o_read_dout2,
  	output [DATA_WIDTH-1:0]			o_read_dout3
);
  
  	wire		w_hex_e;
    wire		w_hex_d;
    wire		w_hex_b;
    wire		w_hex_7;
    wire		w_hex_6;
    wire		w_hex_c;
    wire		w_hex_9;
    wire		w_hex_3;
  
  	reg	[ 3:0]	r_sel_dly;
  
	// select_signal_delay
  
  	always @(posedge I_CLK or negedge I_RSTN) begin
      	if	(!I_RSTN) r_sel_dly <= 'b0;
    	else		  r_sel_dly <= i_sel;    
  	end  
  
  	// enable signal
  
  	assign w_hex_e = 	r_sel_dly[3] &&	 r_sel_dly[2]	&&  r_sel_dly[1]	&&	!r_sel_dly[0];
  	assign w_hex_d = 	r_sel_dly[3] &&	 r_sel_dly[2]	&& !r_sel_dly[1]	&&	 r_sel_dly[0];
  	assign w_hex_b = 	r_sel_dly[3] &&	!r_sel_dly[2]	&&  r_sel_dly[1]	&&	 r_sel_dly[0];
  	assign w_hex_7 =   !r_sel_dly[3] &&  r_sel_dly[2]	&&  r_sel_dly[1]	&&	 r_sel_dly[0];
  	assign w_hex_6 =   !r_sel_dly[3] &&  r_sel_dly[2]	&&  r_sel_dly[1]	&&	!r_sel_dly[0];
  	assign w_hex_c = 	r_sel_dly[3] &&	 r_sel_dly[2]	&& !r_sel_dly[1]	&&	!r_sel_dly[0];
  	assign w_hex_9 = 	r_sel_dly[3] &&	!r_sel_dly[2]	&& !r_sel_dly[1]	&&	 r_sel_dly[0];
  	assign w_hex_3 =   !r_sel_dly[3] && !r_sel_dly[2]	&&  r_sel_dly[1]	&&	 r_sel_dly[0];
  
  	// select data
  
  	assign o_read_dout1 = (w_hex_e) ? i_read_din2 :
      					  (w_hex_d) ? i_read_din3 :
                          (w_hex_b) ? i_read_din4 :
    					  (w_hex_7) ? i_read_din1 :
    					  (w_hex_6) ? i_read_din2 :
    					  (w_hex_c) ? i_read_din3 :
                          (w_hex_9) ? i_read_din4 :
    					  (w_hex_3) ? i_read_din1 :	'h0;
   	
  	assign o_read_dout2 = (w_hex_e) ? i_read_din3 :
      					  (w_hex_d) ? i_read_din4 :
      					  (w_hex_b) ? i_read_din1 :
    					  (w_hex_7) ? i_read_din2 :
    					  (w_hex_6) ? i_read_din3 :
    					  (w_hex_c) ? i_read_din4 :
      					  (w_hex_9) ? i_read_din1 :
    					  (w_hex_3) ? i_read_din2 :	'h0; 
  
  assign o_read_dout3 = (w_hex_e) ? i_read_din4 :
    					(w_hex_d) ? i_read_din1 :
    					(w_hex_b) ? i_read_din2 :
    					(w_hex_7) ? i_read_din3 : 'h0;
  
endmodule