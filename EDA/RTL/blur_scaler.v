module blur_scaler #(parameter WEIGHT_WIDTH = 4, PARAM_WIDTH = 11, DATA_WIDTH = 8)
(


  	input							I_CLK,
	input 							I_RSTN,
  	input [PARAM_WIDTH-1:0]			i_vact_state,
  	input [PARAM_WIDTH-1:0]			i_hor_cnt,
  	input							i_vsync,
  	input							i_hsync,
  	input							i_den,
  	input							i_weight_wr_mode_cap,
  	input							i_mirror_mode_cap,
  	input							i_blur_mode_cap,
  	input [WEIGHT_WIDTH-1:0]		i_w1_cap,
  	input [WEIGHT_WIDTH-1:0]		i_w2_cap,
  	input [WEIGHT_WIDTH-1:0]		i_w3_cap,
  	input [WEIGHT_WIDTH-1:0]		i_w4_cap,
  	input [WEIGHT_WIDTH-1:0]		i_w5_cap,
  	input [WEIGHT_WIDTH-1:0]		i_w6_cap,
  	input [WEIGHT_WIDTH-1:0]		i_w7_cap,
  	input [WEIGHT_WIDTH-1:0]		i_w8_cap,
  	input [WEIGHT_WIDTH-1:0]		i_w9_cap,  
  	input [DATA_WIDTH-1:0]			i_sram_rd1,
  	input [DATA_WIDTH-1:0]			i_sram_rd2,    
  	input [DATA_WIDTH-1:0]			i_sram_rd3,      
	output							o_vsync,
  	output							o_hsync,
  	output							o_den,
  	output [DATA_WIDTH-1:0]			o_data
);
  
  	localparam SUM_WIDTH = WEIGHT_WIDTH + DATA_WIDTH;
  
  	wire							w_mirror_blur;
  	wire							w_only_mirror;
  	wire							w_last_hact;
  	wire							w_first_case;
  	wire							w_last_case;
  	wire							w_first_line;
  	wire							w_middle_line;
  	wire							w_last_line;  
  	wire							w_case_1_1;
  	wire							w_case_1_2;
  	wire							w_case_1_3;
  	wire							w_case_2_1;
  	wire							w_case_2_2;
  	wire							w_case_2_3;
  	wire							w_case_3_1;
  	wire							w_case_3_2;
  	wire							w_case_3_3;
  
  	wire [WEIGHT_WIDTH-1:0]			w_weight1;
  	wire [WEIGHT_WIDTH-1:0]			w_weight2;
  	wire [WEIGHT_WIDTH-1:0]			w_weight3;
  	wire [WEIGHT_WIDTH-1:0]			w_weight4;
  	wire [WEIGHT_WIDTH-1:0]			w_weight5;
  	wire [WEIGHT_WIDTH-1:0]			w_weight6;
  	wire [WEIGHT_WIDTH-1:0]			w_weight7;
  	wire [WEIGHT_WIDTH-1:0]			w_weight8;
  	wire [WEIGHT_WIDTH-1:0]			w_weight9;
  
  	wire [DATA_WIDTH-1:0]			w_filter1;    
  	wire [DATA_WIDTH-1:0]			w_filter2;   
  	wire [DATA_WIDTH-1:0]			w_filter3;   
  	wire [DATA_WIDTH-1:0]			w_filter4;   
  	wire [DATA_WIDTH-1:0]			w_filter5;   
  	wire [DATA_WIDTH-1:0]			w_filter6;   
  	wire [DATA_WIDTH-1:0]			w_filter7;   
  	wire [DATA_WIDTH-1:0]			w_filter8;   
  	wire [DATA_WIDTH-1:0]			w_filter9;   
  
  	wire [DATA_WIDTH-1:0]			w_scale_shift; 
  	wire [DATA_WIDTH-1:0]			w_scale_div;   
  
  	reg								r_den_dly;
  	reg [PARAM_WIDTH-1:0]			r_vact_state_dly1;  	
  	reg [PARAM_WIDTH-1:0]			r_vact_state_dly2;
  	reg [PARAM_WIDTH-1:0]			r_vact_state_dly3;
  	reg [PARAM_WIDTH-1:0]			r_hor_cnt_dly;
  
  	reg [WEIGHT_WIDTH*3-1:0]		r_weight_line1;
  	reg [WEIGHT_WIDTH*3-1:0]		r_weight_line2;
  	reg [WEIGHT_WIDTH*3-1:0]		r_weight_line3;  
  	reg [DATA_WIDTH*3-1:0]			r_filter_line1;     
  	reg [DATA_WIDTH*3-1:0]			r_filter_line2;  
  	reg [DATA_WIDTH*3-1:0]			r_filter_line3;    
  
  	reg [SUM_WIDTH-1:0]				r_scale_sum;
  	reg								r_last_case;  
  	reg								r_vsync_final;
   	reg								r_hsync_final; 
   	reg								r_den_final; 
  	reg [7:0]						r_weight_total;
  
  	// input data sync
  
  	always @(posedge I_CLK or negedge I_RSTN) begin
    	if	(!I_RSTN) r_den_dly <= 'b0;
    	else		  r_den_dly <= i_den;    
  	end

  	always @(posedge I_CLK or negedge I_RSTN) begin
      	if	(!I_RSTN) begin
          	r_vact_state_dly1 <= 'h0;
          	r_vact_state_dly2 <= 'h0;
          	r_vact_state_dly3 <= 'h0;        
      	end  
    	else begin
          	r_vact_state_dly1 <= i_vact_state;
            r_vact_state_dly2 <= r_vact_state_dly1;
            r_vact_state_dly3 <= r_vact_state_dly2;
        end
  	end
    
  	always @(posedge I_CLK or negedge I_RSTN) begin
      	if	(!I_RSTN) begin
          	r_hor_cnt_dly <= 'h0;
      	end  
    	else begin
          	r_hor_cnt_dly <= i_hor_cnt;
        end
  	end  
  
  
  	// scaler weight
  	// blur_filter_sel
  
  	always @(posedge I_CLK or negedge I_RSTN) begin
      	if(!I_RSTN) begin
          	r_weight_line1 <= 'h0;
          	r_weight_line2 <= 'h0;
          	r_weight_line3 <= 'h0;          
      	end  
        else if (i_weight_wr_mode_cap) begin
        	r_weight_line1 <= {i_w1_cap, i_w2_cap, i_w3_cap};
        	r_weight_line2 <= {i_w4_cap, i_w5_cap, i_w6_cap};
        	r_weight_line3 <= {i_w7_cap, i_w8_cap, i_w9_cap};
        end
      	else begin
          	if(w_only_mirror) begin
            	r_weight_line1 <= {4'h0, 4'h0, 4'h0};
                r_weight_line2 <= {4'h0, 4'h1, 4'h0};
        		r_weight_line3 <= {4'h0, 4'h0, 4'h0};      
            
            end
          	else begin
              	r_weight_line1 <= {4'h1, 4'h2, 4'h1};
              	r_weight_line2 <= {4'h2, 4'h4, 4'h2};
              	r_weight_line3 <= {4'h1, 4'h2, 4'h1}; 
          	end
        end
  	end    
  
  	assign w_only_mirror = (i_mirror_mode_cap && !i_blur_mode_cap);
  	assign w_weight1 = r_weight_line1[11:8];
  	assign w_weight2 = r_weight_line1[ 7:4];
  	assign w_weight3 = r_weight_line1[ 3:0];
  	assign w_weight4 = r_weight_line2[11:8];
  	assign w_weight5 = r_weight_line2[ 7:4];
  	assign w_weight6 = r_weight_line2[ 3:0];
  	assign w_weight7 = r_weight_line3[11:8];
  	assign w_weight8 = r_weight_line3[ 7:4];
  	assign w_weight9 = r_weight_line3[ 3:0];
  
  	//data input
  
  	always @(posedge I_CLK or negedge I_RSTN) begin
      	if(!I_RSTN) begin
          	r_filter_line1 <= 'h0;
          	r_filter_line2 <= 'h0;
          	r_filter_line3 <= 'h0;          
      	end  
      	else if (r_den_dly) begin
        	r_filter_line1 <= {r_filter_line1[15:0], i_sram_rd1};
        	r_filter_line2 <= {r_filter_line2[15:0], i_sram_rd2};
        	r_filter_line3 <= {r_filter_line3[15:0], i_sram_rd3};
        end
      	else if (w_last_hact) begin
          	r_filter_line1 <= {r_filter_line1[15:0], 8'h0};
        	r_filter_line2 <= {r_filter_line2[15:0], 8'h0};
        	r_filter_line3 <= {r_filter_line3[15:0], 8'h0};
        end            
      	else begin
          	r_filter_line1 <= 'h0;
          	r_filter_line2 <= 'h0;
          	r_filter_line3 <= 'h0; 
        end
  	end    

  	assign w_last_hact = !r_den_dly && !r_hor_cnt_dly && r_vact_state_dly3;
  
  	assign w_filter1 = r_filter_line1[23:16];
  	assign w_filter2 = r_filter_line1[15: 8];
  	assign w_filter3 = r_filter_line1[ 7: 0];
  	assign w_filter4 = r_filter_line2[23:16];
  	assign w_filter5 = r_filter_line2[15: 8];
  	assign w_filter6 = r_filter_line2[ 7: 0];
  	assign w_filter7 = r_filter_line3[23:16];
  	assign w_filter8 = r_filter_line3[15: 8];
  	assign w_filter9 = r_filter_line3[ 7: 0];
  
  	// blur_filter
  
    always @(posedge I_CLK or negedge I_RSTN) begin
      	if	(!I_RSTN) r_last_case <= 'b0;
    	else		  r_last_case <= w_last_hact;    
  	end
  
    always @(posedge I_CLK or negedge I_RSTN) begin
      	if	(!I_RSTN) r_den_dly <= 'b0;
    	else		  r_den_dly <= i_den;    
  	end    
  
    always @(posedge I_CLK or negedge I_RSTN) begin
      	if	(!I_RSTN) r_scale_sum <= 'h0;
      	else if(w_case_1_1) r_scale_sum <= w_filter6*w_weight1 + w_filter5*w_weight2 + w_filter6*w_weight3 +
           								   w_filter3*w_weight4 + w_filter2*w_weight5 + w_filter3*w_weight6 +
           								   w_filter6*w_weight7 + w_filter5*w_weight8 + w_filter6*w_weight9 ;
      
      	else if(w_case_1_2) r_scale_sum <= w_filter4*w_weight1 + w_filter5*w_weight2 + w_filter6*w_weight3 +
           								   w_filter1*w_weight4 + w_filter2*w_weight5 + w_filter3*w_weight6 +
           								   w_filter4*w_weight7 + w_filter5*w_weight8 + w_filter6*w_weight9 ;
      
      	else if(w_case_1_3) r_scale_sum <= w_filter4*w_weight1 + w_filter5*w_weight2 + w_filter4*w_weight3 +
           								   w_filter1*w_weight4 + w_filter2*w_weight5 + w_filter1*w_weight6 +
           								   w_filter4*w_weight7 + w_filter5*w_weight8 + w_filter4*w_weight9 ;
      
      	else if(w_case_2_1) r_scale_sum <= w_filter3*w_weight1 + w_filter2*w_weight2 + w_filter3*w_weight3 +
           								   w_filter6*w_weight4 + w_filter5*w_weight5 + w_filter6*w_weight6 +
           								   w_filter9*w_weight7 + w_filter8*w_weight8 + w_filter9*w_weight9 ;
      
      	else if(w_case_2_2) r_scale_sum <= w_filter1*w_weight1 + w_filter2*w_weight2 + w_filter3*w_weight3 +
           								   w_filter4*w_weight4 + w_filter5*w_weight5 + w_filter6*w_weight6 +
           								   w_filter7*w_weight7 + w_filter8*w_weight8 + w_filter9*w_weight9 ;
      
      	else if(w_case_2_3) r_scale_sum <= w_filter1*w_weight1 + w_filter2*w_weight2 + w_filter1*w_weight3 +
           								   w_filter4*w_weight4 + w_filter5*w_weight5 + w_filter4*w_weight6 +
           								   w_filter7*w_weight7 + w_filter8*w_weight8 + w_filter7*w_weight9 ;
      
      	else if(w_case_3_1) r_scale_sum <= w_filter3*w_weight1 + w_filter2*w_weight2 + w_filter3*w_weight3 +
           								   w_filter6*w_weight4 + w_filter5*w_weight5 + w_filter6*w_weight6 +
           								   w_filter3*w_weight7 + w_filter2*w_weight8 + w_filter3*w_weight9 ;
      
      	else if(w_case_3_2) r_scale_sum <= w_filter1*w_weight1 + w_filter2*w_weight2 + w_filter3*w_weight3 +
           								   w_filter4*w_weight4 + w_filter5*w_weight5 + w_filter6*w_weight6 +
           								   w_filter1*w_weight7 + w_filter2*w_weight8 + w_filter3*w_weight9 ;
      
      	else if(w_case_3_3) r_scale_sum <= w_filter1*w_weight1 + w_filter2*w_weight2 + w_filter1*w_weight3 +
           								   w_filter4*w_weight4 + w_filter5*w_weight5 + w_filter4*w_weight6 +
           								   w_filter1*w_weight7 + w_filter2*w_weight8 + w_filter1*w_weight9 ;  
      
      	else				r_scale_sum <= 'h0;
      
  	end      
  
  	assign w_scale_shift = (i_mirror_mode_cap && !i_blur_mode_cap) ? r_scale_sum[7:0] : r_scale_sum[11:4];
  	assign w_scale_div   = (i_weight_wr_mode_cap) ? (r_scale_sum / r_weight_total) : w_scale_shift;
  	
  	assign w_first_case = (r_hor_cnt_dly	 == 'd2);
  	assign w_last_case  = r_last_case;
  	assign w_first_line = (r_vact_state_dly3 == 'd3);
  	assign w_middle_line = (r_vact_state_dly3 == 'd5);
  	assign w_last_line = (r_vact_state_dly3 == 'd7);
  
  	assign w_case_1_1	= w_first_line  &&  w_first_case && !w_last_case ;
  	assign w_case_1_2	= w_first_line  && !w_first_case && !w_last_case ;
  	assign w_case_1_3	= w_first_line  && !w_first_case &&  w_last_case ;  
  	assign w_case_2_1	= w_middle_line &&  w_first_case && !w_last_case ;  
  	assign w_case_2_2	= w_middle_line && !w_first_case && !w_last_case ;  
  	assign w_case_2_3	= w_middle_line && !w_first_case &&  w_last_case ;    
  	assign w_case_3_1	= w_last_line 	&&  w_first_case && !w_last_case ;   
  	assign w_case_3_2	= w_last_line 	&& !w_first_case && !w_last_case ; 
  	assign w_case_3_3	= w_last_line 	&& !w_first_case &&  w_last_case ;   
  
  
  	// output wideo sync
  	always @(posedge I_CLK or negedge I_RSTN) begin
      	if (!I_RSTN) begin
        	r_vsync_final 	<= 'b0;
            r_hsync_final 	<= 'b0;
            r_den_final 	<= 'b0;
      	end
    	else begin
            r_vsync_final 	<= i_vsync;
            r_hsync_final 	<= i_hsync;
            r_den_final 	<= w_first_line || w_middle_line || w_last_line;      
        end
  	end
  
  	assign o_vsync = r_vsync_final;
  	assign o_hsync = r_hsync_final;
  	assign o_den   = r_den_final;
  	assign o_data  = w_scale_div;
  
endmodule