module video_sync_out_gen #(parameter PARAM_WIDTH = 16)
(
  	input							I_CLK,
	input 							I_RSTN,  
  	input							i_vsync_sync,
    input							i_mirror_mode_cap,
    input							i_blur_mode_cap, 
  	input [PARAM_WIDTH-1:0]			i_hsw_cap,
  	input [PARAM_WIDTH-1:0]			i_hact_cap,
  	input [PARAM_WIDTH-1:0]			i_hfp_cap,
  	input [PARAM_WIDTH-1:0]			i_hbp_cap,
  	input [PARAM_WIDTH-1:0]			i_vsw_cap,
  	input [PARAM_WIDTH-1:0]			i_vact_cap,
  	input [PARAM_WIDTH-1:0]			i_vfp_cap,
  	input [PARAM_WIDTH-1:0]			i_vbp_cap,
  	input [PARAM_WIDTH-1:0]			i_htotal, 
  	input [PARAM_WIDTH-1:0]			i_vtotal,  
  	output							o_vsync,
  	output							o_hsync  
      
);
  
  	localparam BUFFER = 4'b0010; // 2Line
  
  	wire							w_cnt_en;
  	wire							w_cnt_rst;
  	wire							w_en_trigger;
  	wire [PARAM_WIDTH-1:0]			w_pixel_cnt;  	
  	wire [PARAM_WIDTH-1:0]			w_line_cnt;
  	wire							w_line_cnt_en;  
  	wire							w_line_done;  
  	wire							w_buf_rst;    
  	wire							w_buf_shift;    
  	wire							w_buf_done;
    wire							w_buf_done_edge;    
    wire							w_hsync_en;
  	wire							w_vsync_en;
  	wire							w_vsync_edge;
  
  
  	reg [PARAM_WIDTH-1:0]			r_vsw;  	
  	reg [PARAM_WIDTH-1:0]			r_hsw;
  	reg								r_vsync_dly;
  	reg								r_vsync_edge_dly;
  	reg								r_cnt_en;
  	reg [ 3:0]						r_buffer;
  	reg								r_buf_done_dly;
  	reg								r_hsync;
  	reg								r_vsync;
  
  	// edge detector
  	always @(posedge I_CLK or negedge I_RSTN) begin
    	if(!I_RSTN) begin
      		r_vsync_dly <= 'b0;
    	end
    	else begin
      		r_vsync_dly <= i_vsync_sync;
        end
  	end  
  
  	assign w_vsync_edge = i_vsync_sync && !r_vsync_dly;
  
  	// counter enable
  	always @(posedge I_CLK or negedge I_RSTN) begin
    	if(!I_RSTN) begin
      		r_vsync_edge_dly <= 'b0;
    	end
    	else begin
      		r_vsync_edge_dly <= w_vsync_edge;
        end
  	end    

  	always @(posedge I_CLK or negedge I_RSTN) begin
    	if(!I_RSTN) begin
      		r_cnt_en <= 'b0;
    	end
      	else if(w_en_trigger) begin
      		r_cnt_en <= 'b1;
        end
  	end 
  
  	assign	w_cnt_en = r_cnt_en;
  	assign	w_en_trigger = (r_vsync_edge_dly && (i_mirror_mode_cap || i_blur_mode_cap));
  
  	// parameter setting

  	always @(posedge I_CLK or negedge I_RSTN) begin
    	if(!I_RSTN) begin
      		r_vsw <= 'd0;
          	r_hsw <= 'd0;
    	end
      	else if(r_vsync_edge_dly) begin
      		r_vsw <= i_vsw_cap - 'd1;
        	r_hsw <= i_hsw_cap - 'd1;
        end
  	end   
  
  	// pixel counter
  	counter #(.BIT_WIDTH(PARAM_WIDTH))
  	u_pixel_cnt
  	(
      	.I_CLK					(I_CLK				),
      	.I_RSTN					(I_RSTN				),
      	.i_enable				(w_cnt_en			),
      	.i_sync_cnt				(w_buf_done_edge || w_buf_shift	),       
      	.i_max_cnt				(i_htotal			),
      	.o_cnt					(w_pixel_cnt		),
      	.o_done					(w_line_cnt_en		)
  	);   	
  
  	// line counter
  	counter #(.BIT_WIDTH(PARAM_WIDTH))
  	u_line_cnt
  	(
      	.I_CLK					(I_CLK				),
      	.I_RSTN					(I_RSTN				),
      	.i_enable				(w_line_cnt_en		),
      	.i_sync_cnt				(w_buf_done_edge || w_buf_shift	),       
      	.i_max_cnt				(i_vtotal			),
      	.o_cnt					(w_line_cnt			),
      	.o_done					(w_line_done		)
  	);   	
    
  	// buffer setting
  	always @(posedge I_CLK or negedge I_RSTN) begin
    	if(!I_RSTN) begin
      		r_buffer <= 'd0;
    	end
      	else if(w_buf_rst) begin
      		r_buffer <= BUFFER;
        end
      	else if(w_buf_shift) begin
        	r_buffer <= {1'b0, r_buffer[3:1]};
        end      
  	end   

  	always @(posedge I_CLK or negedge I_RSTN) begin
    	if(!I_RSTN) begin
      		r_buf_done_dly <= 'b0;
    	end
    	else begin
      		r_buf_done_dly <= w_buf_done;
        end
  	end   
  
  assign	w_buf_rst		= (w_vsync_edge && (!i_mirror_mode_cap	&& !i_blur_mode_cap));
  	assign	w_buf_shift		= (w_line_cnt[0] && (w_pixel_cnt == 'd0) &&  w_cnt_en) && !w_buf_done;
  	assign	w_buf_done		= !r_buffer;
  	assign	w_buf_done_edge	= (!r_buf_done_dly && w_buf_done);
  
  	// hsync generation
  	always @(posedge I_CLK or negedge I_RSTN) begin
    	if(!I_RSTN) begin
      		r_hsync <= 'd0;
    	end
      	else if(w_hsync_en) begin
      		r_hsync <= ~r_hsync;
        end
  	end 
  
  	assign	w_hsync_en	= (w_buf_done_edge	|| w_line_cnt_en || (w_pixel_cnt == r_hsw)) && w_buf_done	&& w_cnt_en;
  	assign	o_hsync	= r_hsync;
  
  	// vsync generation
  	always @(posedge I_CLK or negedge I_RSTN) begin
    	if(!I_RSTN) begin
      		r_vsync <= 'd0;
    	end
        else if(w_vsync_en) begin
      		r_vsync <= ~r_vsync;
        end
  	end 
  
  assign	w_vsync_en	= (w_buf_done_edge	|| (w_line_done || (w_line_cnt == r_vsw) && w_line_cnt_en)) && w_buf_done && w_cnt_en;
  	assign	o_vsync	= r_vsync;  
  
 
  
endmodule