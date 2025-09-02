module counter #(parameter BIT_WIDTH = 8)
(
	input					I_CLK,
  	input					I_RSTN,
  	input					i_enable,
  	input					i_sync_cnt,
  	input	[BIT_WIDTH-1:0] i_max_cnt,
  	input	[BIT_WIDTH-1:0] o_cnt,
  	output					o_done
);
  
  	wire					w_cnt_done;
  	reg [BIT_WIDTH-1:0] 	r_cnt;
  
    assign w_cnt_done = ((r_cnt == i_max_cnt) && i_enable) || i_sync_cnt;
  	
  	always @(posedge I_CLK or negedge I_RSTN) begin
      	if 		(!I_RSTN) 	r_cnt <= 'd0;
      	else if	(w_cnt_done)r_cnt <= 'd0;
      	else if	(i_enable)	r_cnt <= r_cnt + 'd1;
    end
  
  	assign o_cnt	= r_cnt;
  	assign o_done = ((r_cnt == i_max_cnt) && i_enable);
  
endmodule