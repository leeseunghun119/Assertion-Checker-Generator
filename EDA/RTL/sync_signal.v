module sync_signal #(parameter BUS_WIDTH = 8)
(
    input					I_CLK			,
    input					I_RSTN			,
    input [BUS_WIDTH-1:0]	i_signal		,
    input [BUS_WIDTH-1:0]	o_signal_sync	
);
  
  	reg [BUS_WIDTH-1:0] r_signal_sync;
  
  	always @(posedge I_CLK or negedge I_RSTN) begin
    	if(!I_RSTN) begin
      		r_signal_sync <= 'd0;
    	end
    	else begin
      		r_signal_sync <= i_signal;
        end
  	end
  
  	assign o_signal_sync = r_signal_sync;
  
endmodule