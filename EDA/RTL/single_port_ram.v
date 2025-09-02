module single_port_ram #(parameter PARAM_WIDTH = 11, DATA_WIDTH = 8)
(
    input						I_CLK			,
    input						I_RSTN			,
    input						i_cs			,
    input						i_we			,
    input	[PARAM_WIDTH-1:0]	i_addr			,
    input	[ DATA_WIDTH-1:0]	i_din			,
    output	[ DATA_WIDTH-1:0]	o_dout							 
);
  
  	reg	[DATA_WIDTH-1:0]	r_mem		[0:1920-1]		;
  	reg	[DATA_WIDTH-1:0]	r_tmp_data					;
  
  	always @(posedge I_CLK or negedge I_RSTN) begin
      	if(!I_RSTN) begin
      		r_tmp_data <= 'h0;
      	end
      	else if (i_cs) begin
        	if(!i_we) begin
        		r_tmp_data <= r_mem[i_addr];
      		end
      		else begin
      			r_tmp_data <= 'h0;
      		end
    	end
  	end

  	always @(posedge I_CLK or negedge I_RSTN) begin
      	if (i_cs)begin
      		if(i_we)begin
        		r_mem[i_addr] <= i_din;
      		end
    	end
  	end
  
  	assign o_dout = r_tmp_data;
  
endmodule