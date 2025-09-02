module mux_output #(parameter DATA_WIDTH = 8)
(
  	input							I_CLK,
	input 							I_RSTN,
  	input							i_mirror_mode_cap,
  	input							i_blur_mode_cap,
  	input							i_vsync_bypass,
  	input							i_hsync_bypass,  
  	input							i_den_bypass,  
  	input [DATA_WIDTH-1:0]			i_data_bypass,  
  	input							i_vsync_scaler,  
  	input							i_hsync_scaler,   
  	input							i_den_scaler,    
  	input [DATA_WIDTH-1:0]			i_data_scaler,    
       
	output							o_vsync,
  	output							o_hsync,
  	output							o_den,
  	output [DATA_WIDTH-1:0]			o_data
);
  
  	wire					w_scaler_on;
  	reg						r_vsync_bypass_dly;
  	reg						r_hsync_bypass_dly;
  	reg						r_den_bypass_dly;
  	reg [DATA_WIDTH-1:0]	r_data_bypass_dly;
  	reg						r_vsync;
  	reg						r_hsync;
  	reg						r_den;
  	reg [DATA_WIDTH-1:0]	r_data;
  	
  
  	//output mux
  	always @(posedge I_CLK or negedge I_RSTN) begin
      	if (!I_RSTN) begin
          	r_vsync_bypass_dly <= 'h0;
            r_hsync_bypass_dly <= 'h0;
            r_den_bypass_dly   <= 'h0;
            r_data_bypass_dly  <= 'h0;
      	end  
    	else begin
          	r_vsync_bypass_dly <= i_vsync_bypass;
            r_hsync_bypass_dly <= i_hsync_bypass;
            r_den_bypass_dly   <= i_den_bypass;
            r_data_bypass_dly  <= i_data_bypass;
        end
  	end    

  
  	always @(posedge I_CLK or negedge I_RSTN) begin
      	if (!I_RSTN) begin
          	r_vsync <= 'h0;
            r_hsync <= 'h0;
            r_den   <= 'h0;
            r_data  <= 'h0;
      	end  
      	else if(w_scaler_on)begin
          	r_vsync <= i_vsync_scaler;
            r_hsync <= i_hsync_scaler;
            r_den   <= i_den_scaler;
            r_data  <= i_data_scaler;
        end
        else begin
          	r_vsync <= r_vsync_bypass_dly;
            r_hsync <= r_hsync_bypass_dly;
            r_den   <= r_den_bypass_dly;
            r_data  <= r_data_bypass_dly;
        end
  	end     
  
  
 	assign	w_scaler_on = i_mirror_mode_cap || i_blur_mode_cap;
  
  	assign	o_vsync = r_vsync;
  	assign	o_hsync = r_hsync;
  	assign	o_den   = r_den;
  	assign	o_data  = r_data;
  
endmodule