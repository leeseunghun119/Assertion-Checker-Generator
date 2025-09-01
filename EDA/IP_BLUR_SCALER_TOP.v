`define BASE_APB_MAX_DATA_WIDTH 32
`define BASE_APB_MAX_PARAM_WIDTH 32

module IP_BLUR_SCALER_TOP #(parameter PADDR_WIDTH =32, PDATA_WIDTH = 32)
( 
  	input							I_CLK,
	input 							I_RSTN,
  	input							I_VSYNC,
  	input							I_HSYNC,
  	input							I_DEN,
  	input	[7:0]					I_DATA,
  
  	output							O_VSYNC,
  	output							O_HSYNC,
  	output							O_DEN, 
  	output	[7:0]					O_DATA,

    input 				PRSTN,
    input 				PCLK,
    input 				i_PSEL,
    input 				i_PEN,
    input 				i_PWRITE,
  input 		[`BASE_APB_MAX_DATA_WIDTH-1:0] 	i_PADDR,
  input 		[`BASE_APB_MAX_DATA_WIDTH-1:0] 	i_PWDATA,
  output reg 	[`BASE_APB_MAX_DATA_WIDTH-1:0] 	o_PRDATA

);
  	localparam DATA_WIDTH	= 8;
  	localparam	PARAM_WIDTH = 16;
  	localparam	WEIGHT_WIDTH = 4;
  
  	wire							w_vsync_sync;
  	wire							w_hsync_sync;  	
  	wire							w_den_sync; 
  	wire [DATA_WIDTH-1:0]			w_data_sync;
  
  	wire							w_weight_wr_mode;
  	wire							w_mirror_mode;
  	wire							w_blur_mode;
  	wire [WEIGHT_WIDTH-1:0]			w_w1;
  	wire [WEIGHT_WIDTH-1:0]			w_w2;
  	wire [WEIGHT_WIDTH-1:0]			w_w3;
  	wire [WEIGHT_WIDTH-1:0]			w_w4;
  	wire [WEIGHT_WIDTH-1:0]			w_w5;
  	wire [WEIGHT_WIDTH-1:0]			w_w6;
  	wire [WEIGHT_WIDTH-1:0]			w_w7;
  	wire [WEIGHT_WIDTH-1:0]			w_w8;
  	wire [WEIGHT_WIDTH-1:0]			w_w9;
  	wire [PARAM_WIDTH-1:0]			w_hsw;
  	wire [PARAM_WIDTH-1:0]			w_hact;
  	wire [PARAM_WIDTH-1:0]			w_hfp;
  	wire [PARAM_WIDTH-1:0]			w_hbp;
  	wire [PARAM_WIDTH-1:0]			w_vsw;
  	wire [PARAM_WIDTH-1:0]			w_vact;
  	wire [PARAM_WIDTH-1:0]			w_vfp;
  	wire [PARAM_WIDTH-1:0]			w_vbp;

  	wire							w_weight_wr_mode_cap;
  	wire							w_mirror_mode_cap;
  	wire							w_blur_mode_cap;
  	wire [WEIGHT_WIDTH-1:0]			w_w1_cap;
  	wire [WEIGHT_WIDTH-1:0]			w_w2_cap;
  	wire [WEIGHT_WIDTH-1:0]			w_w3_cap;
  	wire [WEIGHT_WIDTH-1:0]			w_w4_cap;
  	wire [WEIGHT_WIDTH-1:0]			w_w5_cap;
  	wire [WEIGHT_WIDTH-1:0]			w_w6_cap;
  	wire [WEIGHT_WIDTH-1:0]			w_w7_cap;
  	wire [WEIGHT_WIDTH-1:0]			w_w8_cap;
  	wire [WEIGHT_WIDTH-1:0]			w_w9_cap;
  	wire [PARAM_WIDTH-1:0]			w_hsw_cap;
  	wire [PARAM_WIDTH-1:0]			w_hact_cap;
  	wire [PARAM_WIDTH-1:0]			w_hfp_cap;
  	wire [PARAM_WIDTH-1:0]			w_hbp_cap;
  	wire [PARAM_WIDTH-1:0]			w_vsw_cap;
  	wire [PARAM_WIDTH-1:0]			w_vact_cap;
  	wire [PARAM_WIDTH-1:0]			w_vfp_cap;
  	wire [PARAM_WIDTH-1:0]			w_vbp_cap;
  	wire [PARAM_WIDTH-1:0]			w_htotal;
  	wire [PARAM_WIDTH-1:0]			w_vtotal;  
  
  	wire							w_vsync_before_scale;
  	wire							w_hsync_before_scale;
  
   	wire							w_cs1;
  	wire							w_we1;
  	wire [PARAM_WIDTH-1:0]			w_addr1;
  	wire [DATA_WIDTH-1:0]			w_din1; 
  
   	wire							w_cs2;
  	wire							w_we2;
  	wire [PARAM_WIDTH-1:0]			w_addr2;
  	wire [DATA_WIDTH-1:0]			w_din2; 
  
   	wire							w_cs3;
  	wire							w_we3;
  	wire [PARAM_WIDTH-1:0]			w_addr3;
  	wire [DATA_WIDTH-1:0]			w_din3;   
  
   	wire							w_cs4;
  	wire							w_we4;
  	wire [PARAM_WIDTH-1:0]			w_addr4;
  	wire [DATA_WIDTH-1:0]			w_din4;   
  
  	wire [PARAM_WIDTH-1:0]			w_vact_state;
  	wire [PARAM_WIDTH-1:0]			w_hor_cnt;
  	wire [  3:0]					w_sel;	
  	wire							w_den_before_scale;

  	wire [DATA_WIDTH-1:0]			w_dout1;     
  	wire [DATA_WIDTH-1:0]			w_dout2;     
  	wire [DATA_WIDTH-1:0]			w_dout3;     
  	wire [DATA_WIDTH-1:0]			w_dout4;       
  	wire [DATA_WIDTH-1:0]			w_read_dout1;   	
  	wire [DATA_WIDTH-1:0]			w_read_dout2;
  	wire [DATA_WIDTH-1:0]			w_read_dout3;  
  
  	wire							w_vsync_after_scale;  
  	wire							w_hsync_after_scale;
  	wire							w_den_after_scale;
  	wire [DATA_WIDTH-1:0]			w_data_after_scale;  

  	wire							w_vsync_result;
  	wire							w_hsync_result;  
  	wire							w_den_result;  
  	wire [DATA_WIDTH-1:0]			w_data_result;    	
  
  
  	sync_signal #(.BUS_WIDTH(1))
  	u0_sync_signal
  	(
    	.I_CLK			(I_CLK			),
    	.I_RSTN			(I_RSTN			),
    	.i_signal		(I_VSYNC		),
    	.o_signal_sync	(w_vsync_sync	)
  	);
  
  
  	sync_signal #(.BUS_WIDTH(1))
  	u1_sync_signal
  	(
    	.I_CLK			(I_CLK			),
    	.I_RSTN			(I_RSTN			),
      	.i_signal		(I_HSYNC		),
      	.o_signal_sync	(w_hsync_sync	)
  	);  
  
  	sync_signal #(.BUS_WIDTH(1))
  	u2_sync_signal
  	(
    	.I_CLK			(I_CLK			),
    	.I_RSTN			(I_RSTN			),
      	.i_signal		(I_DEN			),
      	.o_signal_sync	(w_den_sync		)
  	);  
  
  	sync_signal #(.BUS_WIDTH(8))
  	u3_sync_signal
  	(
    	.I_CLK			(I_CLK			),
    	.I_RSTN			(I_RSTN			),
      	.i_signal		(I_DATA			),
      	.o_signal_sync	(w_data_sync	)
  	);  
  
  
    // SFR
   apb_sfr_ctrl u_apb_sfr_ctrl(
    .PRSTN(PRSTN),
    .PCLK(PCLK),
    .i_PSEL(i_PSEL),
    .i_PEN(i_PEN),
    .i_PWRITE(i_PWRITE),
    .i_PADDR(i_PADDR),
    .i_PWDATA(i_PWDATA),
    .o_PRDATA(o_PRDATA),
     .o_vsw(w_vsw),
     .o_vbp(w_vbp),  
     .o_vact(w_vact),   
     .o_vfp(w_vfp),
     .o_hsw(w_hsw),
     .o_hbp(w_hbp),   
     .o_hact(w_hact),    
     .o_hfp(w_hfp), 
	.o_weight_wr_mode	(w_weight_wr_mode),          
    .o_mirror_mode		(w_mirror_mode	),   
    .o_blur_mode		(w_blur_mode	),
    .o_w1				(w_w1			),      
    .o_w2				(w_w2			),      
    .o_w3				(w_w3			),      
    .o_w4				(w_w4			),      
    .o_w5				(w_w5			),      
    .o_w6				(w_w6			),      
    .o_w7				(w_w7			),      
    .o_w8				(w_w8			),
    .o_w9				(w_w9			)    
 
  );  
  
  

  
  sfr_cap #(.PARAM_WIDTH(PARAM_WIDTH),	.WEIGHT_WIDTH(WEIGHT_WIDTH))
  	u_sfr_cap
  	(
      	.I_CLK					(I_CLK				),
      	.I_RSTN					(I_RSTN				),
      	.i_vsync_sync			(w_vsync_sync		),
      	.i_weight_wr_mode		(w_weight_wr_mode	),          
      	.i_mirror_mode			(w_mirror_mode		),   
      	.i_blur_mode			(w_blur_mode		),
      	.i_w1					(w_w1				),      
      	.i_w2					(w_w2				),      
      	.i_w3					(w_w3				),      
      	.i_w4					(w_w4				),      
      	.i_w5					(w_w5				),      
      	.i_w6					(w_w6				),      
      	.i_w7					(w_w7				),      
      	.i_w8					(w_w8				),
      	.i_w9					(w_w9				),
        .i_hsw					(w_hsw				),   
      	.i_hact					(w_hact				),   
      	.i_hfp					(w_hfp				),   
      	.i_hbp					(w_hbp				),   
      	.i_vsw					(w_vsw				),   
      	.i_vact					(w_vact				),   
      	.i_vfp					(w_vfp				),   
      	.i_vbp					(w_vbp				),
      	.o_weight_wr_mode_cap	(w_weight_wr_mode_cap),          
      	.o_mirror_mode_cap		(w_mirror_mode_cap	),   
      	.o_blur_mode_cap		(w_blur_mode_cap	),
      	.o_w1_cap				(w_w1_cap			),      
      	.o_w2_cap				(w_w2_cap			),      
      	.o_w3_cap				(w_w3_cap			),      
      	.o_w4_cap				(w_w4_cap			),      
      	.o_w5_cap				(w_w5_cap			),      
      	.o_w6_cap				(w_w6_cap			),      
      	.o_w7_cap				(w_w7_cap			),      
      	.o_w8_cap				(w_w8_cap			),
      	.o_w9_cap				(w_w9_cap			),
        .o_hsw_cap				(w_hsw_cap			),   
      	.o_hact_cap				(w_hact_cap			),   
      	.o_hfp_cap				(w_hfp_cap			),   
      	.o_hbp_cap				(w_hbp_cap			),   
      	.o_vsw_cap				(w_vsw_cap			),   
      	.o_vact_cap				(w_vact_cap			),   
      	.o_vfp_cap				(w_vfp_cap			),   
      	.o_vbp_cap				(w_vbp_cap			),       
      	.o_htotal				(w_htotal			),     
      	.o_vtotal				(w_vtotal			)
  	);  
  
  
  video_sync_out_gen #(.PARAM_WIDTH(PARAM_WIDTH))
  	u_video_sync_out_gen
  	(
      	.I_CLK					(I_CLK				),
      	.I_RSTN					(I_RSTN				),
      	.i_vsync_sync			(w_vsync_sync		),
      	.i_mirror_mode_cap		(w_mirror_mode_cap	),   
      	.i_blur_mode_cap		(w_blur_mode_cap	),
        .i_hsw_cap				(w_hsw_cap			),   
      	.i_hact_cap				(w_hact_cap			),   
      	.i_hfp_cap				(w_hfp_cap			),   
      	.i_hbp_cap				(w_hbp_cap			),   
      	.i_vsw_cap				(w_vsw_cap			),   
      	.i_vact_cap				(w_vact_cap			),   
      	.i_vfp_cap				(w_vfp_cap			),   
      	.i_vbp_cap				(w_vbp_cap			),       
      	.i_htotal				(w_htotal			),     
      	.i_vtotal				(w_vtotal			),
      	.o_vsync				(w_vsync_before_scale),
      	.o_hsync				(w_hsync_before_scale)
  	);    
  
  
  ram_ctrl #(.PARAM_WIDTH(PARAM_WIDTH),	.DATA_WIDTH(DATA_WIDTH))
  	u_ram_ctrl
  	(
      	.I_CLK					(I_CLK				),
      	.I_RSTN					(I_RSTN				),
      	.i_vsync_sync			(w_vsync_sync		),
      	.i_hsync_sync			(w_hsync_sync		),      
      	.i_den_sync				(w_den_sync			),       
      	.i_data_sync			(w_data_sync		), 
      	.i_weight_wr_mode_cap	(w_weight_wr_mode_cap),          
      	.i_mirror_mode_cap		(w_mirror_mode_cap	),   
      	.i_blur_mode_cap		(w_blur_mode_cap	),
   
      	.i_hact_cap				(w_hact_cap			),         
      	.i_vact_cap				(w_vact_cap			),    
      	.i_htotal				(w_htotal			),      
      
      	.o_cs1					(w_cs1				),      
      	.o_we1					(w_we1				),      
      	.o_addr1				(w_addr1			),      
      	.o_din1					(w_din1				),
      	.o_cs2					(w_cs2				),      
      	.o_we2					(w_we2				),      
      	.o_addr2				(w_addr2			),      
      	.o_din2					(w_din2				),
      	.o_cs3					(w_cs3				),      
      	.o_we3					(w_we3				),      
      	.o_addr3				(w_addr3			),      
      	.o_din3					(w_din3				),
      	.o_cs4					(w_cs4				),      
      	.o_we4					(w_we4				),      
      	.o_addr4				(w_addr4			),      
      	.o_din4					(w_din4				),      
      
      	.o_vact_state			(w_vact_state		),     
      	.o_hor_cnt				(w_hor_cnt			),
      	.o_sel					(w_sel				),
      	.o_den					(w_den_before_scale	)
  	);    
  
  mux_sram_read #(.DATA_WIDTH(DATA_WIDTH))
  	u_mux_sram_read
  	(
      	.I_CLK					(I_CLK				),
      	.I_RSTN					(I_RSTN				),
      	.i_sel					(w_sel				),
   
      	.i_read_din1			(w_dout1			),         
      	.i_read_din2			(w_dout2			),   
      	.i_read_din3			(w_dout3			),   
      	.i_read_din4			(w_dout4			),         
      
      	.o_read_dout1			(w_read_dout1		),     
      	.o_read_dout2			(w_read_dout2		),  
      	.o_read_dout3			(w_read_dout3		)        
  	);     
  
  
  blur_scaler #(.WEIGHT_WIDTH(WEIGHT_WIDTH), .PARAM_WIDTH(PARAM_WIDTH),	.DATA_WIDTH(DATA_WIDTH))
  	u_blur_scaler
  	(
      	.I_CLK					(I_CLK				),
      	.I_RSTN					(I_RSTN				),
      	.i_vact_state			(w_vact_state		),
     	.i_hor_cnt				(w_hor_cnt			),          
      	.i_vsync				(w_vsync_before_scale),   
      	.i_hsync				(w_hsync_before_scale),   
      	.i_den					(w_den_before_scale	),
      	.i_weight_wr_mode_cap	(w_weight_wr_mode_cap),          
      	.i_mirror_mode_cap		(w_mirror_mode_cap	),   
      	.i_blur_mode_cap		(w_blur_mode_cap	),
      	.i_w1_cap				(w_w1_cap			),      
      	.i_w2_cap				(w_w2_cap			),      
      	.i_w3_cap				(w_w3_cap			),      
      	.i_w4_cap				(w_w4_cap			),      
      	.i_w5_cap				(w_w5_cap			),      
      	.i_w6_cap				(w_w6_cap			),      
      	.i_w7_cap				(w_w7_cap			),      
      	.i_w8_cap				(w_w8_cap			),
      	.i_w9_cap				(w_w9_cap			),
      	.i_sram_rd1				(w_read_dout1		),   
      	.i_sram_rd2				(w_read_dout2		),  
      	.i_sram_rd3				(w_read_dout3		),        
      
      	.o_vsync				(w_vsync_after_scale), 
      	.o_hsync				(w_hsync_after_scale),      
      	.o_den					(w_den_after_scale	),  
      	.o_data					(w_data_after_scale	)        
  	);    
  
  single_port_ram #(.PARAM_WIDTH(PARAM_WIDTH), .DATA_WIDTH(DATA_WIDTH))
  	u0_single_port_ram
  	(
      	.I_CLK					(I_CLK			),
      	.I_RSTN					(I_RSTN			),
      	.i_cs					(w_cs1			),      	
      	.i_we					(w_we1			),
      	.i_addr					(w_addr1		),
      	.i_din					(w_din1			),
      	.o_dout					(w_dout1		)       
  	);      
  
  single_port_ram #(.PARAM_WIDTH(PARAM_WIDTH), .DATA_WIDTH(DATA_WIDTH))
  	u1_single_port_ram
  	(
      	.I_CLK					(I_CLK			),
      	.I_RSTN					(I_RSTN			),
      	.i_cs					(w_cs2			),      	
      	.i_we					(w_we2			),
      	.i_addr					(w_addr2		),
      	.i_din					(w_din2			),
      	.o_dout					(w_dout2		)       
  	);      

  single_port_ram #(.PARAM_WIDTH(PARAM_WIDTH), .DATA_WIDTH(DATA_WIDTH))
  	u2_single_port_ram
  	(
      	.I_CLK					(I_CLK			),
      	.I_RSTN					(I_RSTN			),
      	.i_cs					(w_cs3			),      	
      	.i_we					(w_we3			),
      	.i_addr					(w_addr3		),
      	.i_din					(w_din3			),
      	.o_dout					(w_dout3		)       
  	);      
  
  single_port_ram #(.PARAM_WIDTH(PARAM_WIDTH), .DATA_WIDTH(DATA_WIDTH))
  	u3_single_port_ram
  	(
      	.I_CLK					(I_CLK			),
      	.I_RSTN					(I_RSTN			),
      	.i_cs					(w_cs4			),      	
      	.i_we					(w_we4			),
      	.i_addr					(w_addr4		),
      	.i_din					(w_din4			),
      	.o_dout					(w_dout4		)       
  	);      
  
  
  mux_output #(.DATA_WIDTH(DATA_WIDTH))
  	u_mux_output
  	(
      	.I_CLK					(I_CLK				),
      	.I_RSTN					(I_RSTN				),
      	.i_mirror_mode_cap		(w_mirror_mode_cap	),   
      	.i_blur_mode_cap		(w_blur_mode_cap	),
      	.i_vsync_bypass			(w_vsync_sync		),   
      	.i_hsync_bypass			(w_hsync_sync		),
      	.i_den_bypass			(w_den_sync			),
      	.i_data_bypass			(w_data_sync		),
      

      	.i_vsync_scaler			(w_vsync_after_scale),   
      	.i_hsync_scaler			(w_hsync_after_scale),   
      	.i_den_scaler			(w_den_after_scale	),   
      	.i_data_scaler			(w_data_after_scale	),         
      
      	.o_vsync				(O_VSYNC			), 
      	.o_hsync				(O_HSYNC			),      
      	.o_den					(O_DEN				),  
      	.o_data					(O_DATA				)        
  	);   
  
endmodule