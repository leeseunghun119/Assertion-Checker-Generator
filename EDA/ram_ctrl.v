module ram_ctrl #(parameter PARAM_WIDTH = 16, DATA_WIDTH = 8)
(
    input						I_CLK				,
    input						I_RSTN				,
    input						i_vsync_sync		,
    input						i_hsync_sync		,
    input						i_den_sync			,
    input	[ DATA_WIDTH-1:0]	i_data_sync			,
    input						i_weight_wr_mode_cap,
    input						i_mirror_mode_cap	,
    input						i_blur_mode_cap		,
    input	[PARAM_WIDTH-1:0]	i_hact_cap			,
    input	[PARAM_WIDTH-1:0]	i_vact_cap			,
    input	[PARAM_WIDTH-1:0]	i_htotal			,
    output						o_cs1				,
    output						o_we1				,
    output	[PARAM_WIDTH-1:0]	o_addr1				,
    output	[ DATA_WIDTH-1:0]	o_din1				,						 
    output						o_cs2				,
    output						o_we2				,
    output	[PARAM_WIDTH-1:0]	o_addr2				,
    output	[ DATA_WIDTH-1:0]	o_din2				,						 
    output						o_cs3				,
    output						o_we3				,
    output	[PARAM_WIDTH-1:0]	o_addr3				,
    output	[ DATA_WIDTH-1:0]	o_din3				,						 
    output						o_cs4				,
    output						o_we4				,
    output	[PARAM_WIDTH-1:0]	o_addr4				,
    output	[ DATA_WIDTH-1:0]	o_din4				,						 
    output	[PARAM_WIDTH-1:0]	o_vact_state		,
    output	[PARAM_WIDTH-1:0]	o_hor_cnt			,
    output	[            3:0]	o_sel				,
    output						o_den				
);
  
  	//-----------//
  	//---state---//
  	//-----------//
  	localparam	IDLE	= 0	,
  				//Write_FSM
  				WRITE1	= 1	,
  				WAIT1	= 2	,
  				WRITE2	= 3	,
  				WAIT2	= 4	,
  				WRITE3	= 5	,
  				WAIT3	= 6	,
  				WRITE4	= 7	,
  				WAIT4	= 8	,
  
  				//Read_FSM
  				BUFFER1	= 1	,
  				BUFFER2	= 2	,
  				FIRST	= 3	,
  				BLANK1	= 4	,
  				READ	= 5	,
  				BLANK2	= 6	,
  				LAST	= 7	;
  
  //-----------//
  //---wire----//
  //-----------//
  wire						w_vsync_edge	;
  wire						w_hsync_edge	;
  wire						w_act_blank_en	;
  wire						w_hor_cnt_en	;
  wire						w_ver_cnt_en	;
  wire						w_hor_cnt_rst	;
  wire						w_ver_cnt_rst	;
  wire	[PARAM_WIDTH-1:0]	w_hor_cnt		;
  wire	[PARAM_WIDTH-1:0]	w_ver_cnt		;
  wire						w_line_done		;
  wire						w_frame_done	;
  wire						w_wr_fsm_start	;
  wire						w_rd_fsm_start	;
  wire						w_wait1_to_wr1	;
  wire						w_wait1_to_wr2	;
  wire						w_wait2_to_wr2	;
  wire						w_wait2_to_wr3	;
  wire						w_wait3_to_wr3	;
  wire						w_wait3_to_wr4	;
  wire						w_wait4_to_wr4	;
  wire						w_wait_to_idle	;
  wire						w_wait4_to_idle ;
  wire						w_line_buffer	;
  wire						w_blank_read	;
  wire						w_last_read		;
  
  wire						w_cs1_wr		;
  wire						w_cs1_rd		;
  wire						w_we1			;
  wire	[PARAM_WIDTH-1:0]	w_addr1_wr		;
  wire	[PARAM_WIDTH-1:0]	w_addr1_rd		;
  wire	[ DATA_WIDTH-1:0]	w_din1			;
  wire						w_cs2_wr		;
  wire						w_cs2_rd		;
  wire						w_we2			;
  wire	[PARAM_WIDTH-1:0]	w_addr2_wr		;
  wire	[PARAM_WIDTH-1:0]	w_addr2_rd		;
  wire	[ DATA_WIDTH-1:0]	w_din2			;
  wire						w_cs3_wr		;
  wire						w_cs3_rd		;
  wire						w_we3			;
  wire	[PARAM_WIDTH-1:0]	w_addr3_wr		;
  wire	[PARAM_WIDTH-1:0]	w_addr3_rd		;
  wire	[ DATA_WIDTH-1:0]	w_din3			;
  wire						w_cs4_wr		;
  wire						w_cs4_rd		;
  wire						w_we4			;
  wire	[PARAM_WIDTH-1:0]	w_addr4_wr		;
  wire	[PARAM_WIDTH-1:0]	w_addr4_rd		;
  wire	[ DATA_WIDTH-1:0]	w_din4			;
  wire	[            3:0]	w_rd_en			;
  wire	[            3:0]	w_rd_sel		;
  wire	[            3:0]	w_sel			;
  wire						w_den			;
  
  
  //-----------//
  //---reg-----//
  //-----------//
  reg	[ DATA_WIDTH-1:0]	r_data_dly			;
  reg	[PARAM_WIDTH-1:0]	r_vact				;
  reg	[PARAM_WIDTH-1:0]	r_hact				;
  reg	[PARAM_WIDTH-1:0]	r_hblank			;
  reg	[            3:0]	r_wr_current_state	;
  reg	[            3:0]	r_wr_next_state		;
  reg	[            3:0]	r_rd_current_state	;
  reg	[            3:0]	r_rd_next_state		;
  reg						r_act_blank_sel		;
  reg						r_vsync_dly			;
  reg						r_vsync_edge_dly	;
  reg						r_hsync_dly			;
  
  reg						r_cs1				;
  reg						r_we1				;
  reg	[PARAM_WIDTH-1:0]	r_addr1				;
  reg	[ DATA_WIDTH-1:0]	r_din1				;
  reg						r_cs2				;
  reg						r_we2				;
  reg	[PARAM_WIDTH-1:0]	r_addr2				;
  reg	[ DATA_WIDTH-1:0]	r_din2				;
  reg						r_cs3				;
  reg						r_we3				;
  reg	[PARAM_WIDTH-1:0]	r_addr3				;
  reg	[ DATA_WIDTH-1:0]	r_din3				;
  reg						r_cs4				;
  reg						r_we4				;
  reg	[PARAM_WIDTH-1:0]	r_addr4				;
  reg	[ DATA_WIDTH-1:0]	r_din4				;
  reg	[PARAM_WIDTH-1:0]	r_vact_state		;
  reg	[PARAM_WIDTH-1:0]	r_hor_cnt			;
  reg	[            3:0]	r_sel				;
  reg						r_den				;
  
  
  //-------------------------//
  //---vsync_edge_detector---//
  //-------------------------//
  always @(posedge I_CLK or negedge I_RSTN) begin
    if	(!I_RSTN) 	r_vsync_dly <= 'b0			;
    else		 	r_vsync_dly <= i_vsync_sync	;
  end
  
  assign w_vsync_edge = i_vsync_sync && !r_vsync_dly;
  
  //-------------------------//
  //---hsync_edge_detector---//
  //-------------------------//
  always @(posedge I_CLK or negedge I_RSTN) begin
    if	(!I_RSTN) 	r_hsync_dly <= 'b0			;
    else		 	r_hsync_dly <= i_hsync_sync	;
  end
  
  assign w_hsync_edge = i_hsync_sync && !r_hsync_dly;
  
  //-----------------------//
  //---parameter_setting---//
  //-----------------------//
  always @(posedge I_CLK or negedge I_RSTN) begin
    if	(!I_RSTN) 	r_vsync_edge_dly <= 'b0				;
    else		 	r_vsync_edge_dly <= w_vsync_edge	;
  end
  
  always @(posedge I_CLK or negedge I_RSTN) begin
    if(!I_RSTN) begin
      r_vact	<= 'd0;
      r_hact	<= 'd0;
      r_hblank	<= 'd0;
    end
    else if(r_vsync_edge_dly) begin
      r_vact	<= i_vact_cap + 'd1			;
      r_hact	<= i_hact_cap - 'd1			;
      r_hblank	<= i_htotal   - i_hact_cap	;
    end
  end
  
  //----------------//
  //---data_delay---//
  //----------------//
  always @(posedge I_CLK or negedge I_RSTN) begin
    if	(!I_RSTN) 	r_data_dly <= 'b0			;
    else		 	r_data_dly <= i_data_sync	;
  end
  
  //-------------//
  //---hor_cnt---//
  //-------------//
  counter #(.BIT_WIDTH(PARAM_WIDTH))
  u_hor_cnt
  (
     .I_CLK		(I_CLK			)
    ,.I_RSTN	(I_RSTN			)
    ,.i_enable	(w_hor_cnt_en	)
    ,.i_sync_cnt(w_hor_cnt_rst	)
    ,.i_max_cnt	(16'd1930		)
    ,.o_cnt		(w_hor_cnt		)
    ,.o_done	(w_link_done	)
  );
  
  always @(posedge I_CLK or negedge I_RSTN) begin
    if		(!I_RSTN		) 	r_act_blank_sel <= 'b0				;
    else if	(!w_hor_cnt_en	) 	r_act_blank_sel <= 'b0				;
    else if	(w_act_blank_en	) 	r_act_blank_sel <= ~r_act_blank_sel	; // 0: active 1: blank
  end
  
  assign w_hor_cnt_en   = (r_rd_current_state != IDLE)																					;
  assign w_act_blank_en = (!r_act_blank_sel && (w_hor_cnt == r_hact)) || (r_act_blank_sel && (w_hor_cnt == r_hblank))					;
  assign w_hor_cnt_rst  = (!r_act_blank_sel && (w_hor_cnt == r_hact)) || (r_act_blank_sel && (w_hor_cnt == r_hblank)) || !w_hor_cnt_en	;
  
  //-------------//
  //---ver_cnt---//
  //-------------//
  counter #(.BIT_WIDTH(PARAM_WIDTH))
  u_ver_cnt
  (
     .I_CLK		(I_CLK			)
    ,.I_RSTN	(I_RSTN			)
    ,.i_enable	(w_ver_cnt_en	)
    ,.i_sync_cnt(w_ver_cnt_rst	)
    ,.i_max_cnt	(16'd1090		)
    ,.o_cnt		(w_ver_cnt		)
    ,.o_done	(w_frame_done	)
  );
  
  assign w_ver_cnt_en  = (r_rd_current_state != IDLE) && w_hsync_edge	;
  assign w_ver_cnt_rst = (r_rd_current_state == IDLE)					;
  //assign w_ver_cnt_rst = (r_rd_current_state == LAST)					;
  
  //---------------------//
  //---FSM_transitions---//
  //---------------------//
  always @(posedge I_CLK or negedge I_RSTN) begin
    if(!I_RSTN) begin
      r_wr_current_state	<= 'd0;
      r_rd_current_state	<= 'd0;
    end
    else begin
      r_wr_current_state	<= r_wr_next_state;
      r_rd_current_state	<= r_rd_next_state;
    end
  end
  
  //-------------------//
  //---MEM_write_FSM---//
  //-------------------//
  always @(*) begin
    case(r_wr_current_state)
      IDLE		:	r_wr_next_state = 	(w_wr_fsm_start	)	? WRITE1	: IDLE		;
      WRITE1	:	r_wr_next_state = 	(!i_den_sync	)	? WAIT1		: WRITE1	;
      WAIT1		:	r_wr_next_state = 	(w_wait1_to_wr1	)	? WRITE1	:
       									(w_wait1_to_wr2	)	? WRITE2	:
       									(w_wait_to_idle	)	? IDLE		: WAIT1		;
      WRITE2	:	r_wr_next_state =	(!i_den_sync	)	? WAIT2		: WRITE2	;
      WAIT2		:	r_wr_next_state = 	(w_wait2_to_wr2	)	? WRITE2	:
        								(w_wait2_to_wr3	)	? WRITE3	:
       									(w_wait_to_idle	)	? IDLE		: WAIT2		;
      WRITE3	:	r_wr_next_state = 	(!i_den_sync	)	? WAIT3		: WRITE3	;
      WAIT3		:	r_wr_next_state = 	(w_wait3_to_wr3	)	? WRITE3	:
        								(w_wait3_to_wr4	)	? WRITE4	:
        								(w_wait_to_idle	)	? IDLE		: WAIT3		;
      WRITE4	:	r_wr_next_state = 	(!i_den_sync	)	? WAIT4		: WRITE4	;
      WAIT4		:	r_wr_next_state = 	(w_wait4_to_wr4	)	? WRITE4	:
        								(w_wait4_to_idle)	? IDLE		: WAIT4		;
      default	:	r_wr_next_state = 	IDLE										;
    endcase
  end
  
  assign w_wr_fsm_start	=	(( i_blur_mode_cap	||	i_mirror_mode_cap)	&&	 i_den_sync)	;
  assign w_wait1_to_wr1	=	(!w_ver_cnt[1]		&&	!w_ver_cnt[0]		&&	 i_den_sync)	;
  assign w_wait1_to_wr2	=	(!w_ver_cnt[1]		&&	 w_ver_cnt[0]		&&	 i_den_sync)	;
  assign w_wait2_to_wr2	=	(!w_ver_cnt[1]		&&	 w_ver_cnt[0]		&&	 i_den_sync)	;
  assign w_wait2_to_wr3	=	( w_ver_cnt[1]		&&	!w_ver_cnt[0]		&&	 i_den_sync)	;
  assign w_wait3_to_wr3	=	( w_ver_cnt[1]		&&	!w_ver_cnt[0]		&&	 i_den_sync)	;
  assign w_wait3_to_wr4	=	( w_ver_cnt[1]		&&	 w_ver_cnt[0]		&&	 i_den_sync)	;
  assign w_wait4_to_wr4	=	( w_ver_cnt[1]		&&	 w_ver_cnt[0]		&&	 i_den_sync)	;
  assign w_wait_to_idle	=	((w_ver_cnt			==	 i_vact_cap	)		&&	!i_den_sync)	;
  assign w_wait4_to_idle=	(!w_ver_cnt[1]		&&	!w_ver_cnt[0]		&&	!i_den_sync)	;
  
  //--------------------------//
  //---MEM_write_FSM_output---//
  //--------------------------//
  assign w_cs1_wr	=	(r_wr_current_state == WRITE1) 						;
  assign w_we1		=	(r_wr_current_state == WRITE1) 						;
  assign w_addr1_wr	=	(r_wr_current_state == WRITE1) ? w_hor_cnt  : 'd0	;
  assign w_din1		=	(r_wr_current_state == WRITE1) ? r_data_dly : 'd0	;
 
  assign w_cs2_wr	=	(r_wr_current_state == WRITE2) 						;
  assign w_we2		=	(r_wr_current_state == WRITE2) 						;
  assign w_addr2_wr	=	(r_wr_current_state == WRITE2) ? w_hor_cnt  : 'd0	;
  assign w_din2		=	(r_wr_current_state == WRITE2) ? r_data_dly : 'd0	;
 
  assign w_cs3_wr	=	(r_wr_current_state == WRITE3) 						;
  assign w_we3		=	(r_wr_current_state == WRITE3) 						;
  assign w_addr3_wr	=	(r_wr_current_state == WRITE3) ? w_hor_cnt  : 'd0	;
  assign w_din3		=	(r_wr_current_state == WRITE3) ? r_data_dly : 'd0	;
 
  assign w_cs4_wr	=	(r_wr_current_state == WRITE4) 						;
  assign w_we4		=	(r_wr_current_state == WRITE4) 						;
  assign w_addr4_wr	=	(r_wr_current_state == WRITE4) ? w_hor_cnt  : 'd0	;
  assign w_din4		=	(r_wr_current_state == WRITE4) ? r_data_dly : 'd0	;
 
  //------------------//
  //---MEM_read_FSM---//
  //------------------//
  always @(*) begin
    case(r_rd_current_state)
      IDLE		:	r_rd_next_state = 	(w_rd_fsm_start	)	? BUFFER1	: IDLE		;
      BUFFER1	:	r_rd_next_state = 	(w_line_buffer	)	? BUFFER2	: BUFFER1	;
      BUFFER2	:	r_rd_next_state = 	(w_line_buffer	)	? FIRST		: BUFFER2	;
      FIRST		:	r_rd_next_state = 	(w_hor_cnt_rst	)	? BLANK1	: FIRST		; //"w_hor_cnt_rst" is toggle when counter reach to hact or hblank
      BLANK1	:	r_rd_next_state = 	(w_hor_cnt_rst	)	? READ		: BLANK1	;
      READ		:	r_rd_next_state = 	(w_hor_cnt_rst	)	? BLANK2	: READ		;
      BLANK2	:	r_rd_next_state = 	(w_blank_read	)	? READ		: 
      									(w_last_read	)	? LAST		: BLANK2	;
      LAST		:	r_rd_next_state = 	(w_hor_cnt_rst	)	? IDLE		: LAST		;
      default	:	r_rd_next_state = 	IDLE										;
    endcase
  end
  
  assign w_rd_fsm_start	=  ((i_blur_mode_cap	||	i_mirror_mode_cap		) && i_den_sync);
  assign w_line_buffer	=	r_act_blank_sel	&&	(w_hor_cnt	==	r_hblank)				; //ref : hor_cnt (line num = 191)
  assign w_blank_read	=	w_line_buffer	&&	(w_ver_cnt	!=	r_vact	)				;
  assign w_last_read	=	w_line_buffer	&&	(w_ver_cnt	==	r_vact	)				;
  
  //-------------------------//
  //---MEM_read_FSM_output---//
  //-------------------------//
  assign w_rd_en	=	(!w_ver_cnt[1]	&&	!w_ver_cnt[0])	?	'hE	:			//'b1110
   						(!w_ver_cnt[1]	&&	 w_ver_cnt[0])	?	'hD	:			//'b1101
   						( w_ver_cnt[1]	&&	!w_ver_cnt[0])	?	'hB	:			//'b1011
   						( w_ver_cnt[1]	&&	 w_ver_cnt[0])	?	'h7	:	'h0;	//'b0111
  
  assign w_rd_sel	=	(!w_ver_cnt[1]	&&	!w_ver_cnt[0])	?	'h6	:			//'b0110
   						(!w_ver_cnt[1]	&&	 w_ver_cnt[0])	?	'hC	:			//'b1101
   						( w_ver_cnt[1]	&&	!w_ver_cnt[0])	?	'h9	:			//'b1001
   						( w_ver_cnt[1]	&&	 w_ver_cnt[0])	?	'h3	:	'h0;	//'b0011
  
  assign w_cs1_rd	=	((r_rd_current_state == READ)	&&	w_rd_en[0])	||	((r_rd_current_state ==	LAST)	&&	w_rd_sel[0]) ||	(r_rd_current_state	==	FIRST)	;
  assign w_cs2_rd	=	((r_rd_current_state == READ)	&&	w_rd_en[1])	||	((r_rd_current_state ==	LAST)	&&	w_rd_sel[1]) ||	(r_rd_current_state	==	FIRST)	;
  assign w_cs3_rd	=	((r_rd_current_state == READ)	&&	w_rd_en[2])	||	((r_rd_current_state ==	LAST)	&&	w_rd_sel[2])									;
  assign w_cs4_rd	=	((r_rd_current_state == READ)	&&	w_rd_en[3])	||	((r_rd_current_state ==	LAST)	&&	w_rd_sel[3])									;
  
  assign w_addr1_rd	=	(w_cs1_rd	&&	!i_mirror_mode_cap)	?	w_hor_cnt			:		
    					(w_cs1_rd	&&	 i_mirror_mode_cap)	?	r_hact - w_hor_cnt	:	'd0;	
  assign w_addr2_rd	=	(w_cs2_rd	&&	!i_mirror_mode_cap)	?	w_hor_cnt			:		
    					(w_cs2_rd	&&	 i_mirror_mode_cap)	?	r_hact - w_hor_cnt	:	'd0;	
  assign w_addr3_rd	=	(w_cs3_rd	&&	!i_mirror_mode_cap)	?	w_hor_cnt			:		
    					(w_cs3_rd	&&	 i_mirror_mode_cap)	?	r_hact - w_hor_cnt	:	'd0;	
  assign w_addr4_rd	=	(w_cs4_rd	&&	!i_mirror_mode_cap)	?	w_hor_cnt			:		
    					(w_cs4_rd	&&	 i_mirror_mode_cap)	?	r_hact - w_hor_cnt	:	'd0;	
  
  assign w_sel		=	(r_rd_current_state == FIRST)	?	'h3			:		
 						(r_rd_current_state == READ	)	?	w_rd_en		:	
    					(r_rd_current_state == LAST	)	?	w_rd_sel	:	'h0;	
  
  assign w_den		=	(r_rd_current_state == READ) ||	(r_rd_current_state == LAST) ||(r_rd_current_state == FIRST);
  
  
  //----------------//
  //---Output_F/F---//
  //----------------//
  always @(posedge I_CLK or negedge I_RSTN) begin
    if(!I_RSTN) begin
      r_cs1			<=	'h0	;
      r_we1			<=	'h0	;
      r_addr1		<=	'h0	;
      r_din1		<=	'h0	;
      r_cs2			<=	'h0	;
      r_we2			<=	'h0	;
      r_addr2		<=	'h0	;
      r_din2		<=	'h0	;
      r_cs3			<=	'h0	;
      r_we3			<=	'h0	;
      r_addr3		<=	'h0	;
      r_din3		<=	'h0	;
      r_cs4			<=	'h0	;
      r_we4			<=	'h0	;
      r_addr4		<=	'h0	;
      r_din4		<=	'h0	;
      r_vact_state	<=	'h0	;
      r_hor_cnt		<=	'h0	;
      r_sel			<=	'h0	;
      r_den			<=	'h0	;
    end
    else begin
      r_cs1			<=	w_cs1_wr 	| w_cs1_rd	;
      r_we1			<=	w_we1					;
      r_addr1		<=	w_addr1_wr 	| w_addr1_rd;
      r_din1		<=	w_din1					;
      r_cs2			<=	w_cs2_wr 	| w_cs2_rd	;
      r_we2			<=	w_we2					;
      r_addr2		<=	w_addr2_wr 	| w_addr2_rd;
      r_din2		<=	w_din2					;
      r_cs3			<=	w_cs3_wr 	| w_cs3_rd	;
      r_we3			<=	w_we3					;
      r_addr3		<=	w_addr3_wr 	| w_addr3_rd;
      r_din3		<=	w_din3					;
      r_cs4			<=	w_cs4_wr 	| w_cs4_rd	;
      r_we4			<=	w_we4					;
      r_addr4		<=	w_addr4_wr 	| w_addr4_rd;
      r_din4		<=	w_din4					;
      r_vact_state	<=	r_rd_current_state		;
      r_hor_cnt		<=	w_hor_cnt				;
      r_sel			<=	w_sel					;
      r_den			<=	w_den					;
    end
  end
  
     assign o_cs1			=	r_cs1		;
     assign o_we1			=	r_we1		;
     assign o_addr1			=	r_addr1		;
     assign o_din1			=	r_din1		;
     assign o_cs2			=	r_cs2		;
     assign o_we2			=	r_we2		;
     assign o_addr2			=	r_addr2		;
     assign o_din2			=	r_din2		;
     assign o_cs3			=	r_cs3		;
     assign o_we3			=	r_we3		;
     assign o_addr3			=	r_addr3		;
     assign o_din3			=	r_din3		;
     assign o_cs4			=	r_cs4		;
     assign o_we4			=	r_we4		;
     assign o_addr4			=	r_addr4		;
     assign o_din4			=	r_din4		;
     assign o_vact_state	=	r_vact_state;
     assign o_hor_cnt		=	r_hor_cnt	;
     assign o_sel			=	r_sel		;
     assign o_den			=	r_den		;
  
endmodule