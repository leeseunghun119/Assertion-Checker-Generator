`define MAX_SIZE 6
`define DATA_SIZE 8

class hw_seq_item_c extends uvm_sequence_item;

  rand bit [ `MAX_SIZE-1:0] HSW				;
  rand bit [ `MAX_SIZE-1:0] HBP				;
  rand bit [ `MAX_SIZE-1:0] HACT			;
  rand bit [ `MAX_SIZE-1:0] HFP				;
  rand bit [ `MAX_SIZE-1:0] VSW				;
  rand bit [ `MAX_SIZE-1:0] VBP			   	;
  rand bit [ `MAX_SIZE-1:0] VACT		   	;
  rand bit [ `MAX_SIZE-1:0] VFP			   	;
  
  rand bit 				    MODE_BLUR      	;
  rand bit 				    MODE_MIRROR    	;
  rand bit 				    MODE_WEIGHT_WR 	;
  bit	   [		   2:0] MODE			;
 
  rand bit [		   3:0] WEIGHT1			;
  rand bit [		   3:0] WEIGHT2			;
  rand bit [		   3:0] WEIGHT3			;
  rand bit [		   3:0] WEIGHT4			;
  rand bit [		   3:0] WEIGHT5			;
  rand bit [		   3:0] WEIGHT6			;
  rand bit [		   3:0] WEIGHT7			;
  rand bit [		   3:0] WEIGHT8			;
  rand bit [		   3:0] WEIGHT9			;
  
  rand bit [`DATA_SIZE-1:0] I_DATA			; 
  rand bit [`DATA_SIZE-1:0] FRAME			;
  
  bit 	   [		  15:0] HTOT			;
  bit 	   [		  15:0] VTOT			;
  
  `uvm_object_utils_begin(hw_seq_item_c)
  	`uvm_field_int(HSW				, 	UVM_DEFAULT)
  	`uvm_field_int(HBP				, 	UVM_DEFAULT)
  	`uvm_field_int(HACT				,	UVM_DEFAULT)
  	`uvm_field_int(HFP				, 	UVM_DEFAULT)
  	`uvm_field_int(VSW				, 	UVM_DEFAULT)
  	`uvm_field_int(VBP				, 	UVM_DEFAULT)
  	`uvm_field_int(VACT				, 	UVM_DEFAULT)
  	`uvm_field_int(VFP				, 	UVM_DEFAULT)
  	`uvm_field_int(VFP				, 	UVM_DEFAULT)  
  	`uvm_field_int(MODE_BLUR		, 	UVM_DEFAULT)
  	`uvm_field_int(MODE_MIRROR 		, 	UVM_DEFAULT)
    `uvm_field_int(MODE_WEIGHT_WR	, 	UVM_DEFAULT)
  	`uvm_field_int(WEIGHT1			, 	UVM_DEFAULT)
  	`uvm_field_int(WEIGHT2			, 	UVM_DEFAULT)
  	`uvm_field_int(WEIGHT3			, 	UVM_DEFAULT)
  	`uvm_field_int(WEIGHT4			, 	UVM_DEFAULT)
  	`uvm_field_int(WEIGHT5			, 	UVM_DEFAULT)
  	`uvm_field_int(WEIGHT6			, 	UVM_DEFAULT)
  	`uvm_field_int(WEIGHT7			, 	UVM_DEFAULT)
  	`uvm_field_int(WEIGHT8			, 	UVM_DEFAULT)
  	`uvm_field_int(WEIGHT9			, 	UVM_DEFAULT)
  	`uvm_field_int(I_DATA			, 	UVM_DEFAULT)
  	`uvm_field_int(FRAME			, 	UVM_DEFAULT)
  `uvm_object_utils_end
  
  function new (string name="hw_seq_item_c");
	super.new(name);
  endfunction
  
  /*
  function void debug_display();
    `uvm_info(get_full_name(), $psprintf("================================================"), UVM_LOW)
    `uvm_info(get_full_name(), $psprintf("================================================"), UVM_LOW)
    `uvm_info(get_full_name(), $psprintf("VTOTAL = %0d",VSW+VBP+VACT+VFP), UVM_LOW)
  endfunction
  */
  
  constraint frame_const{
    //FRAME inside{[2:3]};
    FRAME == 2;
  }
  
  constraint hsw_const{
    HSW inside {5};
  }
  
  constraint hbp_const{
    HBP == 5;
  }
  
  constraint hact_const{
    HACT == 10;
  }
  
  constraint hfp_const{
    HFP == 5;
  }
  
  constraint vsw_const{
    VSW == 1;
  }
  
  constraint vbp_const{
    VBP == 1;
  }
  
  constraint vact_const{
    VACT == 10;
  }
  
  constraint vfp_const{
    VFP == 1;  // VFP >1
  }
    
  constraint mode_const{  
    MODE_BLUR      == 1;
    MODE_MIRROR    == 0;
    MODE_WEIGHT_WR == 0;
  }
  
  constraint weight_const{  
    WEIGHT1 == 1;
    WEIGHT2 == 2;
    WEIGHT3 == 1;
    WEIGHT4 == 2;
    WEIGHT5 == 4;
    WEIGHT6 == 2;
    WEIGHT7 == 1;
    WEIGHT8 == 2;
    WEIGHT9 == 1;
  }
  
  
  function void pre_randomize();
  endfunction: pre_randomize
  
  function void post_randomize();
    HTOT = HSW + HBP + HACT + HFP;
 	VTOT = VSW + VBP + VACT + VFP;
    MODE = {MODE_BLUR, MODE_MIRROR, MODE_WEIGHT_WR} ;
    
    `uvm_info(get_full_name(), $psprintf("========================================================================"), UVM_LOW)
    `uvm_info(get_full_name(), $psprintf("========================================================================"), UVM_LOW)
    `uvm_info(get_full_name(), $psprintf("====================="), UVM_LOW)
    `uvm_info(get_full_name(), $psprintf("== VIDEO SYNC INFO =="), UVM_LOW)
    `uvm_info(get_full_name(), $psprintf("====================="), UVM_LOW)
    `uvm_info(get_full_name(), $psprintf("FRAME = %0d",FRAME), UVM_LOW)
    `uvm_info(get_full_name(), $psprintf("VTOTAL = %0d",VTOT), UVM_LOW)
    `uvm_info(get_full_name(), $psprintf("HTOTAL = %0d",HTOT), UVM_LOW)
    `uvm_info(get_full_name(), $psprintf("HSW = %0d",HSW), UVM_LOW)
    `uvm_info(get_full_name(), $psprintf("HBP = %0d",HBP), UVM_LOW)
    `uvm_info(get_full_name(), $psprintf("HACT = %0d",HACT), UVM_LOW)
    `uvm_info(get_full_name(), $psprintf("HFP = %0d",HFP), UVM_LOW)
    `uvm_info(get_full_name(), $psprintf("VSW = %0d",VSW), UVM_LOW)
    `uvm_info(get_full_name(), $psprintf("VBP = %0d",VBP), UVM_LOW)
    `uvm_info(get_full_name(), $psprintf("VACT = %0d",VACT), UVM_LOW)
    `uvm_info(get_full_name(), $psprintf("VFP = %0d",VFP), UVM_LOW)
    `uvm_info(get_full_name(), $psprintf("====================="), UVM_LOW)
    `uvm_info(get_full_name(), $psprintf("===== MODE INFO ====="), UVM_LOW)
    `uvm_info(get_full_name(), $psprintf("====================="), UVM_LOW)
    if 		(MODE == 3'b100) `uvm_info(get_full_name(), $psprintf("MODE = BLUR"), UVM_LOW)
    else if (MODE == 3'b010) `uvm_info(get_full_name(), $psprintf("MODE = MIRROR"), UVM_LOW)
    else if (MODE == 3'b001) `uvm_info(get_full_name(), $psprintf("MODE = WEIGHT_WR"), UVM_LOW)
    else					 `uvm_info(get_full_name(), $psprintf("PLEASE SET MODE"), UVM_LOW) 
      
    `uvm_info(get_full_name(), $psprintf("====================="), UVM_LOW)
    `uvm_info(get_full_name(), $psprintf("=== FILTER WEIGHT ==="), UVM_LOW)
    `uvm_info(get_full_name(), $psprintf("====================="), UVM_LOW)
    `uvm_info(get_full_name(), $psprintf("||  %0d %0d %0d  ||", WEIGHT1, WEIGHT2, WEIGHT3), UVM_LOW)
    `uvm_info(get_full_name(), $psprintf("||  %0d %0d %0d  ||", WEIGHT4, WEIGHT5, WEIGHT6), UVM_LOW)
    `uvm_info(get_full_name(), $psprintf("||  %0d %0d %0d  ||", WEIGHT7, WEIGHT8, WEIGHT9), UVM_LOW)
    `uvm_info(get_full_name(), $psprintf("====================="), UVM_LOW)
    `uvm_info(get_full_name(), $psprintf("========================================================================"), UVM_LOW)
    `uvm_info(get_full_name(), $psprintf("========================================================================"), UVM_LOW)
  endfunction: post_randomize
  
endclass
