class hw_base_seq_c extends uvm_sequence;
  `uvm_object_utils_begin(hw_base_seq_c)
  `uvm_object_utils_end
  
  `uvm_declare_p_sequencer(vseqr_c)
  
  hw_drv_pkt_c	pkt;
  hw_seq_item_c rnd_item;
  
  function new (string name = "hw_base_seq_c"); 
    super.new(name);
    rnd_item = new();
  endfunction

  virtual task pre_body();
    super.pre_body();
    
    if (starting_phase != null) begin
      `uvm_info(get_type_name(), $sformatf("Raise objection"), UVM_LOW)
      starting_phase.raise_objection(this, get_type_name()); // raise an objection    
    end
  endtask
  
  virtual task body();
    `uvm_create_on(pkt, p_sequencer.hw_seqr)
    //super.body(); // warning) Body definitition undefined.
    //..
  endtask
  
  virtual task post_body();
    super.post_body();
    
    if (starting_phase != null) begin
      `uvm_info(get_type_name(), $sformatf("Drop objection"), UVM_LOW)
      starting_phase.drop_objection(this, get_type_name()); // drop an objection
    end
  endtask
  task send_sync_value(hw_seq_item_c r_item);
  
  endtask
endclass

class hm_video_load_seq_c extends hw_base_seq_c;
  `uvm_object_utils(hm_video_load_seq_c)
   
  int fp 			  		;
  string video_file_path	;
  string info[$]	  		;
  string tmp_string	  		;
  
  int dummy			  		;
  int tmp_value		  		;
  int data_value[$]	  		;
  int i				  		;
  int hactive		  		;
  int vactive		  		;
  int w1			  		;
  int w2			  		;
  int w3			  		;		 
  int w4			  		;
  int w5			  		;
  int w6			  		;
  int w7			  		;
  int w8			  		;
  int w9			  		;
  int mode_blur		  		;
  int mode_mirror	  		;
  int mode_weight_wr  		;
  
  
  function new (string name = "hm_video_load_seq_c");
    super.new(name);
  endfunction  
  
  virtual task body();
    
    super.body();
    
    info.delete();
    data_value.delete();
    
    `uvm_info(get_full_name(), $psprintf("IMAGE DATA LOAD START"), UVM_LOW)

    
    video_file_path = $sformatf("image.pgm");
    
    fp = $fopen($sformatf("%s", video_file_path), "r");
    if(fp == 0) begin
      `uvm_info(get_full_name(), $psprintf("Video Path Fail!!"), UVM_LOW)
      $finish;
    end
    i = 0;
    while(!$feof(fp)) begin
      if(i<4)begin
        dummy = $fscanf(fp, "%s\n", tmp_string);
        info.push_back(tmp_string);
        i++;
      end
      else begin
        dummy = $fscanf(fp, "%d\n", tmp_value);
        data_value.push_back(tmp_value);
        i++;
      end
    end
    $fclose(fp);
    
    `uvm_info(get_full_name(), $psprintf("Video data load done"), UVM_LOW)
    //`uvm_info(get_full_name(), $psprintf("Video file path : %s", video_file_path), UVM_LOW)
    //`uvm_info(get_full_name(), $psprintf("Video data ppm format : %s", info[0]), UVM_LOW)
    //`uvm_info(get_full_name(), $psprintf("Video data ppm image H size : %s", info[1]), UVM_LOW)
    //`uvm_info(get_full_name(), $psprintf("Video data ppm image V size : %s", info[2]), UVM_LOW)
    //`uvm_info(get_full_name(), $psprintf("Video data ppm pixel max value : %s", info[3]), UVM_LOW)
    //`uvm_info(get_full_name(), $psprintf("Video pixel num : %d", data_value.size()), UVM_LOW)
    
  endtask
  
endclass : hm_video_load_seq_c

class hm_video_hsw_seq_c extends hw_base_seq_c;
  `uvm_object_utils(hm_video_hsw_seq_c)
  
  bit sig_vsync;
  
  function new (string name = "hm_video_hsw_seq_c");
    super.new(name);
  endfunction  
  
  virtual task body();
    super.body();
    //`uvm_info(get_full_name(), $psprintf("HSW = %0d",rnd_item.HSW), UVM_LOW)
    for(int i=1; i<=rnd_item.HSW; i++)begin
    pkt.I_VSYNC =sig_vsync;
    pkt.I_HSYNC =1'b1;
    send_sync_value(rnd_item);
    `uvm_send(pkt)
    end
  endtask
  
endclass : hm_video_hsw_seq_c

class hm_video_hbp_seq_c extends hw_base_seq_c;
  `uvm_object_utils(hm_video_hbp_seq_c)
  
  bit sig_vsync;
  
  function new (string name = "hm_video_hbp_seq_c");
    super.new(name);
  endfunction  
  
  virtual task body();
    super.body();
    for(int i=1; i<=rnd_item.HBP; i++)begin
    pkt.I_VSYNC =sig_vsync;
    pkt.I_HSYNC =1'b0;
    send_sync_value(rnd_item);
    `uvm_send(pkt)
    end
  endtask
  
endclass : hm_video_hbp_seq_c

class hm_video_hact_seq_c extends hw_base_seq_c;
  `uvm_object_utils(hm_video_hact_seq_c)
  
  hm_video_load_seq_c video_load ;
  
  bit sig_vsync;
  bit sig_den;
  bit [15:0] cnt_line;
  
  function new (string name = "hm_video_hact_seq_c");
    super.new(name);
    video_load=new();
  endfunction  
  
  virtual task body();
    super.body();
    pkt.I_DEN = sig_den;
    `uvm_do(video_load)
    
    if(sig_den == 'b1)begin
      	for(int i=1; i<=rnd_item.HACT; i++)begin
          	pkt.I_DATA = video_load.data_value[(cnt_line*rnd_item.HACT)+(i-1)];
    		send_sync_value(rnd_item);
        	`uvm_send(pkt)
        end
    end
    else begin
    	for(int i=1; i<=rnd_item.HACT; i++)begin
      	  pkt.I_VSYNC = sig_vsync;
      	  pkt.I_HSYNC = 'b0;
          send_sync_value(rnd_item);
      	  `uvm_send(pkt)
    	end
    end
  endtask
  
endclass : hm_video_hact_seq_c

class hm_video_hfp_seq_c extends hw_base_seq_c;
  `uvm_object_utils(hm_video_hfp_seq_c)
  
  bit sig_vsync;
  bit sig_den;
  
  function new (string name = "hm_video_hfp_seq_c");
    super.new(name);
  endfunction  
  
  virtual task body();
    super.body();
    //pkt.DE = 0;
    for(int i=1; i<=rnd_item.HFP; i++)begin
    pkt.I_VSYNC =sig_vsync;
    pkt.I_HSYNC = 'b0;
    pkt.I_DEN   = 'b0;
    pkt.I_DATA  = 'h0;
    send_sync_value(rnd_item);
    `uvm_send(pkt)
    end
  endtask
  
endclass : hm_video_hfp_seq_c

class hm_video_line_seq_c extends hw_base_seq_c;
  `uvm_object_utils(hm_video_line_seq_c)
  
 	hm_video_hsw_seq_c hsw_seq; 
 	hm_video_hbp_seq_c hbp_seq; 
 	hm_video_hact_seq_c hact_seq; 
 	hm_video_hfp_seq_c hfp_seq; 
  	
  	bit sig_vsync;
  	bit sig_den;
  	bit [15:0] cnt_line;
  
  function new (string name = "hm_video_bline_seq_c");
    super.new(name);
    hsw_seq = new();
    hbp_seq = new();
    hact_seq = new();
    hfp_seq = new();
  endfunction  
  
  virtual task body();
    
    hsw_seq.sig_vsync  = sig_vsync;
    hbp_seq.sig_vsync  = sig_vsync;
    hact_seq.sig_vsync = sig_vsync;
    hact_seq.sig_den   = sig_den;
    hfp_seq.sig_vsync  = sig_vsync;
    
    hsw_seq.rnd_item  = rnd_item;
    hbp_seq.rnd_item  = rnd_item;
    hact_seq.rnd_item = rnd_item;
    hfp_seq.rnd_item  = rnd_item;
    
    hact_seq.cnt_line = cnt_line;
    
    //`uvm_info(get_type_name(), $sformatf("HSW Sequence Started.."), UVM_LOW)
    `uvm_send(hsw_seq)
    //`uvm_info(get_type_name(), $sformatf("HBP Sequence Started.."), UVM_LOW)
    `uvm_send(hbp_seq)
    //`uvm_info(get_type_name(), $sformatf("HACT Sequence Started.."), UVM_LOW)
    `uvm_send(hact_seq)
    //`uvm_info(get_type_name(), $sformatf("HFP Sequence Started.."), UVM_LOW)
    `uvm_send(hfp_seq)
    
  endtask
  
endclass : hm_video_line_seq_c


class hm_video_frame_seq_c extends hw_base_seq_c;
  `uvm_object_utils(hm_video_frame_seq_c)
  
 	hm_video_line_seq_c line_seq; 
  	bit line_delay = 0;
  
  function new (string name = "hm_video_manual_seq_c");
    super.new(name);
    line_seq = new();
  endfunction  
  
  virtual task body();
   	
    line_seq.rnd_item = rnd_item;
    for(int k=0; k<rnd_item.FRAME; k++)begin
      if(line_delay) begin
        for(int i=1; i<=2; i++)begin
          `uvm_info(get_type_name(), $sformatf("LINE_DELAY %d", i), UVM_LOW)
          line_seq.sig_vsync = 0;
          line_seq.sig_den = 0;
          `uvm_send(line_seq)
        end
      end
      //vertical sync width
      //`uvm_info(get_type_name(), $sformatf("VSW Sequence Started.."), UVM_LOW)
      for(int i=1; i<=rnd_item.VSW; i++)begin
        line_seq.sig_vsync = 1;
        line_seq.sig_den = 0;
        line_seq.cnt_line = 0;
        `uvm_send(line_seq)
      end
      //vertical backporch
      //`uvm_info(get_type_name(), $sformatf("VBP Sequence Started.."), UVM_LOW)
      for(int i=1; i<=rnd_item.VBP; i++)begin
        line_seq.sig_vsync = 0;
        line_seq.sig_den = 0;
        line_seq.cnt_line = 0;
        `uvm_send(line_seq)
      end
      //vertical active
      //`uvm_info(get_type_name(), $sformatf("VACT Sequence Started.."), UVM_LOW)
      for(int i=1; i<=rnd_item.VACT; i++)begin
        line_seq.sig_vsync = 0;
        line_seq.sig_den = 1;
        `uvm_send(line_seq)
        line_seq.cnt_line++;
      end
      //vertical frontporch
      //`uvm_info(get_type_name(), $sformatf("VFP Sequence Started.."), UVM_LOW)
      for(int i=1; i<=rnd_item.VFP; i++)begin
        line_seq.sig_vsync = 0;
        line_seq.sig_den = 0;
        line_seq.cnt_line = 0;
        `uvm_send(line_seq)
      end
    end
    
    // FOR LAST HSYNC
    for(int i=1; i<=rnd_item.VBP; i++)begin
    	line_seq.sig_vsync = 0;
    	line_seq.sig_den = 0;
    	line_seq.cnt_line = 0;
    	`uvm_send(line_seq)
    end
    
  endtask
  
endclass : hm_video_frame_seq_c



