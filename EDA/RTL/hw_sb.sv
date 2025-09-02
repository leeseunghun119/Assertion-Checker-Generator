`uvm_analysis_imp_decl(_in_hw)
`uvm_analysis_imp_decl(_out_hw)
//
parameter V   = 10 ;
parameter H   = 10 ;
parameter ON  = 1  ;
parameter OFF = 0  ;

typedef struct{
  byte                M, N;
  int                 width;
  int                 height;
  int                 max;
  int                 pixels[V-1][H-1];
} PPMImage;

typedef struct{
  int					filter[2][2];	
} Filter;

import "DPI-C" context function int  fnRead(input string fileNm, output PPMImage img);
import "DPI-C" context function void fnClose(input PPMImage img);
import "DPI-C" context function int  fnWrite(input string fileNm, output PPMImage img);
import "DPI-C" context function int  fnBlur(input PPMImage img_org, output PPMImage img_blur, input Filter filter, input Filter filter_wr, input int weight_wr_mode, input int blur_mode, input int mirror_mode, input int w1, input int w2, input int w3, input int w4, input int w5, input int w6, input int w7, input int w8, input int w9);
//

class hw_sb_c extends uvm_scoreboard;
  `uvm_component_utils(hw_sb_c)

  uvm_analysis_imp_in_hw#(hw_mon_pkt_c, hw_sb_c) in_hw_imp_port;// TLM implementation port
  uvm_analysis_imp_out_hw#(hw_mon_pkt_c, hw_sb_c) out_hw_imp_port;// TLM implementation port

  virtual interface hw_if vif;
  
  event aaassa;
  
  bit [7:0] ref_data[$]		;
  //bit [7:0] rtl_data[$]		;
  bit [7:0] data_in[$]		;
  bit [7:0] data_out[$]		;
  int match_cnt				;
  int mismatch_cnt			;
  string golden_file_path	;
  string info[$]			;
  string tmp_string	  		;
  int i						;
  int fp 			  		;
  int dummy			  		;
  int tmp_value		  		;
  
  PPMImage IMG_ORG	  	  	;
  PPMImage IMG_RE 	  	  	;
  PPMImage IMG_BYPASS 	  	;
  PPMImage IMG_MIRROR 	  	;
  PPMImage IMG_BLUR	   	  	;
  PPMImage IMG_BLUR_MIRROR  ;
  PPMImage IMG_CUSTOM	    ;
  
  Filter filter				;
  Filter filter_wr			;  	    
  
  function new(string name, uvm_component parent);
	super.new(name, parent);
    
    in_hw_imp_port = new("in_hw_imp_port", this);
    out_hw_imp_port = new("out_hw_imp_port", this);
    
  endfunction
 
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
  endfunction
  
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if(!uvm_config_db#(virtual hw_if)::get(this, "", "vif", vif)) begin
      `uvm_fatal(get_full_name(), {"Virtual interface must be set for :", get_full_name(), ".vif"})
    end
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    
    //rtl_data.delete();
    
    forever begin
      fork
      	golden_image();
     	compare_data();
      join
    end
  endtask
  
  virtual task compare_data();
    bit [7:0] rtl_data;
    //wait(rtl_data.size() > 0 && rtl_data.size() == ref_data.size());
    wait(data_out.size() > 0 && data_out.size() == ref_data.size());
    foreach(ref_data[i])begin
    	rtl_data = data_out.pop_front();
      if(ref_data[i] == rtl_data)begin
    		match_cnt++;
        `uvm_info(get_type_name(), $sformatf("DATA MATCH REF = %d [%d] OUT = %d",ref_data[i], i, rtl_data), UVM_LOW)
    	end
    	else begin
      		mismatch_cnt++;
          `uvm_error(get_type_name(), $sformatf("DATA MISMATCH REF = %d [%d] OUT = %d",ref_data[i], i, rtl_data))
    	end
    end
  endtask
  
  virtual function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    `uvm_info(get_type_name(), $sformatf("###COMPARE RESULT###"), UVM_LOW)
    `uvm_info(get_type_name(), $sformatf("MATCH COUNT = %0d",match_cnt), UVM_LOW)
    `uvm_info(get_type_name(), $sformatf("MISMATCH COUNT = %0d",mismatch_cnt), UVM_LOW)
    `uvm_info(get_type_name(), $sformatf("####################"), UVM_LOW)
    
  endfunction: report_phase
  
  task golden_image();
    
    ref_data.delete();
    
    @(posedge vif.O_DEN);
    
    fnRead("image.pgm", IMG_ORG);
    fnBlur(IMG_ORG, IMG_BLUR, filter, filter_wr, 0, 1, 0, 1, 2, 1, 2, 4, 2, 1, 2, 1);
    fnWrite("blur_image.pgm", IMG_BLUR);
    fnClose(IMG_BLUR);
    fnClose(IMG_ORG);    
    
    //golden_file_path = $sformatf("blur_result.pgm");
    golden_file_path = $sformatf("blur_image.pgm");
    
    fp = $fopen($sformatf("%s", golden_file_path), "r");
    if(fp == 0) begin
      `uvm_info(get_full_name(), $psprintf("Golden Image Path Fail!!"), UVM_LOW)
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
        ref_data.push_back(tmp_value);
        i++;
      end
    end
    $fclose(fp);
    
  endtask
  
  virtual function void write_in_hw (hw_mon_pkt_c pkt);
    if(pkt.I_VSYNC)begin
      data_in.delete();
    end else if(pkt.I_DEN)begin
      data_in.push_back(pkt.I_DATA);
    end
  endfunction
  
  virtual function void write_out_hw (hw_mon_pkt_c pkt);
    if(pkt.O_VSYNC)begin
      data_out.delete();
    end else if(pkt.O_DEN)begin
      data_out.push_back(pkt.O_DATA);
    end
  endfunction
  
endclass