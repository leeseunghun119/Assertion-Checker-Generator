// Base sequence 

class hw_base_vseq_c extends uvm_sequence;
  `uvm_object_utils_begin(hw_base_vseq_c)
  `uvm_object_utils_end
  
  `uvm_declare_p_sequencer(vseqr_c)
  
  function new (string name = "hw_base_vseq_c"); 
    super.new(name);
  endfunction

  virtual task pre_body();
    super.pre_body();
    
    if (starting_phase != null) begin
      `uvm_info(get_type_name(), $sformatf("Raise objection"), UVM_LOW)
      starting_phase.raise_objection(this, get_type_name()); // raise an objection    
    end
  endtask
  
  virtual task body();
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
endclass

    
// Test sequence(virtual sequence)
class hw_basic_vseq_c extends hw_base_seq_c;
  `uvm_object_utils(hw_basic_vseq_c)
  
  //hw_drv_pkt_c	pkt;
  hw_seq_item_c	rnd_item;
  hm_video_frame_seq_c frame_seq;
  uvm_status_e 	status;
  
  int 			wdata;
  int 			rdata;
  
  
  function new (string name = "hw_basic_vseq_c");
    super.new(name);
    rnd_item = new();
    frame_seq = new();
  endfunction  
  
  virtual task pre_body();
    super.pre_body();
    `uvm_info(get_type_name(), $sformatf("pre_body() starts.."), UVM_LOW)
  endtask
  
  virtual task body();
    super.body();
    `uvm_info(get_type_name(), $sformatf("Start Test"), UVM_LOW)
    
    wait_for_reset_release();
    
    
    assert(rnd_item.randomize() with {
      	//i_enable == 1'b1;
      });
    rnd_item.sprint();
    
    

    $display("Start sfr setting..");
    
    p_sequencer.m_reg_block.my_reg1.vsw.write(status, rnd_item.VSW);  //vsw
    p_sequencer.m_reg_block.my_reg1.hsw.write(status, rnd_item.HSW);  //hsw   
    
    //`uvm_info(get_full_name(), $psprintf("VSW = %0d",rnd_item.VSW), UVM_LOW)
    
    p_sequencer.m_reg_block.my_reg2.vbp.write(status, rnd_item.VBP);  //vbp   
    p_sequencer.m_reg_block.my_reg2.hbp.write(status, rnd_item.HBP);  //hbp    
    
    p_sequencer.m_reg_block.my_reg3.vact.write(status, rnd_item.VACT);  //vact  
    p_sequencer.m_reg_block.my_reg3.hact.write(status, rnd_item.HACT);  //hact      
    
    p_sequencer.m_reg_block.my_reg4.vfp.write(status, rnd_item.VFP);  //vfp       
    p_sequencer.m_reg_block.my_reg4.hfp.write(status, rnd_item.HFP);  //hfp    
    
    p_sequencer.m_reg_block.my_reg5.weight_wr_mode.write(status, rnd_item.MODE_WEIGHT_WR);  //weight_wr_mode
    p_sequencer.m_reg_block.my_reg5.mirror_mode.write(status, rnd_item.MODE_MIRROR);  //mirror_mode
    p_sequencer.m_reg_block.my_reg5.blur_mode.write(status, rnd_item.MODE_BLUR);  //blur_mode
    
    p_sequencer.m_reg_block.my_reg6.w1.write(status, rnd_item.WEIGHT1);  //w1  
    p_sequencer.m_reg_block.my_reg6.w2.write(status, rnd_item.WEIGHT2);  //w2
    p_sequencer.m_reg_block.my_reg6.w3.write(status, rnd_item.WEIGHT3);  //w3      
    
    p_sequencer.m_reg_block.my_reg7.w4.write(status, rnd_item.WEIGHT4);  //w4  
    p_sequencer.m_reg_block.my_reg7.w5.write(status, rnd_item.WEIGHT5);  //w5  
    p_sequencer.m_reg_block.my_reg7.w6.write(status, rnd_item.WEIGHT6);  //w6      
    
    p_sequencer.m_reg_block.my_reg8.w7.write(status, rnd_item.WEIGHT7);  //w7  
    p_sequencer.m_reg_block.my_reg8.w8.write(status, rnd_item.WEIGHT8);  //w8  
    p_sequencer.m_reg_block.my_reg8.w9.write(status, rnd_item.WEIGHT9);  //w9             
    
    //p_sequencer.m_reg_block.my_reg1.vsw.write(status, 'd10);  //vsw
    //p_sequencer.m_reg_block.my_reg1.hsw.write(status, 'd10);  //hsw   
    //
    //p_sequencer.m_reg_block.my_reg2.vbp.write(status, 'd10);  //vbp   
    //p_sequencer.m_reg_block.my_reg2.hbp.write(status, 'd10);  //hbp    
    //
    //p_sequencer.m_reg_block.my_reg3.vact.write(status, 'd20);  //vact  
    //p_sequencer.m_reg_block.my_reg3.hact.write(status, 'd20);  //hact      
    //
    //p_sequencer.m_reg_block.my_reg4.vfp.write(status, 'd10);  //vfp       
    //p_sequencer.m_reg_block.my_reg4.hfp.write(status, 'd10);  //hfp    
    //
    //p_sequencer.m_reg_block.my_reg5.weight_wr_mode.write(status, 'd0);  //weight_wr_mode
    //p_sequencer.m_reg_block.my_reg5.mirror_mode.write(status, 'd1);  //mirror_mode
    //p_sequencer.m_reg_block.my_reg5.blur_mode.write(status, 'd0);  //blur_mode
    //
    //p_sequencer.m_reg_block.my_reg6.w1.write(status, 'd1);  //w1  
    //p_sequencer.m_reg_block.my_reg6.w2.write(status, 'd1);  //w2
    //p_sequencer.m_reg_block.my_reg6.w3.write(status, 'd1);  //w3      
    //
    //p_sequencer.m_reg_block.my_reg7.w4.write(status, 'd1);  //w4  
    //p_sequencer.m_reg_block.my_reg7.w5.write(status, 'd1);  //w5  
    //p_sequencer.m_reg_block.my_reg7.w6.write(status, 'd1);  //w6      
    //
    //p_sequencer.m_reg_block.my_reg8.w7.write(status, 'd1);  //w7  
    //p_sequencer.m_reg_block.my_reg8.w8.write(status, 'd1);  //w8  
    //p_sequencer.m_reg_block.my_reg8.w9.write(status, 'd1);  //w9             
    
  

    $display("End sfr setting..");

    
    

    
    
    
    
    `uvm_info(get_type_name(), $sformatf("FRAME Sequence Started.."), UVM_LOW)
    frame_seq.rnd_item = rnd_item;
    `uvm_send(frame_seq)
    `uvm_info(get_type_name(), $sformatf("FRAME Sequence ended.."), UVM_LOW)
    /*
    `uvm_create_on(pkt, p_sequencer.hw_seqr)
    repeat(20) begin
      assert(pkt.randomize() with {
      	//i_enable == 1'b1;
      });
      `uvm_info(get_type_name(), $sformatf("[%2d]Send Packets", $time), UVM_LOW)
      `uvm_send(pkt);
    end
    */

    //assert(pkt.randomize() with {
      //i_cf == 2'b0;
      //i_enable == 1'b0;
      //i_data_in0 == 16'h0;
      //i_data_in1 == 16'h0;
    //});
    /*
    `uvm_info(get_type_name(), $sformatf("[%2d]Send Packets", $time), UVM_LOW)
    `uvm_send(pkt);    
      
    */
    repeat(100) @(posedge p_sequencer.vif.CLK);
    `uvm_info(get_type_name(), $sformatf("Finish Test"), UVM_LOW)
  endtask
  
  
  virtual task post_body();
    super.post_body();
    `uvm_info(get_type_name(), $sformatf("post_body() starts.."), UVM_LOW)
  endtask
  
  virtual task wait_for_reset_release();
    @(posedge p_sequencer.vif.RSTN);
    `uvm_info(get_type_name(), $sformatf("System reset is released."), UVM_LOW)
    repeat(10) @(posedge p_sequencer.vif.CLK);
    `uvm_info(get_type_name(), $sformatf("Wait for 10 clock cycles."), UVM_LOW)
  endtask
  
endclass

