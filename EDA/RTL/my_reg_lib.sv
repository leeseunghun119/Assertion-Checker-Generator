//------------------------------------
// my_reg1                            
//------------------------------------
class my_reg1_c extends uvm_reg;
  
  `uvm_object_utils(my_reg1_c)
  
  // Field
  rand uvm_reg_field vsw; 
  rand uvm_reg_field hsw; 
  
  // Constructor
  function new(string name = "my_reg1_c");
    super.new(name, 32, UVM_NO_COVERAGE);
  endfunction
  
  // build
  virtual function void build();
    // create object instance
    this.vsw = uvm_reg_field::type_id::create("vsw");
    this.hsw = uvm_reg_field::type_id::create("hsw");    
   
    // Configure  
    this.vsw.configure (this, 16, 16, "RW", 0, 1'b0, 0, 1, 1);
    this.hsw.configure (this, 16, 0, "RW", 0, 1'b0, 0, 1, 1);  
    
  endfunction
  
endclass



//------------------------------------
// my_reg2                            
//------------------------------------
class my_reg2_c extends uvm_reg;
  
  `uvm_object_utils(my_reg2_c)
  
  // Field
  rand uvm_reg_field vbp; 
  rand uvm_reg_field hbp; 
  
  // Constructor
  function new(string name = "my_reg2_c");
    super.new(name, 32, UVM_NO_COVERAGE);
  endfunction
  
  // build
  virtual function void build();
    // create object instance
    this.vbp = uvm_reg_field::type_id::create("vbp");
    this.hbp = uvm_reg_field::type_id::create("hbp");    
   
    // Configure
    this.vbp.configure (this, 16, 16, "RW", 0, 1'b0, 0, 1, 1);
    this.hbp.configure (this, 16, 0, "RW", 0, 1'b0, 0, 1, 1);  
  endfunction
  
endclass


//------------------------------------
// my_reg3                            
//------------------------------------
class my_reg3_c extends uvm_reg;
  
  `uvm_object_utils(my_reg3_c)
  
  // Field
  rand uvm_reg_field vact; 
  rand uvm_reg_field hact; 
  
  // Constructor
  function new(string name = "my_reg3_c");
    super.new(name, 32, UVM_NO_COVERAGE);
  endfunction
  
  // build
  virtual function void build();
    // create object instance
    this.vact = uvm_reg_field::type_id::create("vact");
    this.hact = uvm_reg_field::type_id::create("hact");   
    // Configure
    this.vact.configure (this, 16, 16, "RW", 0, 1'b0, 0, 1, 1);
    this.hact.configure (this, 16, 0, "RW", 0, 1'b0, 0, 1, 1);  
  endfunction
  
endclass


//------------------------------------
// my_reg4                            
//------------------------------------
class my_reg4_c extends uvm_reg;
  
  `uvm_object_utils(my_reg4_c)
  
  // Field
  rand uvm_reg_field vfp; 
  rand uvm_reg_field hfp; 

  
  // Constructor
  function new(string name = "my_reg4_c");
    super.new(name, 32, UVM_NO_COVERAGE);
  endfunction
  
  // build
  virtual function void build();
    // create object instance
    this.vfp = uvm_reg_field::type_id::create("vfp");
    this.hfp = uvm_reg_field::type_id::create("hfp");    
   
    // Configure
    this.vfp.configure (this, 16, 16, "RW", 0, 1'b0, 0, 1, 1);
    this.hfp.configure (this, 16, 0, "RW", 0, 1'b0, 0, 1, 1); 
  endfunction
  
endclass


//------------------------------------
// my_reg5                            
//------------------------------------
class my_reg5_c extends uvm_reg;
  
  `uvm_object_utils(my_reg5_c)
  
  // Field
  rand uvm_reg_field weight_wr_mode;
  rand uvm_reg_field mirror_mode;  
  rand uvm_reg_field blur_mode;
  
  // Constructor
  function new(string name = "my_reg5_c");
    super.new(name, 32, UVM_NO_COVERAGE);
  endfunction
  
  // build
  virtual function void build();
    // create object instance
    this.weight_wr_mode = uvm_reg_field::type_id::create("weight_wr_mode");
    this.mirror_mode = uvm_reg_field::type_id::create("mirror_mode");
    this.blur_mode = uvm_reg_field::type_id::create("blur_mode");
   
    // Configure
    this.weight_wr_mode.configure (this, 1, 8, "RW", 0, 1'b0, 0, 1, 1);
    this.mirror_mode.configure (this, 1, 4, "RW", 0, 1'b0, 0, 1, 1);
    this.blur_mode.configure (this, 1, 0, "RW", 0, 1'b0, 0, 1, 1);
    
  endfunction
  
endclass


//------------------------------------
// my_reg6                            
//------------------------------------
class my_reg6_c extends uvm_reg;
  
  `uvm_object_utils(my_reg6_c)
  
  // Field
  rand uvm_reg_field w1; 
  rand uvm_reg_field w2; 
  rand uvm_reg_field w3; 
  
  // Constructor
  function new(string name = "my_reg6_c");
    super.new(name, 32, UVM_NO_COVERAGE);
  endfunction
  
  // build
  virtual function void build();
    // create object instance
    this.w1 = uvm_reg_field::type_id::create("w1");
    this.w2 = uvm_reg_field::type_id::create("w2");    
    this.w3 = uvm_reg_field::type_id::create("w3");   
    // Configure
    this.w1.configure (this, 4, 16, "RW", 0, 1'b0, 0, 1, 1);
    this.w2.configure (this, 4, 8, "RW", 0, 1'b0, 0, 1, 1);    
    this.w3.configure (this, 4, 0, "RW", 0, 1'b0, 0, 1, 1);    
  endfunction
  
endclass



//------------------------------------
// my_reg7                            
//------------------------------------
class my_reg7_c extends uvm_reg;
  
  `uvm_object_utils(my_reg7_c)
  
  // Field
  rand uvm_reg_field w4; 
  rand uvm_reg_field w5; 
  rand uvm_reg_field w6; 
  
  // Constructor
  function new(string name = "my_reg7_c");
    super.new(name, 32, UVM_NO_COVERAGE);
  endfunction
  
  // build
  virtual function void build();
    // create object instance
    this.w4 = uvm_reg_field::type_id::create("w4");
    this.w5 = uvm_reg_field::type_id::create("w5");    
    this.w6 = uvm_reg_field::type_id::create("w6");   
    // Configure
    this.w4.configure (this, 4, 16, "RW", 0, 1'b0, 0, 1, 1);
    this.w5.configure (this, 4, 8, "RW", 0, 1'b0, 0, 1, 1);    
    this.w6.configure (this, 4, 0, "RW", 0, 1'b0, 0, 1, 1);    
  endfunction
  
endclass


//------------------------------------
// my_reg8                            
//------------------------------------
class my_reg8_c extends uvm_reg;
  
  `uvm_object_utils(my_reg8_c)
  
  // Field
  rand uvm_reg_field w7; 
  rand uvm_reg_field w8; 
  rand uvm_reg_field w9; 
  
  // Constructor
  function new(string name = "my_reg8_c");
    super.new(name, 32, UVM_NO_COVERAGE);
  endfunction
  
  // build
  virtual function void build();
    // create object instance
    this.w7 = uvm_reg_field::type_id::create("w7");
    this.w8 = uvm_reg_field::type_id::create("w8");    
    this.w9 = uvm_reg_field::type_id::create("w9");   
    // Configure
    this.w7.configure (this, 4, 16, "RW", 0, 1'b0, 0, 1, 1);
    this.w8.configure (this, 4, 8, "RW", 0, 1'b0, 0, 1, 1);    
    this.w9.configure (this, 4, 0, "RW", 0, 1'b0, 0, 1, 1);    
  endfunction
  
endclass


//------------------------------------
// my_reg9                            
//------------------------------------
/*
class my_reg9_c extends uvm_reg;
  
  `uvm_object_utils(my_reg9_c)
  
  // Field
  rand uvm_reg_field o_scale_on;
  rand uvm_reg_field o_scale_factor;
  rand uvm_reg_field o_scale_mode;
  rand uvm_reg_field o_sync_polarity;
  
  // Constructor
  function new(string name = "my_reg9_c");
    super.new(name, 32, UVM_NO_COVERAGE);
  endfunction
  
  // build
  virtual function void build();
    // create object instance
    this.o_scale_on = uvm_reg_field::type_id::create("o_scale_on");
    this.o_scale_factor = uvm_reg_field::type_id::create("o_scale_factor");
    this.o_scale_mode = uvm_reg_field::type_id::create("o_scale_mode");
    this.o_sync_polarity = uvm_reg_field::type_id::create("o_sync_polarity");

    // Configure
    this.o_scale_on.configure (this, 1, 9, "RW", 0, 0, 1, 1, 1);
    this.o_scale_factor.configure (this, 1, 6, "RW", 0, 0, 1, 1, 1);
    this.o_scale_mode.configure (this, 1, 3, "RW", 0, 0, 1, 1, 1);
    this.o_sync_polarity.configure (this, 1, 0, "RW", 0, 0, 1, 1, 1);    
    
    
    
  endfunction
  
endclass
*/