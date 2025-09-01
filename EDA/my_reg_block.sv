`include "my_reg_lib.sv"

class my_reg_block extends uvm_reg_block;
  
  `uvm_object_utils(my_reg_block)
  
  // Reg
  rand my_reg1_c my_reg1;
  rand my_reg2_c my_reg2;
  rand my_reg3_c my_reg3;
  rand my_reg4_c my_reg4;
  rand my_reg5_c my_reg5;
  rand my_reg6_c my_reg6;  
  rand my_reg7_c my_reg7;
  rand my_reg8_c my_reg8;  
 // rand my_reg9_c my_reg9;

  
  
  // Constructor  
  function new(string name = "my_reg_block");
    super.new (name, build_coverage(UVM_NO_COVERAGE));
  endfunction
  
  // Build
  virtual function void build();
    
    // create instances
    default_map = create_map ("my_map", 0, 4, UVM_LITTLE_ENDIAN); // name, offset, n-byte, Endian
    my_reg1 = my_reg1_c::type_id::create("my_reg1", ,get_full_name);
    my_reg2 = my_reg2_c::type_id::create("my_reg2", ,get_full_name);
    my_reg3 = my_reg3_c::type_id::create("my_reg3", ,get_full_name);
    my_reg4 = my_reg4_c::type_id::create("my_reg4", ,get_full_name);    
    my_reg5 = my_reg5_c::type_id::create("my_reg5", ,get_full_name);
    my_reg6 = my_reg6_c::type_id::create("my_reg6", ,get_full_name);    
    my_reg7 = my_reg7_c::type_id::create("my_reg7", ,get_full_name);
    my_reg8 = my_reg8_c::type_id::create("my_reg8", ,get_full_name);    
 //   my_reg9 = my_reg9_c::type_id::create("my_reg9", ,get_full_name);        
    
    
    // call build of each reg
    my_reg1.build();
    my_reg2.build();
    my_reg3.build();
    my_reg4.build();    
    my_reg5.build();
    my_reg6.build();    
    my_reg7.build();
    my_reg8.build();    
  //  my_reg9.build();      
    // configure
    my_reg1.configure(this);
    my_reg2.configure(this);
    my_reg3.configure(this);
    my_reg4.configure(this);    
    my_reg5.configure(this);
    my_reg6.configure(this);
    my_reg7.configure(this);
    my_reg8.configure(this);       
  //  my_reg9.configure(this);       
    
    //my_reg1.configure(this, null, "tb.DUT.SFR.my_reg1");
    //my_reg2.configure(this, null, "tb.DUT.SFR.my_reg2");
    
    // add_hdl
    my_reg1.add_hdl_path_slice("my_reg1", 0, 32);
    my_reg2.add_hdl_path_slice("my_reg2", 0, 32);
    my_reg3.add_hdl_path_slice("my_reg3", 0, 32);
    my_reg4.add_hdl_path_slice("my_reg4", 0, 32);    
    my_reg5.add_hdl_path_slice("my_reg5", 0, 32);
    my_reg6.add_hdl_path_slice("my_reg6", 0, 32);
    my_reg7.add_hdl_path_slice("my_reg7", 0, 32);
    my_reg8.add_hdl_path_slice("my_reg8", 0, 32);        
  //  my_reg9.add_hdl_path_slice("my_reg9", 0, 32);        
    
    
    // add registers to the dafault map
    default_map.add_reg (my_reg1, 0, "RW", 0);
    default_map.add_reg (my_reg2, 4, "RW", 0);
    default_map.add_reg (my_reg3, 8, "RW", 0);
    default_map.add_reg (my_reg4, 12, "RW", 0);    
    default_map.add_reg (my_reg5, 16, "RW", 0);
    default_map.add_reg (my_reg6, 20, "RW", 0);
    default_map.add_reg (my_reg7, 24, "RW", 0);
    default_map.add_reg (my_reg8, 28, "RW", 0);  
 //   default_map.add_reg (my_reg9, 32, "RW", 0);      
    lock_model();
    
  endfunction
  
endclass