import uvm_pkg::*;

class apb_adapter extends uvm_reg_adapter;
  
  logic [31:0] bup_data;
  
  `uvm_object_utils(apb_adapter)
  
  // Constructor
  function new(string name = "apb_adapter");
    super.new(name);
  endfunction
  
  // reg2bus
  virtual function uvm_sequence_item reg2bus (const ref uvm_reg_bus_op rw);
    apb_item pkt;
    pkt = apb_item::type_id::create ("pkt");
    pkt.i_PWRITE = (rw.kind == UVM_WRITE);
    pkt.i_PADDR = rw.addr;
    pkt.i_PWDATA = rw.data;
    bup_data = rw.data;
    `uvm_info(get_type_name, $psprintf("[reg2bus] addr = %0h, data = %0h, kind = %s", pkt.i_PADDR, pkt.i_PWDATA, rw.kind.name()), UVM_LOW)
    return pkt;
  endfunction
  
  // bus2reg
  virtual function void bus2reg (uvm_sequence_item bus_item, ref uvm_reg_bus_op rw);
    apb_item pkt;
    
    if(! $cast(pkt, bus_item)) begin
      `uvm_fatal(get_type_name, "[apb_adapter] Failed to cast bus_item to pkt !")
    end
    
    rw.kind = pkt.i_PWRITE ? UVM_WRITE : UVM_READ;
    rw.addr = pkt.i_PADDR;
    rw.data = pkt.i_PWRITE ? pkt.i_PWDATA : pkt.o_PRDATA;
    rw.status = UVM_IS_OK;
    `uvm_info(get_type_name, $psprintf("[bus2reg] addr = %0h, data = %0h, kind = %s, status = %s", rw.addr, rw.data, rw.kind.name(), rw.status.name()), UVM_LOW)
  endfunction
  
endclass