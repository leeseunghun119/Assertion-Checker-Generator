
`include "hw_if.sv"
`include "apb_sfr_ctrl.v"
`include "IP_BLUR_SCALER_TOP.v"
`include "blur_scaler.v"
`include "counter.v"
`include "mux_output.v"
`include "mux_sram_read.v"
`include "sfr_cap.v"
`include "sync_signal.v"
`include "single_port_ram.v"
`include "ram_ctrl.v"
`include "video_sync_out_gen.v"


// Checker Intferface
`include "video_sync_checker_intf.sv"
`include "video_sync_out_checker_intf.sv"
`include "sfr_checker_intf.sv"
`include "mux_output_checker_intf.sv"
`include "ram_ctrl_checker_intf.sv"
`include "sram_checker_intf.sv"


// Assertion Waiver
`include "assertion_waiver.sv"
//`include "new_assertion_waiver.sv"