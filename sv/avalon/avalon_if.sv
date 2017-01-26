// ---------------------------------------------------------------------------
//
//  Description: Avalon Interface
//    // Bundle of wires (logic) to attach to either an Avalon master or slave
// ---------------------------------------------------------------------------
interface avalon_if #( parameter DATA_WIDTH = 64, parameter EMPTY_WIDTH = 3);
  logic                      clk;
  logic                      reset_n;
  logic                      ready;
  logic                      valid;
  logic                      startofpacket;
  logic                      endofpacket;
  logic   [(DATA_WIDTH-1):0] data;
  logic  [(EMPTY_WIDTH-1):0] empty;
  logic                      error;
endinterface : avalon_if