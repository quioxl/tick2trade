// ---------------------------------------------------------------------------
//
//  Description: Avalon Interface
//    // Bundle of wires (logic) to attach to either an Avalon master or slave
// ---------------------------------------------------------------------------
import t2t_pkg::*;

interface avalon_if();
  logic        clk;
  logic        reset_n;
  logic        ready;
  logic        valid;
  logic        startofpacket;
  logic        endofpacket;
  logic [63:0] data;
  logic  [2:0] empty;
  logic        error;
  t_dec_msg    dec_data; // Uses the union to define the message fields

  assign dec_data = data;
endinterface : avalon_if
