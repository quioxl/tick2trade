// ---------------------------------------------------------------------------
//
//  Description: The Comparator Subtraction block (cmp_sub) checks if
//               the high value is greater than the low value. If it is
//               the condition is stated as true.
//
// ---------------------------------------------------------------------------

import tts_pkg::*;

module cmp_sub #(
  parameter SUB_DATA_WIDTH  = 32,  // Width of the incoming data for compare
  parameter SUB_EARLY_WIDTH = 24,  // Width available for early pipelining
  parameter SUB_PIPE        = 0    // Adds additional pipeline stage to the compare for timing
) (

  // Clk/Reset
  input                              clk,         // Core clock
  input                              reset_n,     // Active low core reset

  input  bit [SUB_DATA_WIDTH-1:0]    value_hi,    // Expected high value
  input  bit [SUB_DATA_WIDTH-1:0]    value_lo,    // Expected lo value

  output bit                         cond_true    // value_hi is greater than value_lo
);

  assign cond_true = value_hi > value_lo;

endmodule // cmp_sub
