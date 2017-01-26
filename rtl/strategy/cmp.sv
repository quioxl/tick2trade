// ---------------------------------------------------------------------------
//
//  Description: The Comparator block (CMP) is responsible for comparing the
//               strategy parameters against the incoming message field.
//
// ---------------------------------------------------------------------------

import tts_pkg::*;

module cmp #(
  parameter CMP_RAM_WIDTH  = 64,  // Width of the incoming parameters for compare
  parameter CMP_CYCA_WIDTH = 24,  // Width of the first data beat
  parameter CMP_REG_CYCB   = 0,   // Register cycle B before compare?
  parameter CMP_PIPE       = 0    // Adds additional pipeline stage to the compare for timing
) (

  // Clk/Reset
  input                              clk,         // Core clock
  input                              reset_n,     // Active low core reset

  input  bit [CMP_RAM_WIDTH-1    :0] rcb_data,    // Parameter constraints
  input  bit [(CMP_RAM_WIDTH/2)-1:0] tts_field,   // Field for compare

  input  bit                         sef_load_a,  // Load the first part of the tts_field
  input  bit                         sef_load_b,  // Load the second part of the tts_field

  output bit                         cmp_pass     // Comp values pass the strategy check
);

  localparam FLD_HI = (CMP_RAM_WIDTH/2) - 1;
  localparam FLD_LO = (CMP_RAM_WIDTH/2) - CMP_CYCA_WIDTH;

  reg  [FLD_HI:0] field_q;

  reg             load_b_q;
  wire [FLD_HI:0] compare_val;

  wire            field_lt_max, field_gt_min;

  always @(posedge clk) begin
    if      (!reset_n)   field_q                <= '0;
    else if (sef_load_a) field_q[FLD_HI:FLD_LO] <= tts_field[FLD_HI:FLD_LO];
    else if (sef_load_b) field_q[FLD_LO-1:0]    <= tts_field[FLD_LO-1:0];
  end

  // load_b_q is sticky so that after the initial load_b cycle
  // the comparator gets the held value
  always @(posedge clk) begin
    if (!reset_n)        load_b_q <= 1'b0;
    else if (sef_load_b) load_b_q <= 1'b1;
    else if (sef_load_a) load_b_q <= 1'b0;
  end

  if (CMP_REG_CYCB == 1) begin
    assign compare_val = field_q;
  end else begin
    assign compare_val = load_b_q ? field_q : {field_q[FLD_HI:FLD_LO],tts_field[FLD_LO-1:0]};
  end

  cmp_sub #( 
    .SUB_DATA_WIDTH  (FLD_HI+1),
    .SUB_EARLY_WIDTH (CMP_CYCA_WIDTH),
    .SUB_PIPE        (CMP_PIPE)
  ) cmp_max_i (
    .clk       (clk),
    .reset_n   (reset_n),

    .value_hi  (rcb_data[CMP_RAM_WIDTH-1:CMP_RAM_WIDTH/2]),
    .value_lo  (compare_val),
    .cond_true (field_lt_max)
  );

  cmp_sub #( 
    .SUB_DATA_WIDTH  (FLD_HI+1),
    .SUB_EARLY_WIDTH (CMP_CYCA_WIDTH),
    .SUB_PIPE        (CMP_PIPE)
  ) cmp_min_i (
    .clk       (clk),
    .reset_n   (reset_n),

    .value_hi  (compare_val),
    .value_lo  (rcb_data[(CMP_RAM_WIDTH/2)-1:0]),
    .cond_true (field_gt_min)
  );

  assign cmp_pass = field_lt_max & field_gt_min;

endmodule // cmp
