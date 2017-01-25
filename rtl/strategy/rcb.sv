// ---------------------------------------------------------------------------
//
//  Copyright 2017 IMC. All Rights Reserved.
//
//  Description: RAM Control block responsible for arbitrating between Symbol
//               lookup (RAM Reads) and host configuration (RAM writes)
//
// ---------------------------------------------------------------------------

import tts_pkg::*;

module rcb
#(
  parameter RCB_HOST_ARB      = 0,               // Control over write arbitration
  parameter RCB_RAM_WIDTH     = 64,              // Width of the RAM required to hold per symbol parameters
  parameter RCB_REG_ADDR      = 0                // Control registering the address
) (

  // Clk/Reset
  input                            clk,          // Core clock
  input                            reset_n,      // Active low core reset

  // Feed Decoder IF
  input                     [13:0] t2t_rd_addr,  // Address from Feed Decoder
  input                            sef_read,     // Read strobe
  input                            slf_inmsg,    //

  output reg [(RCB_RAM_WIDTH-1):0] rcb_data,     // Output data to comparator

  // Host Config IF
  input                     [13:0] hpb_wr_addr,  // Address
  input      [(RCB_RAM_WIDTH-1):0] hpb_wr_data,  // Write data
  input  [log2(RCB_RAM_WIDTH)-1:0] hpb_wr_en,    // Write enable
  input                            hpb_wr_req,   // Write Request strobe
  output                           rcb_wr_done   // Write done flag back to FSM

);

  localparam RAM_DEPTH = 16384;                  // RAM Depth
  localparam WR_EN_W   = 8;                      // Write Enable granularity

  //---------------------------------------------------------------------
  // RAM
  // Expecting inferrence of BRAM.
  //---------------------------------------------------------------------
  reg [13:0]                ram_addr;                          // RAM Address
  reg                       accept_write_req;                  // Flag indicating if the Wr Request should be accepted
  reg                       ignore_hpb_wr_req;                 // Register indicating if Wr Req input should be ignored
  reg [(RCB_RAM_WIDTH-1):0] RAM[RAM_DEPTH-1:0];                // BRAM RAM to store Symbol information

  //---------------------------------------------------
  // Only accept write if read isn't requested and
  // previous write request has been de-asserted
  //---------------------------------------------------
  assign accept_write_req = !sef_read && hpb_wr_req && !ignore_hpb_wr_req;

  //---------------------------------------------------
  // Register the output data to help with TCKO
  //---------------------------------------------------
  always_ff @(posedge clk) begin
    if (!reset_n) begin
      rcb_data <= 'h0;
    end else begin
      rcb_data <= RAM[ram_addr];
    end
  end

  // FIXME - need to register all inputs from decoder based on PARAM or we will be off a clk?
  //---------------------------------------------------
  //Arbitrate the address.  Default to Feed Decoder
  //---------------------------------------------------
  if (RCB_REG_ADDR == 0) begin : ASSIGN_ADDRESS
    always_comb begin
      ram_addr = t2t_rd_addr;
      if (accept_write_req) begin
        ram_addr = hpb_wr_addr;
      end
    end
  end else if (RCB_REG_ADDR == 1)  begin : REGISTER_ADDRESS
    always_ff @(posedge clk) begin
      if (!reset_n) begin
        ram_addr  <= 1'b0;
      end else if (accept_write_req) begin
        ram_addr  <= hpb_wr_addr;
      end else begin
        ram_addr  <= t2t_rd_addr;
      end
    end
  end else begin : INVALID_PARAM
    $error ("Invalid RCB_REG_ADDR Setting");
  end

  //---------------------------------------------------
  //Write Request ignore generation
  //---------------------------------------------------
  always_ff @(posedge clk) begin
    if (!reset_n) begin
      ignore_hpb_wr_req   <= 1'b0;
    end else if (accept_write_req) begin
      ignore_hpb_wr_req   <= 1'b1;
    end else if (ignore_hpb_wr_req && !hpb_wr_reg) begin
      ignore_hpb_wr_req   <= 1'b0;       // WR Req de-asserted.  De-assert ignore
    end
  end

  //---------------------------------------------------
  //Set the write enables
  //---------------------------------------------------
  generate genvar ii;
    for (ii=0; ii < RCB_RAM_WIDTH/WR_EN_W; ii = ii+1) begin
      always_ff @(posedge clk) begin
        if (hpb_wr_en[ii] && accept_write_req) begin
          RAM[ram_addr][(ii+1)*WR_EN_W-1:ii*WR_EN_W] <= hpb_wr_data[(ii+1)*WR_EN_W-1:ii*WR_EN_W];
        end
      end
    end
  endgenerate

  //---------------------------------------------------
  // Assign the write done  Flop?
  //---------------------------------------------------
  assign rcb_wr_done = accept_write_req;

endmodule // rcb