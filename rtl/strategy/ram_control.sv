// ---------------------------------------------------------------------------
//
//  Copyright 2014 IMC. All Rights Reserved.
//
//  Description: RAM Control block responsible for arbitrating between Symbol
//               lookup and host configuration
//
// ---------------------------------------------------------------------------

`include "strat_pkg.sv"

import strat_pkg::*;

module ram_control
#(
  parameter RCB_HOST_ARB      = 100,             //
  parameter RCB_RAM_WIDTH     = 64,              // Width of the RAM required to hold per symbol parameters
  parameter RCB_REG_ADDR      = 0                //
) (

  // Clk/Reset
  input                            clk,
  input                            reset_n,

  // Feed Decoder IF
  input                     [13:0] t2t_rd_addr,  //
  input                            sef_read,     //
  input                            slf_inmsg,    //

  output reg [(RCB_RAM_WIDTH-1):0] rcb_data,     //

  // Host Config IF
  input                     [13:0] hpb_wr_addr,  //
  input      [(RCB_RAM_WIDTH-1):0] hpb_wr_data,  //
  input  [log2(RCB_RAM_WIDTH)-1:0] hpb_wr_en,    //
  input                            hpb_wr_req,   //
  output                           rcb_wr_done   //

);

  localparam RAM_DEPTH = 16384;

  //---------------------------------------------------------------------
  // RAM
  // Expecting inferrence of BRAM.
  //---------------------------------------------------------------------
  reg [13:0]                ram_addr;
  reg                       accept_write_req;
  reg                       ignore_hpb_wr_req;
  reg [(RCB_RAM_WIDTH-1):0] RAM[RAM_DEPTH-1:0];                // BRAM RAM to store Symbol information

  assign accept_write_req = !sef_read && hpb_wr_req && !ignore_hpb_wr_req;

  // Register the output data to help with TCKO
  always_ff @(posedge clk) begin
    if (!reset_n) begin
      rcb_data <= 'h0;
    end else begin
      rcb_data <= RAM[ram_addr];
    end
  end

  //Arbitrate the address.  Default to main stream
  always_comb begin
    ram_addr = t2t_rd_addr;
    if (accept_write_req) begin
      ram_addr = hpb_wr_addr;
    end
  end

  //Write Request ignore generation
  always_ff @(posedge clk) begin
    if (!reset_n) begin
      ignore_hpb_wr_req   <= 1'b0;
    end else if (accept_write_req) begin
      ignore_hpb_wr_req   <= 1'b1;
    end else if (ignore_hpb_wr_req && !hpb_wr_reg) begin
      ignore_hpb_wr_req   <= 1'b0;       // WR Req de-asserted.  De-assert ignore
    end
  end

  //Set the write enables
  generate genvar ii;
    for (ii=0; ii < RCB_RAM_WIDTH/8; ii = ii+1) begin
      always_ff @(posedge clk) begin
        if (hpb_wr_en[ii]) begin
          RAM[ram_addr][(ii+1)*8-1:ii*8] <= hpb_wr_data[(ii+1)*8-1:ii*8];
        end
      end
    end
  endgenerate

  //Assign the write done  Flop?
  assign rcb_wr_done = accept_write_req;

endmodule // ram_control