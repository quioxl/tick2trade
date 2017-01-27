// ---------------------------------------------------------------------------
//
//  Description: RAM Control block responsible for arbitrating between Symbol
//               lookup (RAM Reads) and host configuration (RAM writes)
//
// ---------------------------------------------------------------------------

module rcb
#(
  parameter RCB_RAM_ADDR_WIDTH = 14,                     // Address width parameter
  parameter RCB_RAM_WIDTH      = 64                      // Width of the RAM required to hold per symbol parameters
) (

  // Clk/Reset
  input                                   clk,            // Core clock
  input                                   reset_n,        // Active low core reset

  // Feed Decoder IF
  input      [(RCB_RAM_ADDR_WIDTH-1):0]   t2t_rd_addr,    // Address from Feed Decoder
  input                                   sef_read,       // Read strobe

  output reg      [(RCB_RAM_WIDTH-1):0]   rcb_data,       // Output data to comparator
  hpb_if                                  hpb_if_i        // Host Config interface

);

  localparam RAM_DEPTH = 2**RCB_RAM_ADDR_WIDTH;           // RAM Depth
  localparam WR_EN_W   = 8;                               // Write Enable granularity

  //---------------------------------------------------------------------
  // RAM
  // Expecting inferrence of BRAM.
  //---------------------------------------------------------------------
  reg                       [13:0] ram_addr;                        // RAM Address
  reg                              accept_write_req;                // Flag indicating if the Wr Request should be accepted
  reg                              ignore_hpb_wr_req_q;             // Flag indicating if Wr Req input should be ignored

  //---------------------------------------------------------------------
  // Storage RAM - Vivado should infer single port BRAM
  //   Width - RCB_RAM_WIDTH
  //   Depth - RAM_DEPTH (hardcoded to 16K)
  //---------------------------------------------------------------------
  reg        [(RCB_RAM_WIDTH-1):0] RAM[RAM_DEPTH-1:0];

  // Flag indicating if a write request is accepted
  assign accept_write_req = !sef_read && hpb_if_i.hpb_wr_req && !ignore_hpb_wr_req_q;

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

  //---------------------------------------------------
  //Arbitrate the address.  Default to Feed Decoder
  // FIXME - add error registers.
  //---------------------------------------------------
  always_comb begin
    ram_addr = t2t_rd_addr;
    if (accept_write_req) begin
      ram_addr = hpb_if_i.hpb_wr_addr;
    end
  end

  //---------------------------------------------------
  //Write Request ignore generation
  // Ignore when WR Request was processed but source
  // block has not dropped request on subsequent clk.
  // Sticky until wr_req input drops
  //---------------------------------------------------
  always_ff @(posedge clk) begin
    if (!reset_n) begin
      ignore_hpb_wr_req_q   <= 1'b0;
    end else if (accept_write_req) begin
      ignore_hpb_wr_req_q   <= 1'b1;
    end else if (!hpb_if_i.hpb_wr_req) begin
      ignore_hpb_wr_req_q   <= 1'b0;
    end
  end

  //---------------------------------------------------
  //Set the byte enables
  //---------------------------------------------------
  generate genvar ii;
    for (ii=0; ii < RCB_RAM_WIDTH/WR_EN_W; ii = ii+1) begin
      always_ff @(posedge clk) begin
        if (hpb_if_i.hpb_wr_byte_en[ii] && accept_write_req) begin
          RAM[ram_addr][(ii+1)*WR_EN_W-1:ii*WR_EN_W] <= hpb_if_i.hpb_wr_data[(ii+1)*WR_EN_W-1:ii*WR_EN_W];
        end
      end
    end
  endgenerate

  //---------------------------------------------------
  // Assign the write done  Flop?
  //---------------------------------------------------
  always_ff @(posedge clk) begin
    if (!reset_n) begin
      hpb_if_i.rcb_wr_done <= 1'b0;
    end else  begin
      hpb_if_i.rcb_wr_done <= accept_write_req;
    end
  end

endmodule // rcb