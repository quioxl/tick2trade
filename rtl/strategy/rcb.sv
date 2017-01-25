// ---------------------------------------------------------------------------
//
//  Description: RAM Control block responsible for arbitrating between Symbol
//               lookup (RAM Reads) and host configuration (RAM writes)
//
// ---------------------------------------------------------------------------

//import tts_pkg::*;

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
  input      [RCB_RAM_WIDTH/8-1:0] hpb_wr_en,    // Write enable
  input                            hpb_wr_req,   // Write Request strobe
  output reg                       rcb_wr_done   // Write done flag back to FSM

);

  localparam RAM_DEPTH = 16384;                  // RAM Depth
  localparam WR_EN_W   = 8;                      // Write Enable granularity

  //---------------------------------------------------------------------
  // RAM
  // Expecting inferrence of BRAM.
  //---------------------------------------------------------------------
  reg        [RCB_RAM_WIDTH/8-1:0] hpb_wr_en_q;
  reg                       [13:0] ram_addr;                          // RAM Address
  reg                              accept_write_req;                  // Flag indicating if the Wr Request should be accepted
  reg                              accept_write_req_q;                // Flag indicating if the Wr Request should be accepted
  reg                              ignore_hpb_wr_req;                 // Register indicating if Wr Req input should be ignored
  reg        [(RCB_RAM_WIDTH-1):0] RAM[RAM_DEPTH-1:0];                // BRAM RAM to store Symbol information

  //---------------------------------------------------
  // Only accept write if read isn't requested and
  // previous write request has been de-asserted
  //---------------------------------------------------
  assign accept_write_req = !sef_read && hpb_wr_req && !ignore_hpb_wr_req;

  if (RCB_REG_ADDR == 0) begin
    always_comb begin
      accept_write_req_q = accept_write_req;
    end
  end else if (RCB_REG_ADDR == 1)  begin
    always_ff @(posedge clk) begin
      if (!reset_n) begin
        accept_write_req_q  <= 'h0;
      end else  begin
        accept_write_req_q  <= accept_write_req;
      end
    end
  end else begin
    $error ("Invalid RCB_REG_ADDR Setting");
  end

//  assign accept_write_req = !sef_read && hpb_wr_req && !ignore_hpb_wr_req;

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
  always_ff @(posedge clk) begin
    if (!reset_n) begin
      hpb_wr_en_q  <= 'h0;
    end else  begin
      hpb_wr_en_q  <= hpb_wr_en;
    end
  end

  //---------------------------------------------------
  //Arbitrate the address.  Default to Feed Decoder
  //---------------------------------------------------
  if (RCB_REG_ADDR == 0) begin
    always_comb begin
      ram_addr = t2t_rd_addr;
      if (accept_write_req) begin
        ram_addr = hpb_wr_addr;
      end
    end
  end else if (RCB_REG_ADDR == 1)  begin
    always_ff @(posedge clk) begin
      if (!reset_n) begin
        ram_addr  <= 1'b0;
      end else if (accept_write_req) begin
        ram_addr  <= hpb_wr_addr;
      end else begin
        ram_addr  <= t2t_rd_addr;
      end
    end
  end else begin
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
    end else if (!hpb_wr_req) begin
      ignore_hpb_wr_req   <= 1'b0;       // WR Req de-asserted.  De-assert ignore
    end
  end

  //---------------------------------------------------
  //Set the write enables
  //---------------------------------------------------
  generate genvar ii;
    for (ii=0; ii < RCB_RAM_WIDTH/WR_EN_W; ii = ii+1) begin

      if (RCB_REG_ADDR == 0) begin
        always_ff @(posedge clk) begin
          if (hpb_wr_en[ii] && accept_write_req) begin
            RAM[ram_addr][(ii+1)*WR_EN_W-1:ii*WR_EN_W] <= hpb_wr_data[(ii+1)*WR_EN_W-1:ii*WR_EN_W];
          end
        end
      end else if (RCB_REG_ADDR == 1)  begin
        always_ff @(posedge clk) begin
          if (hpb_wr_en_q[ii] && accept_write_req_q) begin
            RAM[ram_addr][(ii+1)*WR_EN_W-1:ii*WR_EN_W] <= hpb_wr_data[(ii+1)*WR_EN_W-1:ii*WR_EN_W];
          end
        end
      end
    end
  endgenerate

  //---------------------------------------------------
  // Assign the write done  Flop?
  //---------------------------------------------------
  always_ff @(posedge clk) begin
    if (!reset_n) begin
      rcb_wr_done <= 1'b0;
    end else  begin
      rcb_wr_done <= accept_write_req;
    end
  end

endmodule // rcb