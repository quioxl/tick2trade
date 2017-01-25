// ---------------------------------------------------------------------------
//
//  Description: Top level wrapper
//
// ---------------------------------------------------------------------------

module tick2trade (

  // Clk/Reset
  clk,                       // Core clock
  reset_n,                   // Core reset

  //--------------------------------------------------
  // Feed Decoder
  //--------------------------------------------------

  //Inputs
  in_valid,                  // Valid data present
  in_startofpacket,          // Start of message
  in_endofpacket,            // End of message
  in_data,                   // Data payload
  in_empty,                  // Empty bytes indicator
  in_error,                  // Error indicator

  //Outputs
  in_ready,                  // Ready for message

  //--------------------------------------------------
  // Strategy
  //--------------------------------------------------

  //Inputs
  out_ready,

  //Outputs
  out_valid,
  out_data

  );

  parameter FEED_MSG_DATA_W     = 64;
  parameter FEED_EMPTY_DATA_W   = 3;
  parameter STRAT_ORDER_DATA_W  = 128;

  //Clk/Reset
  input                                 clk;
  input                                 reset_n;

  //--------------------------------------------------
  // Feed Decoder
  //--------------------------------------------------
  input                                 in_valid;
  input                                 in_startofpacket;
  input                                 in_endofpacket;
  input    [(FEED_MSG_DATA_W-1):0]      in_data;
  input  [(FEED_EMPTY_DATA_W-1):0]      in_empty;
  input                                 in_error;
	output                                in_ready;

  //--------------------------------------------------
  // Strategy
  //--------------------------------------------------
  input                                 out_ready;
  output    [(STRAT_ORDER_DATA_W-1):0]  out_data;
  output                                out_ready;


  // Interfaces


  //--------------------------------------------------
  // Feed Decoder
  //--------------------------------------------------

  //--------------------------------------------------
  // Strategy
  //--------------------------------------------------
  tts tts_i (

    // Clock/Reset
    .clk              (),
    .reset_n          (),

    .t2t_rd_addr      (),
    .sef_read         (),
    .slf_inmsg        (),

    .rcb_data         (),

    .hpb_wr_addr      (),
    .hpb_wr_data      (),
    .hpb_wr_en        (),
    .hpb_wr_req       (),
    .rcb_wr_done      ()

  );

endmodule