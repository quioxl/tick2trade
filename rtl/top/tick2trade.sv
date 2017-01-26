// ---------------------------------------------------------------------------
//
//  Description: Top level wrapper
//
// ---------------------------------------------------------------------------

module tick2trade #(

  // Feed Decoder params
  parameter C_PKT_BEAT_BYTES     = 8,
  parameter C_PKT_MAX_BYTES      = 1500,
  parameter C_MSG_CNT_BYTES      = 2,
  parameter C_MSG_LEN_BYTES      = 2,
  parameter C_MSG_MIN_BYTES      = 8,
  parameter C_MSG_MAX_BYTES      = 32,

  //   Strategy Params
  parameter SRCB_RCB_HOST_ARB    =  0,
  parameter SRCB_RAM_WIDTH       =  64,
  parameter SRCB_ADDR_WIDTH      =  14,
  parameter PRCB_RCB_HOST_ARB    =  0,
  parameter PRCB_RAM_WIDTH       =  128,
  parameter PRCB_ADDR_WIDTH      =  14,
  parameter VRCB_RCB_HOST_ARB    =  0,
  parameter VRCB_RAM_WIDTH       =  64,
  parameter VRCB_ADDR_WIDTH      =  14,
  parameter ORCB_RCB_HOST_ARB    =  0,
  parameter ORCB_RAM_WIDTH       =  128,
  parameter ORCB_ADDR_WIDTH      =  14

) (

  // Clk/Reset
  input                                 clk,                       // Core clock
  input                                 reset_n,                   // Core reset

  avalon_if                             dec_in_if,                // Feed Decoder IF (Avalon)
  host_interface                        host_if,

//  //Inputs
//  in_valid,                  // Valid data present
//  in_startofpacket,          // Start of message
//  in_endofpacket,            // End of message
//  in_data,                   // Data payload
//  in_empty,                  // Empty bytes indicator
//  in_error,                  // Error indicator

  //Outputs
  in_ready,                  // Ready for message

  //--------------------------------------------------
  // Strategy
  //--------------------------------------------------
  order_interface                       order_if
  //Inputs
//  out_ready,
//
//  //Outputs
//  out_valid,
//  out_data

  );



  //--------------------------------------------------
  // Feed Decoder
  //--------------------------------------------------


//  input                                 in_valid;
//  input                                 in_startofpacket;
//  input                                 in_endofpacket;
//  input    [(FEED_MSG_DATA_W-1):0]      in_data;
//  input  [(FEED_EMPTY_DATA_W-1):0]      in_empty;
//  input                                 in_error;
//	output                                in_ready;

  //--------------------------------------------------
  // Strategy
  //--------------------------------------------------
//  input                                 out_ready;
//  output    [(STRAT_ORDER_DATA_W-1):0]  out_data;
//  output                                out_ready;


  // Interfaces
  avalon_if                             dec_if,

  //--------------------------------------------------
  // Feed Decoder
  //--------------------------------------------------
  feed_decoder #(
   .C_PKT_BEAT_BYTES    ( C_PKT_BEAT_BYTES        ),
   .C_PKT_MAX_BYTES     ( C_PKT_MAX_BYTES         ),
   .C_MSG_CNT_BYTES     ( C_MSG_CNT_BYTES         ),
   .C_MSG_LEN_BYTES     ( C_MSG_LEN_BYTES         ),
   .C_MSG_MIN_BYTES     ( C_MSG_MIN_BYTES         ),
   .C_MSG_MAX_BYTES     ( C_MSG_MAX_BYTES         )
  )feed_decoder_i (

    // Clock/Reset
    .clk                ( clk                     ),
    .reset_n            ( reset_n                 ),

    .in_ready           ( dec_in_if.ready         ),
    .in_valid           ( dec_in_if.valid         ),
    .in_startofpacket   ( dec_in_if.startofpacket ),
    .in_endofpacket     ( dec_in_if.endofpacket   ),
    .in_data            ( dec_in_if.data          ),
    .in_empty           ( dec_in_if.empty         ),
    .in_error           ( dec_in_if.error         ),


//    .dec_if             ( dec_if                   ),  FIXME - enable if Feed goes to interfaces

    .out_ready          ( dec_if.ready            ),
    .out_valid          ( dec_if.valid            ),
    .out_startofpacket  ( dec_if.startofpacket    ),
    .out_endofpacket    ( dec_if.endofpacket      ),
    .out_data           ( dec_if.data             ),
    .out_empty          ( dec_if.empty            ),
    .out_error          ( dec_if.error            )

  );



  //--------------------------------------------------
  // Strategy
  //--------------------------------------------------
  tts #(

   .SRCB_RCB_HOST_ARB   ( SRCB_RCB_HOST_ARB ),
   .SRCB_RAM_WIDTH      ( SRCB_RAM_WIDTH    ),
   .SRCB_ADDR_WIDTH     ( SRCB_ADDR_WIDTH   ),
   .PRCB_RCB_HOST_ARB   ( PRCB_RCB_HOST_ARB ),
   .PRCB_RAM_WIDTH      ( PRCB_RAM_WIDTH    ),
   .PRCB_ADDR_WIDTH     ( PRCB_ADDR_WIDTH   ),
   .VRCB_RCB_HOST_ARB   ( VRCB_RCB_HOST_ARB ),
   .VRCB_RAM_WIDTH      ( VRCB_RAM_WIDTH    ),
   .VRCB_ADDR_WIDTH     ( VRCB_ADDR_WIDTH   ),
   .ORCB_RCB_HOST_ARB   ( ORCB_RCB_HOST_ARB ),
   .ORCB_RAM_WIDTH      ( ORCB_RAM_WIDTH    ),
   .ORCB_ADDR_WIDTH     ( ORCB_ADDR_WIDTH   )

  )tts_i (

    // Clock/Reset
    .clk                ( clk               ),
    .reset_n            ( reset_n           ),

    .dec_if             ( dec_if            ),

    .host_if            ( host_if           ),
    .order_if           ( order_if          )

  );


endmodule