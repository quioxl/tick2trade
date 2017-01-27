// ---------------------------------------------------------------------------
//
//  Description: Top level wrapper
//
// ---------------------------------------------------------------------------

module tick2trade #(

  // Feed Decoder params
  parameter C_PKT_BEAT_BYTES      = 8,
  parameter C_PKT_MAX_BYTES       = 1500,
  parameter C_MSG_CNT_BYTES       = 2,
  parameter C_MSG_LEN_BYTES       = 2,
  parameter C_MSG_MIN_BYTES       = 8,
  parameter C_MSG_MAX_BYTES       = 32,
  parameter C_DEC_IF_DATA_WIDTH   = 64,
  parameter C_DEC_IF_EMPTY_WIDTH  = 64,

  //   Strategy Params
  parameter HPB_ASYNC_HOST        = 0,
  parameter HPB_DATA_WIDTH        = 128,

  parameter SRCB_RAM_WIDTH        =  64,
  parameter SRCB_ADDR_WIDTH       =  14,
  parameter PRCB_RAM_WIDTH        =  128,
  parameter PRCB_ADDR_WIDTH       =  14,
  parameter VRCB_RAM_WIDTH        =  64,
  parameter VRCB_ADDR_WIDTH       =  14,
  parameter ORCB_RAM_WIDTH        =  128,
  parameter ORCB_ADDR_WIDTH       =  14

) (

  // Clk/Reset
  input                                 clk,                       // Core clock
  input                                 reset_n,                   // Core reset

  avalon_if                             dec_in_if,                // Feed Decoder input IF (Avalon)
  host_interface                        host_if,                  // Host Config input IF
  order_interface                       order_if                  // Order output IF

  );


  // Interface between Feed and Strategy
  avalon_if #(.DATA_WIDTH  (C_DEC_IF_DATA_WIDTH),
              .EMPTY_WIDTH (C_DEC_IF_EMPTY_WIDTH)
             ) dec_if ();

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
   .HPB_ASYNC_HOST      ( HPB_ASYNC_HOST    ),
   .HPB_DATA_WIDTH      ( HPB_DATA_WIDTH    ),
   .SRCB_RAM_WIDTH      ( SRCB_RAM_WIDTH    ),
   .SRCB_ADDR_WIDTH     ( SRCB_ADDR_WIDTH   ),
   .PRCB_RAM_WIDTH      ( PRCB_RAM_WIDTH    ),
   .PRCB_ADDR_WIDTH     ( PRCB_ADDR_WIDTH   ),
   .VRCB_RAM_WIDTH      ( VRCB_RAM_WIDTH    ),
   .VRCB_ADDR_WIDTH     ( VRCB_ADDR_WIDTH   ),
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