// ---------------------------------------------------------------------------
//
//  Description: Top level wrapper
//
// ---------------------------------------------------------------------------

module tick2trade #(

  // Feed Decoder params
  parameter C_PKT_DATA_WIDTH      = 64,

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
  input                clk,                // Core clock
  input                reset_n,            // Active low core reset

  input                aclk,               // Host Asynch Clk
  input                areset_n,           // Host Asycn Reset

  // Interfaces
  avalon_if            dec_in_if,          // Feed Decoder input IF (Avalon)
  host_interface       host_if,            // Host Config input IF
  order_interface      order_if            // Order output IF

  );

  localparam int C_PKT_EMPTY_WIDTH = $clog2(C_PKT_DATA_WIDTH);

  order_interface order_if2 ();   // Vivado issue with recognizing interfaces in the library running OOC

  // Interface between Feed and Strategy
  avalon_if #(.DATA_WIDTH  (C_PKT_DATA_WIDTH),
              .EMPTY_WIDTH (C_PKT_EMPTY_WIDTH)
             ) dec_if ();

  //--------------------------------------------------
  // Feed Decoder
  //--------------------------------------------------
  feed_decoder #(
   .C_PKT_DATA_WIDTH    ( C_PKT_DATA_WIDTH        )
  )feed_decoder_i (

    // Clock/Reset
    .clk                ( clk                     ),
    .reset_n            ( reset_n                 ),

    // Feed input
    .in_ready           ( dec_in_if.ready         ),
    .in_valid           ( dec_in_if.valid         ),
    .in_startofpacket   ( dec_in_if.startofpacket ),
    .in_endofpacket     ( dec_in_if.endofpacket   ),
    .in_data            ( dec_in_if.data          ),
    .in_empty           ( dec_in_if.empty         ),
    .in_error           ( dec_in_if.error         ),

    // Output to Strategy
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
    .clk                ( clk      ),
    .reset_n            ( reset_n  ),
    .aclk               ( aclk     ),
    .areset_n           ( areset_n ),

    // Interfaces
    .dec_if             ( dec_if    ),
    .host_if            ( host_if   ),
    .order_if           ( order_if  )

  );


endmodule