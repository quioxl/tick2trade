// ---------------------------------------------------------------------------
//
//  Description: Strategy module wrapper containing RCB, Comparator, and FSM
//               modules
//
// ---------------------------------------------------------------------------

//import tts_pkg::*;

module tts
#(
  // Symbol RAM Control Parameters
  parameter SRCB_RCB_HOST_ARB  = 0,
  parameter SRCB_RAM_WIDTH     = 64,
  parameter SRCB_ADDR_WIDTH    = 14,

  // Price RAM Control Parameters
  parameter PRCB_RCB_HOST_ARB  = 0,
  parameter PRCB_RAM_WIDTH     = 128,
  parameter PRCB_ADDR_WIDTH    = 14,

  // Volume RAM Control Parameters
  parameter VRCB_RCB_HOST_ARB  = 0,
  parameter VRCB_RAM_WIDTH     = 64,
  parameter VRCB_ADDR_WIDTH    = 14,

  // Order RAM Control Parameters
  parameter ORCB_RCB_HOST_ARB  = 0,
  parameter ORCB_RAM_WIDTH     = 128,
  parameter ORCB_ADDR_WIDTH    = 14

) (
  input                clk,                // Core clock
  input                reset_n,            // Active low core reset

  avalon_if            feed_if,
  host_interface       host_interface_in,
  order_interface      order_if
);

  // Symbol RCB RAM Interface
  hpb_if    #(.RCB_RAM_ADDR_WIDTH(SRCB_ADDR_WIDTH),
              .RCB_RAM_WIDTH(SRCB_RAM_WIDTH)
             ) srcb_hpb_if();

  // Price RCB RAM Interface
  hpb_if    #(.RCB_RAM_ADDR_WIDTH(PRCB_ADDR_WIDTH),
              .RCB_RAM_WIDTH(PRCB_RAM_WIDTH)
             ) prcb_hpb_if();

  // Volume RCB RAM Interface
  hpb_if    #(.RCB_RAM_ADDR_WIDTH(VRCB_ADDR_WIDTH),
              .RCB_RAM_WIDTH(VRCB_RAM_WIDTH)
             ) vrcb_hpb_if();

  // Order RCB RAM Interface
  hpb_if    #(.RCB_RAM_ADDR_WIDTH(ORCB_ADDR_WIDTH),
              .RCB_RAM_WIDTH(ORCB_RAM_WIDTH)
             ) orcb_hpb_if();

  //------------------------------------------------------------------------------------------------------------------
  // HDP
  //------------------------------------------------------------------------------------------------------------------
  hpb # (
   .HPB_DATA_WIDTH      ( SRCB_RCB_HOST_ARB ),
   .HPB_ASYNC_HOST      ( SRCB_RAM_WIDTH    )
  ) hpb_i (

    // Clock/Reset
    .clk                ( clk               ),
    .reset_n            ( reset_n           ),

    .aclk               ( clk               ), //FIXME
    .areset_n           ( reset_n           ), //FIXME

    .host_interface_in  ( host_interface_in ),

    .srcb_hpb_if        ( srcb_hpb_if       ),
    .prcb_hpb_if        ( prcb_hpb_if       ),
    .vrcb_hpb_if        ( vrcb_hpb_if       ),
    .orcb_hpb_if        ( orcb_hpb_if       )

  );

  // FSM

  // Compare

  //------------------------------------------------------------------------------------------------------------------
  // Symbol RCB
  //------------------------------------------------------------------------------------------------------------------
  rcb # (
   .RCB_HOST_ARB    ( SRCB_RCB_HOST_ARB ),
   .RCB_RAM_WIDTH   ( SRCB_RAM_WIDTH    )
  ) srcb_i (

    // Clock/Reset
    .clk              ( clk         ),
    .reset_n          ( reset_n     ),

    .t2t_rd_addr      ('h0),
    .sef_read         ('h0),
    .sef_inmsg        ('h0),

    .rcb_data         (),

    .hpb_if_i         ( srcb_hpb_if )

  );

  //------------------------------------------------------------------------------------------------------------------
  // Price RCB
  //------------------------------------------------------------------------------------------------------------------
  rcb # (
   .RCB_HOST_ARB    ( PRCB_RCB_HOST_ARB ),
   .RCB_RAM_WIDTH   ( PRCB_RAM_WIDTH    )
  ) prcb_i (

    // Clock/Reset
    .clk              ( clk         ),
    .reset_n          ( reset_n     ),

    .t2t_rd_addr      ('h0),
    .sef_read         ('h0),
    .sef_inmsg        ('h0),

    .rcb_data         (),

    .hpb_if_i         ( prcb_hpb_if )

  );

  //------------------------------------------------------------------------------------------------------------------
  // Volume RCB
  //------------------------------------------------------------------------------------------------------------------
  rcb # (
   .RCB_HOST_ARB    ( VRCB_RCB_HOST_ARB ),
   .RCB_RAM_WIDTH   ( VRCB_RAM_WIDTH    )
  ) vrcb_i (

    // Clock/Reset
    .clk              ( clk         ),
    .reset_n          ( reset_n     ),

    .t2t_rd_addr      ('h0),
    .sef_read         ('h0),
    .sef_inmsg        ('h0),

    .rcb_data         (),

    .hpb_if_i         ( vrcb_hpb_if )

  );

  //------------------------------------------------------------------------------------------------------------------
  // Order RCB
  //------------------------------------------------------------------------------------------------------------------
  rcb # (
   .RCB_HOST_ARB    ( ORCB_RCB_HOST_ARB ),
   .RCB_RAM_WIDTH   ( ORCB_RAM_WIDTH    )
  ) orcb_i (

    // Clock/Reset
    .clk              ( clk         ),
    .reset_n          ( reset_n     ),

    .t2t_rd_addr      ('h0),
    .sef_read         ('h0),
    .sef_inmsg        ('h0),

    .rcb_data         (),

    .hpb_if_i         ( orcb_hpb_if )

  );

endmodule // tts