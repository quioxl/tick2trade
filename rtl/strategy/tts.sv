// ---------------------------------------------------------------------------
//
//  Copyright 2017 IMC. All Rights Reserved.
//
//  Description: Strategy module wrapper containing RCB, Comparator, and FSM
//               modules
//
// ---------------------------------------------------------------------------

//`include "strat_pkg.sv"
//
//import strat_pkg::*;

module tts
#(
  // Symbol RAM Control Parameters
  parameter SRCB_RCB_HOST_ARB  = 0,
  parameter SRCB_RAM_WIDTH     = 64,
  parameter SRCB_REG_ADDR      = 1,

  // Price RAM Control Parameters
  parameter PRCB_RCB_HOST_ARB  = 0,
  parameter PRCB_RAM_WIDTH     = 128,
  parameter PRCB_REG_ADDR      = 0,

  // Volume RAM Control Parameters
  parameter VRCB_RCB_HOST_ARB  = 0,
  parameter VRCB_RAM_WIDTH     = 64,
  parameter VRCB_REG_ADDR      = 0,

  // Order RAM Control Parameters
  parameter ORCB_RCB_HOST_ARB  = 0,
  parameter ORCB_RAM_WIDTH     = 128,
  parameter ORCB_REG_ADDR      = 0

) (
  avalon_if      feed_if,
  host_interface host_if
);

  // FSM

  // Compare

  //------------------------------------------------------------------------------------------------------------------
  // Symbol RCB
  //------------------------------------------------------------------------------------------------------------------
  rcb # (
   .RCB_HOST_ARB    ( SRCB_RCB_HOST_ARB ),
   .RCB_RAM_WIDTH   ( SRCB_RAM_WIDTH    ),
   .RCB_REG_ADDR    ( SRCB_REG_ADDR     )
  ) srcb_i (

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

  //------------------------------------------------------------------------------------------------------------------
  // Price RCB
  //------------------------------------------------------------------------------------------------------------------
  rcb # (
   .RCB_HOST_ARB    ( PRCB_RCB_HOST_ARB ),
   .RCB_RAM_WIDTH   ( PRCB_RAM_WIDTH    ),
   .RCB_REG_ADDR    ( PRCB_REG_ADDR     )
  ) prcb_i (

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

  //------------------------------------------------------------------------------------------------------------------
  // Volume RCB
  //------------------------------------------------------------------------------------------------------------------
  rcb # (
   .RCB_HOST_ARB    ( VRCB_RCB_HOST_ARB ),
   .RCB_RAM_WIDTH   ( VRCB_RAM_WIDTH    ),
   .RCB_REG_ADDR    ( VRCB_REG_ADDR     )
  ) vrcb_i (

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

  //------------------------------------------------------------------------------------------------------------------
  // Order RCB
  //------------------------------------------------------------------------------------------------------------------
  rcb # (
   .RCB_HOST_ARB    ( ORCB_RCB_HOST_ARB ),
   .RCB_RAM_WIDTH   ( ORCB_RAM_WIDTH    ),
   .RCB_REG_ADDR    ( ORCB_REG_ADDR     )
  ) orcb_i (

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

endmodule // tts