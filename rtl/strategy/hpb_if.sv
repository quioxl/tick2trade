// ---------------------------------------------------------------------------
//
//  Copyright 2017 IMC. All Rights Reserved.
//
//  Description: Avalon Interface
//
// ---------------------------------------------------------------------------
interface hpb_if #( parameter RCB_RAM_WIDTH = 64);

  logic                              clk;
  logic                              reset_n;

  logic                              hpb_wr_addr;
  logic       [(RCB_RAM_WIDTH-1):0]  hpb_wr_data;
  logic   [log2(RCB_RAM_WIDTH)-1:0]  hpb_wr_en;
  logic                              hpb_wr_req;
  logic                              rcb_wr_done;

endinterface : hpb_if