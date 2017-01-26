// ---------------------------------------------------------------------------
//
//  Description: Avalon Interface
//
// ---------------------------------------------------------------------------
interface hpb_if #( parameter RCB_RAM_ADDR_WIDTH = 14, parameter RCB_RAM_WIDTH = 64);

  logic                              clk;
  logic                              reset_n;

  logic  [(RCB_RAM_ADDR_WIDTH-1):0]  hpb_wr_addr;
  logic       [(RCB_RAM_WIDTH-1):0]  hpb_wr_data;
  logic       [RCB_RAM_WIDTH/8-1:0]  hpb_wr_byte_en;
  logic                              hpb_wr_req;
  logic                              rcb_wr_done;

endinterface : hpb_if