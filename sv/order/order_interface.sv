// ---------------------------------------------------------------------------
//
//  Description: Order interface
//
// ---------------------------------------------------------------------------
interface order_interface #( parameter DATA_WIDTH = 128);

  logic                    clk;
  logic                    reset_n;
  logic [(DATA_WIDTH-1):0] data;
  logic                    ready;
  logic                    valid;

endinterface