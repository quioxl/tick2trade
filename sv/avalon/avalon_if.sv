interface avalon_if;
  logic clk;
  logic reset_n;
  logic ready;
  logic valid;
  logic startofpacket;
  logic endofpacket;
  logic [63:0] data;
  logic [2:0] empty;
  logic error;
endinterface