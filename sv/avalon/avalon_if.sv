interface avalon_if;
  logic clk;
  logic in_ready;
  logic in_valid;
  logic in_startofpacket;
  logic in_endofpacket;
  logic [63:0] in_data;
  logic [2:0] in_empty;
  logic in_error;
endinterface