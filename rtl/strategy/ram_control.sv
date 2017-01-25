
module ram_control
#(
  parameter RCB_HOST_ARB      = 100,             //
  parameter RCB_RAM_WIDTH     = 64,              // Width of the RAM required to hold per symbol parameters
  parameter RCB_REG_ADDR      = 0                //
) (

  // Clk/Reset
  input           clk,
  input           reset_n,

  // Feed Decoder IF
  input                     [13:0] t2t_rd_addr,  //
  input                            sef_read,     //
  input                            slf_inmsg,    //

  output     [(RCB_RAM_WIDTH-1):0] rcb_data,     //

  // Host Config IF
  input                     [13:0] hpb_wr_addr,  //
  input      [(RCB_RAM_WIDTH-1):0] hpb_wr_data,  //
  input  [log2(RCB_RAM_WIDTH)-1:0] hpb_wr_en,    //
  input                            hpb_wr_req,   //
  output                           rcb_wr_done   //
);


endmodule // ram_control