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

  avalon_if            dec_if,
  host_interface       host_if,
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

    reg          tts_sym_vld;
    reg  [13 :0] tts_rd_addr;
    reg  [2  :0] sym_idx;

    wire         sef_rd_srcb, sef_rd_prcb, sef_rd_vrcb, sef_rd_orcb;
    wire         sef_pcmp_load_a, sef_pcmp_load_b, sef_vcmp_load_a, sef_vcmp_load_b;
    wire         sef_out_valid;

    wire [63 :0] srcb_data, vrcb_data;
    wire [127:0] prcb_data, orcb_data;

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

    .host_if            ( host_if           ),

    .srcb_hpb_if        ( srcb_hpb_if       ),
    .prcb_hpb_if        ( prcb_hpb_if       ),
    .vrcb_hpb_if        ( vrcb_hpb_if       ),
    .orcb_hpb_if        ( orcb_hpb_if       )

  );

  //------------------------------------------------------------------------------------------------------------------
  // FSM
  //------------------------------------------------------------------------------------------------------------------
  sef sef_i (
    // Clk/Reset
    .clk               (clk),
    .reset_n           (reset_n),

    // Feed Decoder IF
    .dec_if            (dec_if),

    // Symbol ID RCB
    .sef_rd_srcb       (sef_rd_srcb),
    .tts_sym_vld       (tts_sym_vld),

    // Price Path (RCB & CMP)
    .sef_rd_prcb       (sef_rd_prcb),
    .sef_pcmp_load_a   (sef_pcmp_load_a),
    .sef_pcmp_load_b   (sef_pcmp_load_b),

    // Volume Path (RCB & CMP)
    .sef_rd_vrcb       (sef_rd_vrcb),
    .sef_vcmp_load_a   (sef_vcmp_load_a),
    .sef_vcmp_load_b   (sef_vcmp_load_b),

    // Order RCB
    .sef_rd_orcb       (sef_rd_orcb),
    .sef_out_valid     (sef_out_valid)
);

  //------------------------------------------------------------------------------------------------------------------
  // Symbol RCB
  //------------------------------------------------------------------------------------------------------------------
  rcb # (
   .RCB_HOST_ARB    ( SRCB_RCB_HOST_ARB ),
   .RCB_RAM_WIDTH   ( SRCB_RAM_WIDTH    )
  ) srcb_i (

    // Clock/Reset
    .clk              (clk),
    .reset_n          (reset_n),

    .t2t_rd_addr      (dec_if.data[37:24]),  // Read address is the Symbol ID
    .sef_read         (sef_rd_srcb),
    .sef_inmsg        ('h0),

    .rcb_data         (srcb_data),

    .hpb_if_i         (srcb_hpb_if)

  );

  // Since the Symbol RCB is a library component, a little bit of
  // muxing needs to be done in the wrapper to extract the correct address
  // if this produces a bad timing path, the sRCB could be customized
  // and the byte muxing done prior to the register
  always @(posedge clk) begin
    if      (!reset_n)    sym_idx <= 2'b00;
    else if (sef_rd_srcb) sym_idx <= dec_if.data[39:38];
  end

  always_comb begin
    case(sym_idx)
      2'b00   : begin
                tts_rd_addr = srcb_data[13:0];
                tts_sym_vld = srcb_data[15];
                end
      2'b01   : begin
                tts_rd_addr = srcb_data[29:16];
                tts_sym_vld = srcb_data[31];
                end
      2'b10   : begin
                tts_rd_addr = srcb_data[45:32];
                tts_sym_vld = srcb_data[47];
                end
      2'b11   : begin
                tts_rd_addr = srcb_data[61:48];
                tts_sym_vld = srcb_data[63];
                end
      default : begin
                tts_rd_addr = 14'hX;
                tts_sym_vld = 1'bx;
                end
    endcase
  end

  //------------------------------------------------------------------------------------------------------------------
  // Price RCB
  //------------------------------------------------------------------------------------------------------------------
  rcb # (
   .RCB_HOST_ARB    ( PRCB_RCB_HOST_ARB ),
   .RCB_RAM_WIDTH   ( PRCB_RAM_WIDTH    )
  ) prcb_i (

    // Clock/Reset
    .clk              (clk),
    .reset_n          (reset_n),

    .t2t_rd_addr      (tts_rd_addr),
    .sef_read         (sef_rd_prcb),
    .sef_inmsg        ('h0),

    .rcb_data         (prcb_data),

    .hpb_if_i         (prcb_hpb_if)

  );

  //------------------------------------------------------------------------------------------------------------------
  // Volume RCB
  //------------------------------------------------------------------------------------------------------------------
  rcb # (
   .RCB_HOST_ARB    ( VRCB_RCB_HOST_ARB ),
   .RCB_RAM_WIDTH   ( VRCB_RAM_WIDTH    )
  ) vrcb_i (

    // Clock/Reset
    .clk              (clk),
    .reset_n          (reset_n),

    .t2t_rd_addr      (tts_rd_addr),
    .sef_read         (sef_rd_vrcb),
    .sef_inmsg        ('h0),

    .rcb_data         (vrcb_data),

    .hpb_if_i         (vrcb_hpb_if)

  );

  // Compare

  //------------------------------------------------------------------------------------------------------------------
  // Order RCB
  //------------------------------------------------------------------------------------------------------------------
  rcb # (
   .RCB_HOST_ARB    ( ORCB_RCB_HOST_ARB ),
   .RCB_RAM_WIDTH   ( ORCB_RAM_WIDTH    )
  ) orcb_i (

    // Clock/Reset
    .clk              (clk),
    .reset_n          (reset_n),

    .t2t_rd_addr      (tts_rd_addr),
    .sef_read         (sef_rd_orcb),
    .sef_inmsg        ('h0),

    .rcb_data         (orcb_data),

    .hpb_if_i         (orcb_hpb_if)

  );

endmodule // tts
