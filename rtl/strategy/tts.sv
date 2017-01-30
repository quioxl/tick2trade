// ---------------------------------------------------------------------------
//
//  Description: Strategy module wrapper containing RCB, Comparator, and FSM
//               modules
//
// ---------------------------------------------------------------------------

//import tts_pkg::*;
import t2t_pkg::*;

module tts
#(

  // HPB Parameters
  parameter HPB_ASYNC_HOST     = 0,
  parameter HPB_DATA_WIDTH     = 128,

  // Symbol RAM Control Parameters
  parameter SRCB_RAM_WIDTH     = 64,
  parameter SRCB_ADDR_WIDTH    = 14,

  // Price RAM Control Parameters
  parameter PRCB_RAM_WIDTH     = 128,
  parameter PRCB_ADDR_WIDTH    = 14,

  // Volume RAM Control Parameters
  parameter VRCB_RAM_WIDTH     = 64,
  parameter VRCB_ADDR_WIDTH    = 14,

  // Order RAM Control Parameters
  parameter ORCB_RAM_WIDTH     = 128,
  parameter ORCB_ADDR_WIDTH    = 14

) (
  // Clk/Reset
  input                clk,                // Core clock
  input                reset_n,            // Active low core reset

  input                aclk,               // Host Asynch Clk
  input                areset_n,           // Host Asycn Reset

  // Interfaces
  avalon_if            dec_if,
  host_interface       host_if,
  order_interface      order_if
);

  // Decode Shadow register interface
  avalon_if #(.DATA_WIDTH  (MSG_WIDTH),
              .EMPTY_WIDTH ($clog2(MSG_WIDTH))
             ) dec_shdw_if();

  avalon_if #(.DATA_WIDTH  (MSG_WIDTH),
              .EMPTY_WIDTH ($clog2(MSG_WIDTH))
             ) curr_dec_if();

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
    reg          use_shdw;
    reg  [13 :0] tts_rd_addr;
    reg  [2  :0] sym_idx;

    wire         sef_rd_srcb, sef_rd_prcb, sef_rd_vrcb, sef_rd_orcb;
    wire         sef_pcmp_load_a, sef_pcmp_load_b, sef_vcmp_load_a, sef_vcmp_load_b;
    wire         sef_out_valid;
    wire         pcmp_pass, vcmp_pass;

    wire [63 :0] srcb_data, vrcb_data;
    wire [127:0] prcb_data, orcb_data;

  //------------------------------------------------------------------------------------------------------------------
  // Shadow the incoming decode interface for ready absorbtion
  //------------------------------------------------------------------------------------------------------------------
  always_ff @(posedge clk) begin
    if          (!reset_n) begin
      dec_shdw_if.ready         <= 1'b0;
      dec_shdw_if.valid         <= 1'b0;
      dec_shdw_if.startofpacket <= 1'b0;
      dec_shdw_if.endofpacket   <= 1'b0;
      dec_shdw_if.data          <= 1'b0;
      dec_shdw_if.empty         <= 1'b0;
    end else if (dec_if.valid) begin
      dec_shdw_if.ready         <= dec_if.ready;
      dec_shdw_if.valid         <= dec_if.valid;
      dec_shdw_if.startofpacket <= dec_if.startofpacket;
      dec_shdw_if.endofpacket   <= dec_if.endofpacket;
      dec_shdw_if.data          <= dec_if.data;
      dec_shdw_if.empty         <= dec_if.empty;
    end
  end

  // Always expect valid deassertion to follow ready deasertion
  always_ff @(posedge clk) begin
    if      (!reset_n)                     use_shdw <= 1'b0;
    else if (dec_if.valid & !dec_if.ready) use_shdw <= 1'b1;
    else                                   use_shdw <= 1'b0;
  end

  assign curr_dec_if.ready         = use_shdw ? dec_shdw_if.ready         : dec_if.ready;
  assign curr_dec_if.valid         = use_shdw ? dec_shdw_if.valid         : dec_if.valid;
  assign curr_dec_if.startofpacket = use_shdw ? dec_shdw_if.startofpacket : dec_if.startofpacket;
  assign curr_dec_if.endofpacket   = use_shdw ? dec_shdw_if.endofpacket   : dec_if.endofpacket;
  assign curr_dec_if.data          = use_shdw ? dec_shdw_if.data          : dec_if.data;
  assign curr_dec_if.empty         = use_shdw ? dec_shdw_if.empty         : dec_if.empty;

  //------------------------------------------------------------------------------------------------------------------
  // HPB (Host Protocol Block)
  // Responsible for converting host requests into RAM writes
  //------------------------------------------------------------------------------------------------------------------
  hpb # (
   .HPB_DATA_WIDTH      ( HPB_DATA_WIDTH ),
   .HPB_ASYNC_HOST      ( HPB_ASYNC_HOST )
  ) hpb_i (

    // Clock/Reset
    .clk                (clk),
    .reset_n            (reset_n),

    .aclk               (aclk),
    .areset_n           (areset_n),

    .host_if            (host_if),

    .srcb_hpb_if        (srcb_hpb_if),
    .prcb_hpb_if        (prcb_hpb_if),
    .vrcb_hpb_if        (vrcb_hpb_if),
    .orcb_hpb_if        (orcb_hpb_if)

  );

  //------------------------------------------------------------------------------------------------------------------
  // SEF (Strategy Execution FSM)
  // Controls RAM reads and final trade execution
  //------------------------------------------------------------------------------------------------------------------
  sef sef_i (
    // Clk/Reset
    .clk               (clk),
    .reset_n           (reset_n),

    // Feed Decoder IF
    .dec_if            (curr_dec_if),

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
    .order_if_ready    (order_if.ready),
    .sef_rd_orcb       (sef_rd_orcb),
    .sef_out_valid     (sef_out_valid)
);

  //------------------------------------------------------------------------------------------------------------------
  // Symbol Translation
  //
  // Each SymbolID is translated into a Physical address used to
  // index into the parameter RAMs for comparison with the message field
  //
  //------------------------------------------------------------------------------------------------------------------
  rcb # (
   .RCB_RAM_ADDR_WIDTH  (SRCB_ADDR_WIDTH),
   .RCB_RAM_WIDTH       (SRCB_RAM_WIDTH)
  ) srcb_i (

    // Clock/Reset
    .clk                (clk),
    .reset_n            (reset_n),

    .t2t_rd_addr        (curr_dec_if.dec_data.beat1.symid[13:0]),  // Read address is the Symbol ID
    .sef_read           (sef_rd_srcb),

    .rcb_data           (srcb_data),

    .hpb_if_i           (srcb_hpb_if)

  );

  // Since the Symbol RCB is a library component, a little bit of
  // muxing needs to be done in the wrapper to extract the correct address
  // if this produces a bad timing path, the sRCB could be customized
  // and the byte muxing done prior to the register
  always @(posedge clk) begin
    if      (!reset_n)    sym_idx <= 2'b00;
    else if (sef_rd_srcb) sym_idx <= curr_dec_if.dec_data.beat1.symid[15:14];
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
  // Price Path
  // Responsible for reading out price parameters from its RAM and 
  // comparing against the incoming price field
  //------------------------------------------------------------------------------------------------------------------
  rcb # (
   .RCB_RAM_ADDR_WIDTH ( PRCB_ADDR_WIDTH ),
   .RCB_RAM_WIDTH      ( PRCB_RAM_WIDTH  )
  ) prcb_i (

    // Clock/Reset
    .clk               (clk),
    .reset_n           (reset_n),

    .t2t_rd_addr       (tts_rd_addr),
    .sef_read          (sef_rd_prcb),

    .rcb_data          (prcb_data),

    .hpb_if_i          (prcb_hpb_if)

  );

  cmp # (
   .CMP_RAM_WIDTH    (PRCB_RAM_WIDTH),
   .CMP_CYCA_WIDTH   (MSG_SYMID), // This is because the end of the previous field defines
                                  // the size of the next field, in this case the Price field
   .CMP_REG_CYCB     (1),
   .CMP_PIPE         (1)
  ) pcmp_i (

    // Clock/Reset
    .clk              (clk),
    .reset_n          (reset_n),

    .rcb_data         (prcb_data),
    .tts_field        ({curr_dec_if.dec_data.beat1.price_up, curr_dec_if.dec_data.beat2.price_dn}),

    .sef_load_a       (sef_pcmp_load_a),
    .sef_load_b       (sef_pcmp_load_b),

    .cmp_pass         (pcmp_pass)

  );

  //------------------------------------------------------------------------------------------------------------------
  // Volume Path
  // Responsible for reading the volume parameters from the VRCB
  // and comparing against the incoming Volume field
  //------------------------------------------------------------------------------------------------------------------
  rcb # (
   .RCB_RAM_ADDR_WIDTH (VRCB_ADDR_WIDTH ),
   .RCB_RAM_WIDTH      (VRCB_RAM_WIDTH  )
  ) vrcb_i (

    // Clock/Reset
    .clk               (clk),
    .reset_n           (reset_n),

    .t2t_rd_addr       (tts_rd_addr),
    .sef_read          (sef_rd_vrcb),

    .rcb_data          (vrcb_data),

    .hpb_if_i          (vrcb_hpb_if)

  );

  cmp # (
   .CMP_RAM_WIDTH    (VRCB_RAM_WIDTH),
   .CMP_CYCA_WIDTH   (MSG_PRICE), // This is because the end of the previous field defines
                                  // the size of the next field, in this case the Volume field
   .CMP_REG_CYCB     (0),
   .CMP_PIPE         (0)
  ) vcmp_i (

    // Clock/Reset
    .clk              (clk),
    .reset_n          (reset_n),

    .rcb_data         (vrcb_data),
    .tts_field        ({curr_dec_if.dec_data.beat2.vol_up, curr_dec_if.dec_data.beat3.vol_dn}),

    .sef_load_a       (sef_vcmp_load_a),
    .sef_load_b       (sef_vcmp_load_b),

    .cmp_pass         (vcmp_pass)

  );

  //------------------------------------------------------------------------------------------------------------------
  // Order Path
  // Responsible from reading the Order information from
  // The ORCB and sending onto the Order interface
  // if all conditions are met.
  //------------------------------------------------------------------------------------------------------------------
  rcb # (
   .RCB_RAM_ADDR_WIDTH (ORCB_ADDR_WIDTH ),
   .RCB_RAM_WIDTH      (ORCB_RAM_WIDTH  )
  ) orcb_i (

    // Clock/Reset
    .clk               (clk),
    .reset_n           (reset_n),

    .t2t_rd_addr       (tts_rd_addr),
    .sef_read          (sef_rd_orcb),

    .rcb_data          (orcb_data),

    .hpb_if_i          (orcb_hpb_if)

  );

  always @(posedge clk) begin
    if (!reset_n) begin
      order_if.valid <= 1'b0;
      order_if.data  <= '0;
    end else begin
      order_if.valid <= sef_out_valid & vcmp_pass & pcmp_pass;
      order_if.data  <= orcb_data;
    end
  end

  assign dec_if.ready = order_if.ready; // The tts does not incur stalls

endmodule // tts
