// Header {{{
// 
// File          : feed_dec_avalon64b.sv
// Date Created  : 01/23/2017
// Creator       : 
// Last Modified : 01/23/2017
// Last Modifier : 
// Version       : 1.0
// Description   : Feed Decoder for IMC Assignment
// References    : IMC Assignment.docx
//                 Feed Decoder Design Spec.docx (FIXME)
// -------------------------------------------------------------------------}}}
// Version Info {{{
// ----------------------------------------------------------------------------
// 1.0
//      - Module Declaration Added
//         - Parameters: C_PKT_DATA_WIDTH, C_DATA_BYTES, C_EMPTY_WIDTH
//         - Ports Added based on IMC Assignment.docx
//         - Header Added
//         - Version Info Added
// ----------------------------------------------------------------------------
// -------------------------------------------------------------------------}}}

module feed_decoder #(
  // Design Parameters {{{
  // - Parameters below added for future scalability/configurability
  // - Parameters listed in bytes, as per bit alignment not supported
  //     C_PKT_DAT_BYTES:
  //       - Defines the width of the packet data interface
  //       - Theoretically Supported Values:
  //         - Minimum is C_MSG_LEN_BYTES+C_MSG_CNT_BYTES
  //           - Code expects to be able to capture the MSG Length and
  //             next MSG Count at SOP
  //       - Tested Values: 8
  //     C_PKT_MAX_BYTES:
  //       - Defines the maximum expected packet size
  //       - Tested Values: 1500
  //   C_MSG_CNT_BYTES   : 8
  //   C_MSG_LEN_BYTES   : 8
  //   C_MSG_MIN_BYTES   : 8
  //   C_MSG_MAX_BYTES   : 32
  parameter int C_PKT_BEAT_BYTES  = 8,
  parameter int C_PKT_MAX_BYTES   = 1500,
  parameter int C_MSG_CNT_BYTES   = 2,
  parameter int C_MSG_LEN_BYTES   = 2,
  parameter int C_MSG_MIN_BYTES   = 8,
  parameter int C_MSG_MAX_BYTES   = 32,
  // -----------------------------------------------------------------------}}}
  // Derived Parameters: {{{
  // These parameters should not be included in the instantiation, they are
  // derived from the above parameters
  parameter int C_PKT_DATA_WIDTH  = C_PKT_BEAT_BYTES*8,
  parameter int C_PKT_EMPTY_WIDTH = $clog2(C_PKT_BEAT_BYTES),
  parameter int C_MSG_LEN_WIDTH   = C_MSG_LEN_BYTES*8,
  parameter int C_MSG_CNT_WIDTH   = C_MSG_CNT_BYTES*8
  // -----------------------------------------------------------------------}}}
) (
  // Ports {{{
  // Clock and Reset
  input  logic                         clk,
  input  logic                         reset_n,
  // Input Packet: Avalon Streaming Interface
  output logic                         in_ready,
  input  logic                         in_valid,
  input  logic                         in_startofpacket,
  input  logic                         in_endofpacket,
  input  logic  [C_PKT_DATA_WIDTH-1:0] in_data,
  input  logic [C_PKT_EMPTY_WIDTH-1:0] in_empty,
  input  logic                         in_error,
  // Output Packet: Avalon Streaming Interface
  input  logic                         out_ready,
  output logic                         out_valid,
  output logic                         out_startofpacket,
  output logic                         out_endofpacket,
  output logic  [C_PKT_DATA_WIDTH-1:0] out_data,
  output logic [C_PKT_EMPTY_WIDTH-1:0] out_empty,
  output logic                         out_error
  // -----------------------------------------------------------------------}}}
);
  // Local Parameters {{{
  localparam int C_MSG_CNT_MAX       = (C_PKT_MAX_BYTES-C_MSG_LEN_BYTES)/
                                       (C_MSG_MIN_BYTES+C_MSG_LEN_BYTES);
  localparam int C_MSG_CNT_MAX_WIDTH = $clog2(C_MSG_CNT_MAX)+1;
  localparam int C_MSG_CNT_LSB       = C_PKT_DATA_WIDTH-C_MSG_CNT_WIDTH;

  localparam int C_MSG_LEN_MAX_WIDTH = $clog2(C_MSG_MAX_BYTES)+1;
  localparam int C_MSG_LEN_INIT_LSB  = C_MSG_CNT_LSB-C_MSG_LEN_WIDTH;
  localparam int C_BYT_SHFT_WIDTH    = $clog2(C_PKT_BEAT_BYTES);
  // -----------------------------------------------------------------------}}}
  // DRC {{{
  // FIXME: Add DRC Error if C_PKT_DATA_WIDTH != 64, not tested
  // -----------------------------------------------------------------------}}}
  // Structures {{{
  // Packet Input Capture Structure
  typedef struct packed {
    logic                             vld;
    logic                             sop;
    logic                             eop;
    //logic   [C_PKT_BEAT_BYTES-1][7:0] dat;
    logic      [C_PKT_DATA_WIDTH-1:0] dat;
    logic     [C_PKT_EMPTY_WIDTH-1:0] emt;
    logic                             err;
  } t_pkt;
  typedef struct packed {
    logic                             err_msg_cnt;
    logic                             err_msg_len;
    logic                             err_eop_early;
    logic                             err_eop_late;
    logic                             err_sop_early;
    logic                             err_sop_eop;
  } t_pkt_err;
  typedef struct packed {
    logic                             active;
    logic                             sop;
    logic                             eop;
    logic   [C_MSG_CNT_MAX_WIDTH-1:0] cnt;
    logic   [C_MSG_LEN_MAX_WIDTH-1:0] len;
    logic     [C_MSG_CNT_MAX_WIDTH:0] cnt_nxt;
    logic     [C_MSG_LEN_MAX_WIDTH:0] len_rem;
    logic     [C_PKT_EMPTY_WIDTH-1:0] off;
    logic     [C_PKT_EMPTY_WIDTH-1:0] off_nxt;
    logic     [C_PKT_EMPTY_WIDTH-1:0] emt;
  } t_msg_state;
  // -----------------------------------------------------------------------}}}
  // Signals {{{
  logic                           shift0_en;
  logic                           shift1_en;
  t_pkt                           pkt[2];
  t_pkt                           msg;
  t_msg_state                     msg_state;
  logic  [C_PKT_DATA_WIDTH*2-1:0] pkt1_pkt0_dat;
  
  // -----------------------------------------------------------------------}}}
  // IN Ready {{{
//  always_ff @(posedge clk) begin
//    if (!reset_n) begin
//      in_ready <= 1'b0;
//    end else begin
//      in_ready <= out_ready;
//    end
// end
  assign in_ready = out_ready;
  always_ff @(posedge clk) begin
    if (!reset_n) begin
      shift0_en <= 1'b0;
    end else begin
      shift0_en <= out_ready;
    end
  end
  assign shift1_en = shift0_en & 
                     (~pkt[1].vld | pkt[0].vld);
  // -----------------------------------------------------------------------}}}
  // Input Packet: Input Registers [Stage 0] {{{
  always_ff @(posedge clk) begin
    if (!reset_n) begin
      pkt[0]     <= '0;
    //end else if (pkt[0].rdy) begin
    end else if (shift0_en) begin
      //pkt[0].rdy <= in_ready;
      pkt[0].vld <= in_valid;
      pkt[0].sop <= in_startofpacket;
      pkt[0].eop <= in_endofpacket;
      pkt[0].emt <= in_empty;
      pkt[0].err <= in_error;
      pkt[0].dat <= in_data;
    end
  end
  // -----------------------------------------------------------------------}}}
  // Input Packet: Input Registers [Stage 1] {{{
  always_ff @(posedge clk) begin
    if (!reset_n) begin
      pkt[1]     <= '0;
    //end else if (pkt[1].rdy && (pkt[0].vld || pkt[1].eop)) begin
    end else if (shift1_en) begin
      //pkt[1].rdy <= (~pkt[1].vld & ~pkt[0].vld) |
      //              ( pkt[0].rdy &  pkt[0].eop);
      pkt[1].vld <= pkt[0].vld;
      pkt[1].sop <= pkt[0].sop;
      pkt[1].eop <= pkt[0].eop;
      pkt[1].emt <= pkt[0].emt;
      pkt[1].err <= pkt[0].err;
      pkt[1].dat <= pkt[0].dat;
    end
  end
  // -----------------------------------------------------------------------}}}
  assign pkt1_pkt0_dat = {pkt[1].dat,pkt[0].dat};
  // MSG State: Next Message State {{{
  always_ff @(posedge clk) begin
    if (!reset_n) begin
      msg_state <= '0;
    end else if (shift0_en && pkt[0].vld) begin
      msg_state.active  <= pkt[0].sop |
                           (msg_state.active & ~pkt[0].eop);
      msg_state.sop     <= pkt[0].sop |
                           (msg_state.active & msg_state.eop);
      msg_state.eop     <= msg_state.active & msg_state.len_rem[C_MSG_LEN_MAX_WIDTH];
      if (pkt[0].sop) begin
        msg_state.cnt     <= pkt[0].dat[C_MSG_CNT_LSB+:C_MSG_CNT_MAX_WIDTH];
      end
      if (pkt[0].sop) begin
        msg_state.cnt_nxt <= {1'b0,pkt[0].dat[C_MSG_CNT_LSB+:C_MSG_CNT_MAX_WIDTH]}-2;
      end else if (msg_state.sop) begin
        msg_state.cnt_nxt <= msg_state.cnt_nxt - 1;
      end
      if (pkt[0].sop) begin
        msg_state.len     <= pkt[0].dat[C_MSG_LEN_INIT_LSB+:C_MSG_LEN_MAX_WIDTH];
        // The counters below count down to -1, which is why there is the extra
        // value subtracted initially
        msg_state.len_rem <= {1'b0,pkt[0].dat[C_MSG_LEN_INIT_LSB+:C_MSG_LEN_MAX_WIDTH]}-
                             C_PKT_BEAT_BYTES-1;
        msg_state.off     <= C_MSG_CNT_BYTES+
                             C_MSG_LEN_BYTES;
        msg_state.off_nxt <= msg_state.off +
                             pkt[0].dat[C_MSG_LEN_INIT_LSB+:C_PKT_EMPTY_WIDTH] +
                             C_MSG_LEN_BYTES;
        msg_state.emt     <= (~pkt[0].dat[C_MSG_LEN_INIT_LSB+:C_PKT_EMPTY_WIDTH])+1'b1;
      end
    end
  end
  // -----------------------------------------------------------------------}}}
  // Output Message: Output Registers [Stage 2] {{{
  
  always_ff @(posedge clk) begin
    if (!reset_n) begin
      msg     <= '0;
    end else if (shift0_en) begin
      msg.vld <= pkt[0].vld & pkt[1].vld & out_ready;
      msg.sop <= msg_state.sop;
      msg.eop <= msg_state.eop;
      msg.emt <= msg_state.emt;
      msg.err <= 1'b0;
      for (int ii=0;ii<C_PKT_BEAT_BYTES;ii++) begin
        msg.dat[ii*8+:8] <= 
          pkt1_pkt0_dat[(C_PKT_DATA_WIDTH-msg_state.off*8)+:8];
      end 
    end
  end
  assign out_valid         = msg.vld;
  assign out_startofpacket = msg.sop;
  assign out_endofpacket   = msg.eop;
  assign out_empty         = msg.emt;
  assign out_error         = msg.err;
  assign out_data          = msg.dat;
  // -----------------------------------------------------------------------}}}
endmodule
