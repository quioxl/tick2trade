// ---------------------------------------------------------------------------
//
//  Description: Feed Decoder
//
// ---------------------------------------------------------------------------
module feed_decoder #(
  // Design Parameters {{{
  parameter int C_PKT_DATA_WIDTH  = 64,
  parameter int C_PKT_EMPTY_WIDTH = $clog2(C_PKT_DATA_WIDTH/8)
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

  parameter PKT_SOP_MSG_BYTE = 4;
  parameter PKT_SOP_MSG_BIT  = 32;
  
  // LEN PTR is actually pointing to the byte before the length
  // field as eom would do on previous messages, if they existed.
  parameter LEN_PTR_START = 1;
  parameter MSG_PTR_START = 4; // Starts after the length

  typedef struct packed {
    logic        sop;
    logic        eop;
    logic        vld;
    logic        som;
    logic [63:0] data;
  } t_beat;
  
  t_beat        old_beat, new_beat, shadow_beat;

  logic  [5:0]  rd_ptr, nxt_rd_ptr, eom_ptr, eom_incr, que_ptr;
  logic  [5:0]  eom_rd_diff, eom_que_diff;
  logic [15:0]  nxt_len;
  logic         update_old_beat, get_new_beat, stall_out, ld_from_shadow;
  logic         vld_nxt, eom_nxt;
  logic         ld_ptrs, dly_ld;
  logic         eom_in_old, som_hold, eom_at_end, eom_then_som, get_from_old;
  logic  [2:0]  length_ptr;

  // ------------------------------------------------------------------------
  // Data path
  // ------------------------------------------------------------------------

  // The shadow beat is for cases where there is ready deassertion effecting
  // the pipe. In that case, the block will pull from the shadow register in 
  // the next cycle.
  always @(posedge clk) begin
    if (!reset_n) shadow_beat <= '0;
    else if (in_valid) begin
      shadow_beat.sop  <= in_startofpacket;
      shadow_beat.eop  <= in_endofpacket;
      shadow_beat.vld  <= in_valid;
      shadow_beat.som  <= 1'b0;
      shadow_beat.data <= in_data;
    end
  end

  // ASSERTION : Check that ld_from_shadow is never cleared
  //             if get_new_beat isn't set.
  always @(posedge clk) begin
    if      (!reset_n)             ld_from_shadow <= 1'b0;
    // else if (in_valid && !in_ready && new_beat.vld) ld_from_shadow <= 1'b1;
    else if (in_valid && !in_ready && !get_new_beat) ld_from_shadow <= 1'b1;
    else if (get_new_beat)         ld_from_shadow <= 1'b0;
  end

  // This is the data queue everything is pulled from. It can be visualized
  // as the old_beat sitting atop the new_beat. We need to take in a new 
  // beat if it is marked valid on the bus, or if we are sending a message
  // beat and the current invalid isn't our request for delay.
  // CAREFUL : new_beat.som is written by a continuous as the decision
  //           must be made later.
  always @(posedge clk) begin
    if (!reset_n) begin
      new_beat.sop  <= 1'b0;
      new_beat.eop  <= 1'b0;
      new_beat.vld  <= 1'b0;
      new_beat.data <= '0;
    end else if (get_new_beat) begin
      new_beat.sop  <= ld_from_shadow ? shadow_beat.sop  : in_startofpacket;
      new_beat.eop  <= ld_from_shadow ? shadow_beat.eop  : in_endofpacket;
      new_beat.vld  <= ld_from_shadow ? shadow_beat.vld  : in_valid;
      new_beat.data <= ld_from_shadow ? shadow_beat.data : in_data;
    end
  end

  // We know there is a new message starting if:
  // 1. The new message beat is valid AND
  //   1. There is an sop OR
  //   2. The eom ptr is between 5 and 12 bytes
  //      from the top of the queue
  assign new_beat.som = new_beat.vld & (new_beat.sop | (eom_que_diff inside {[5:12]}));

  always @(posedge clk) begin
    if (!reset_n)        old_beat <= '0;
    if (update_old_beat) old_beat <= new_beat;
  end

  // We need to take in a new beat if:
  // 1. It is marked valid on the bus
  // 2. The new beat is moving to the old beat
  assign get_new_beat    = !new_beat.vld | update_old_beat;

  // We need to take in a update the old beat if:
  // 1. Old beat is invalid
  // 2. next message cycle is valid AND the first beat
  //    of a new message isn't in the old_beat
  // 3. If the last beat of the previous message completed
  //    But the som will be in the new_beat on the next cycle
  // 4. If the eom was already issued for the last message of the 
  //    packet
  // 5. If the eom for the last message of the packet is able to
  //    go out
  assign update_old_beat = !old_beat.vld | 
                           (vld_nxt & !som_hold) | (old_beat.eop & (vld_nxt | (out_valid & out_endofpacket))) |
                           dly_ld;

  // Read pointer should always be sitting within the old_beat, read data is
  // 8-bytes inclusive of the read pointer location.
  always @(posedge clk) begin
    if (!reset_n) begin
      out_data <= '0;
    end else begin
      // This always gets mapped because we are relying on the control
      // to gate pointer progress in ready low cycles.
      case (rd_ptr[2:0])
        3'h0   : out_data <=  old_beat.data[63:0];
        3'h1   : out_data <= {old_beat.data[55:0], new_beat.data[63:56]};
        3'h2   : out_data <= {old_beat.data[47:0], new_beat.data[63:48]};
        3'h3   : out_data <= {old_beat.data[39:0], new_beat.data[63:40]};
        3'h4   : out_data <= {old_beat.data[31:0], new_beat.data[63:32]};
        3'h5   : out_data <= {old_beat.data[23:0], new_beat.data[63:24]};
        3'h6   : out_data <= {old_beat.data[15:0], new_beat.data[63:16]};
        3'h7   : out_data <= {old_beat.data[7:0],  new_beat.data[63:8]};
        default: out_data <= 'x;
      endcase
    end
  end

  // --------------------------------------------------------------------
  // Control Path
  // --------------------------------------------------------------------

  // The stall condition is if:
  // 1. The eom pointer is going to be in position 0-4 with
  //    an expected som behind it
  // 2. If we get a stall on the slave i/f cooincident with 
  //    an internal stall we need an additional cycle to 
  //    allow for the som to be sent.
  always @(posedge clk) begin
    if (!reset_n) begin
      stall_out <= 1'b0;
    end else begin
      stall_out <= ((rd_ptr[2:0] <= eom_ptr[2:0]) & (eom_que_diff inside {[8:12]}) & !new_beat.eop) |
                   (stall_out & !out_ready);
    end
  end

  // We send a valid message beat if:
  // 1. There is valid data in both beats OR
  // 2. If the eom_ptr is in the old beat and it is valid...
  // 2a. But, not if eom just occured and the som is not yet available
  // 3. Also need to gate on the eop if the last beat is alreaady on the bus.
  //     ASSERTION : Need to make sure that vld_nxt isn't held (does it matter?)
  //                 AND need to make sure eom isn't missed.
  assign vld_nxt = old_beat.vld & (new_beat.vld | eom_in_old) & 
                   !dly_ld & !(old_beat.eop & !eom_nxt) & out_ready;

  always @(posedge clk) begin
    if (!reset_n) begin
      out_valid         <= 1'b0;
      out_startofpacket <= 1'b0;
      out_endofpacket   <= 1'b0;
      out_empty         <= '0;
    end else begin
      out_valid         <= vld_nxt;
      // Want to send a start if old_beat says start and we aren't finishing up
      out_startofpacket <= old_beat.som & !eom_then_som;
      out_endofpacket   <= eom_nxt;
      out_empty         <= 7 - eom_rd_diff[2:0];
    end
  end

  assign out_error = 1'b0;
  assign in_ready  = out_ready & !stall_out;

  // -------------------------------------------------------------------
  // Pointer Math
  // -------------------------------------------------------------------
  
  // Pointers are a little bit confusing since they 
  // will be counting bytes opposite of byte numbering
  // The input stream can be thought of as one big queue
  // we are just tracking data pointers from top to bottom.
  // Want to load on a new message and increment the pointers
  // whenever a beat goes out. Generally that is when 
  // old_beat updates...unless old_beat is invlaid.

  always @(posedge clk) begin
    if (!reset_n) begin // Need to clear out after packets
      que_ptr <= '0;
      rd_ptr  <= MSG_PTR_START;
      eom_ptr <= MSG_PTR_START-3;
    end else if (ld_ptrs) begin
      que_ptr <= '0;
      rd_ptr  <= nxt_rd_ptr;
      eom_ptr <= nxt_rd_ptr + ({nxt_len[5:0]} -1);
    end else if (update_old_beat & old_beat.vld) begin
      que_ptr <= que_ptr + 8;
      rd_ptr  <= rd_ptr  + 8;
    end
  end

  assign eom_rd_diff  = eom_ptr - rd_ptr;
  assign eom_que_diff = eom_ptr - que_ptr;

  assign eom_nxt      = (eom_rd_diff  < 8) & old_beat.vld;
  assign eom_at_end   = eom_que_diff > 12;
  assign eom_in_old   = eom_que_diff < 8;
  assign eom_then_som = eom_que_diff < 7;
  assign som_hold     = eom_then_som & old_beat.som;

  assign eom_incr     = eom_ptr + 3;
  assign nxt_rd_ptr   = new_beat.sop ? MSG_PTR_START : {3'b0, eom_incr[2:0]};

  // Need to load pointers when:
  // 1. An sop is in the new stage
  // 2. An eom is going out AND
  //    the eom_ptr is not at the end of the queue.
  // If the read pointer is too far down, then need a delayed load
  assign ld_ptrs     = new_beat.sop | ((eom_nxt & vld_nxt & !eom_at_end) & out_ready) | (dly_ld & new_beat.vld);

  // The delayed load allows a pointer far down in the new queue
  // to propagate to the old queue before loading the pointers.
  // In this case, there will be a dead cycle on the bus in
  // order to allow the som to get back up into the old beat.
  // So dly needs to hold off valid and ptr math for a cycle.
  always @(posedge clk) begin
    if (!reset_n) dly_ld <= 0;
    else          dly_ld <= eom_nxt & vld_nxt & eom_at_end;
  end
  

  // When there is an sop in the new beat, we always want to load the
  // new pointers from there, otherwise they load from the two bytes
  // behind the eom pointer.
  assign get_from_old = eom_in_old & !new_beat.sop;
  assign length_ptr   = new_beat.sop ? LEN_PTR_START : eom_ptr[2:0];

  always_comb begin
    // Not defined for cases where the eom pointer
    // is in a position such that not enough data
    // can be loaded to get the length. Will let
    // those cases fall to default so the tools
    // can optimize.
    case ({get_from_old,length_ptr})
      4'b0_000 : nxt_len <= new_beat.data[55:40];
      4'b0_001 : nxt_len <= new_beat.data[47:32];
      4'b0_010 : nxt_len <= new_beat.data[39:24];
      4'b0_011 : nxt_len <= new_beat.data[31:16];
      4'b0_100 : nxt_len <= new_beat.data[23:8] ;
      4'b0_101 : nxt_len <= new_beat.data[15:0] ;

      4'b1_000 : nxt_len <= old_beat.data[55:40];
      4'b1_001 : nxt_len <= old_beat.data[47:32];
      4'b1_010 : nxt_len <= old_beat.data[39:24];
      4'b1_011 : nxt_len <= old_beat.data[31:16];
      4'b1_100 : nxt_len <= old_beat.data[23:8] ;
      4'b1_101 : nxt_len <= old_beat.data[15:0] ;
      4'b1_110 : nxt_len <= {old_beat.data[7:0], new_beat.data[63:56]};
      4'b1_111 : nxt_len <= new_beat.data[63:48];
      default  : nxt_len <= 'x;
    endcase
  end

endmodule
