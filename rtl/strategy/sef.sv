// ---------------------------------------------------------------------------
//
//  Description: Strategy Execution FSM (SEF) is responsible for controlling
//               RAM reads, loading comparators and rubber stamping the
//               outgoing order.
//
// ---------------------------------------------------------------------------

import t2t_pkg::*;
import tts_pkg::*;

module sef
#(
) (

  // Clk/Reset
  input          clk,                // Core clock
  input          reset_n,            // Active low core reset

  // Feed Decoder IF
  avalon_if      dec_if,

  // Symbol ID RCB
  output bit     sef_rd_srcb,
  input  bit     tts_sym_vld,

  // Price Path (RCB & CMP)
  output bit     sef_rd_prcb,
  output bit     sef_pcmp_load_a,
  output bit     sef_pcmp_load_b,

  // Volume Path (RCB & CMP)
  output bit     sef_rd_vrcb,
  output bit     sef_vcmp_load_a,
  output bit     sef_vcmp_load_b,

  // Order RCB
  output bit     sef_rd_orcb,
  output bit     sef_out_valid
);

  t_sef_st  state;

  bit       new_msg;

  // Only want to read the symbol ID when a new message comes in so
  // the Host Protocol Block can write it on other cycles
  assign sef_rd_srcb = (state == WAIT) & (dec_if.dec_data.beat1.msg_type == MSG_NEW);

  assign sef_rd_prcb     = (state == LD);
  assign sef_pcmp_load_a = (state == WAIT);
  assign sef_pcmp_load_b = (state == LD);

  assign sef_rd_vrcb     = (state == LD);
  assign sef_vcmp_load_a = (state == LD);
  assign sef_vcmp_load_b = (state == CMP);

  assign sef_rd_orcb     = (state == LD);
  assign sef_out_valid   = (state == CMP);

  assign new_msg = dec_if.valid & dec_if.startofpacket & (dec_if.dec_data.beat1.msg_type == MSG_NEW);

  always @(posedge clk) begin
    if (!reset_n)                        state <= WAIT;
    else begin
      case (state)
        WAIT    : begin
                  if (new_msg)           state <= LD;
                  else                   state <= WAIT;
                  end
        LD      : begin
                  if      (!tts_sym_vld) state <= WAIT; // If there isn't a valid symbol ID translation, abort
                  else if (dec_if.valid) state <= CMP;
                  else                   state <= LD;
                  end
        CMP     : begin
                  if (dec_if.valid)      state <= WAIT;
                  else                   state <= CMP;
                  end
        default :                        state <= WAIT;
      endcase
    end
  end

endmodule // sef
