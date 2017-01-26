// ---------------------------------------------------------------------------
//
//  Description: RAM Control block responsible for arbitrating between Symbol
//               lookup (RAM Reads) and host configuration (RAM writes)
//
// ---------------------------------------------------------------------------

import tts_pkg::*;

module hpb
#(
  parameter HPB_DATA_WIDTH      = 128,                        // Width of incoming host block
  parameter HPB_ASYNC_HOST      = 0                           // Indicates if CDC is required
) (

  // Clk/Reset
  input                                   clk,                // Core clock
  input                                   reset_n,            // Active low core reset

  input                                   aclk,               // Host Asynch Clk
  input                                   areset_n,           // Host Asycn Reset

  // Feed Decoder IF
  host_interface                          host_interface_in,  // Host Interface on Async Clock

  hpb_if                                  srcb_hpb_if,      // Symbol RCB RAM Interface
  hpb_if                                  prcb_hpb_if,      // Price RCB RAM Interface
  hpb_if                                  vrcb_hpb_if,      // Volume RCB RAM Interface
  hpb_if                                  orcb_hpb_if       // Order RCB RAM Interface

);


  host_interface  host_interface_synced();   // Host interface synchronized to core clock
  t_host_msg_map  host_msg_map;              // Struct holding host payload fields

  //-----------------------------------------------------------------------------------
  // HDP Sync - Synchronizes Host IF to core clock
  //-----------------------------------------------------------------------------------
  hpb_sync hpb_sync_i (
                       .clk      (clk),
                       .reset_n  (reset_n),
                       .aclk     (aclk),
                       .areset_n (areset_n),
    .host_interface_in         ( host_interface_in ),
    .host_interface_synced     ( host_interface_synced )
  );

  //-------------------------------------------------
  // Strip out the payload fields
  //-------------------------------------------------
  always_ff @(posedge clk) begin
    if (!reset_n) begin
      host_msg_map <= '0;
    end else if (host_interface_synced.in_config_valid) begin
      host_msg_map.cmd     <= host_interface_synced.in_config_data[CMD_B     +:CMD_NUM_BYTES*8];
      host_msg_map.ram     <= host_interface_synced.in_config_data[RAM_B     +:RAM_NUM_BYTES*8];
      host_msg_map.addr    <= host_interface_synced.in_config_data[ADDR_B    +:ADDR_NUM_BYTES*8];
      host_msg_map.res     <= host_interface_synced.in_config_data[RES_B     +:RES_NUM_BYTES*8];
      host_msg_map.byte_en <= host_interface_synced.in_config_data[BYTE_EN_B +:BYTE_EN_NUM_BYTES*8];
      host_msg_map.data    <= host_interface_synced.in_config_data[DATA_B    +:DATA_NUM_BYTES*8];
    end
  end

  //-------------------------------------------------
  // Drive the output IFs
  // Data on output IFs is either 64 or 128. Dropping
  // the remaining
  //-------------------------------------------------
  always_comb begin
    srcb_hpb_if.hpb_wr_addr    = host_msg_map.addr;
    srcb_hpb_if.hpb_wr_data    = host_msg_map.data;
    srcb_hpb_if.hpb_wr_byte_en = host_msg_map.byte_en;

    prcb_hpb_if.hpb_wr_addr    = host_msg_map.addr;
    prcb_hpb_if.hpb_wr_data    = host_msg_map.data;
    prcb_hpb_if.hpb_wr_byte_en = host_msg_map.byte_en;

    vrcb_hpb_if.hpb_wr_addr    = host_msg_map.addr;
    vrcb_hpb_if.hpb_wr_data    = host_msg_map.data;
    vrcb_hpb_if.hpb_wr_byte_en = host_msg_map.byte_en;

    orcb_hpb_if.hpb_wr_addr    = host_msg_map.addr;
    orcb_hpb_if.hpb_wr_data    = host_msg_map.data;
    orcb_hpb_if.hpb_wr_byte_en = host_msg_map.byte_en;
  end

  //-------------------------------------------------
  // Drive the WR_REQ depending on target RAM
  //-------------------------------------------------
  always_comb begin
    srcb_hpb_if.hpb_wr_req = 'b0;
    prcb_hpb_if.hpb_wr_req = 'b0;
    vrcb_hpb_if.hpb_wr_req = 'b0;
    orcb_hpb_if.hpb_wr_req = 'b0;

    case (host_msg_map.ram)
      tts_pkg::SRCB: srcb_hpb_if.hpb_wr_req = 'b1;
      tts_pkg::PRCB: prcb_hpb_if.hpb_wr_req = 'b1;
      tts_pkg::VRCB: vrcb_hpb_if.hpb_wr_req = 'b1;
      tts_pkg::ORCB: orcb_hpb_if.hpb_wr_req = 'b1;
      default begin
        $error ("Invalid RAM Selection: 8'h%0h", host_msg_map.ram);
      end
    endcase
  end

  //-------------------------------------------------
  // Hold Write until WR_DONE asserted for the
  // targeted RCB
  //-------------------------------------------------
  always_ff @(posedge clk) begin
    if (!reset_n) begin
      host_interface_synced.in_config_accept <= 'b0;
    end else begin
      case (host_msg_map.ram)

        // Sybmol RCB
        tts_pkg::SRCB:
        begin
          if (srcb_hpb_if.rcb_wr_done) begin
            host_interface_synced.in_config_accept <= 'b1;
          end else begin
            host_interface_synced.in_config_accept <= 'b0;
          end
        end

        // Price RCB
        tts_pkg::PRCB:
        begin
          if (prcb_hpb_if.rcb_wr_done) begin
            host_interface_synced.in_config_accept <= 'b1;
          end else begin
            host_interface_synced.in_config_accept <= 'b0;
          end
        end

        // Volume RCB
        tts_pkg::VRCB:
        begin
          if (vrcb_hpb_if.rcb_wr_done) begin
            host_interface_synced.in_config_accept <= 'b1;
          end else begin
            host_interface_synced.in_config_accept <= 'b0;
          end
        end

        // Order RCB
        tts_pkg::ORCB:
        begin
          if (orcb_hpb_if.rcb_wr_done) begin
            host_interface_synced.in_config_accept <= 'b1;
          end else begin
            host_interface_synced.in_config_accept <= 'b0;
          end
        end

        default begin
          $error ("Invalid RAM Selection: 8'h%0h", host_msg_map.ram);
        end
      endcase


    end

  end

endmodule // hpb
