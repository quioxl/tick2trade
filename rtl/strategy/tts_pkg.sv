// ---------------------------------------------------------------------------
//
//  Copyright 2014 IMC. All Rights Reserved.
//
//  Description: Common elements to the Strategy blocks
//
// ---------------------------------------------------------------------------
package tts_pkg;

  // Start offsets for fields in payload
  parameter  CMD_B             = 248;
  parameter  RAM_B             = 240;
  parameter  ADDR_B            = 224;
  parameter  RES_B             = 216;
  parameter  BYTE_EN_B         = 192;
  parameter  DATA_B            = 0;

  // Number of bytes in field
  parameter  CMD_NUM_BYTES     = 1;
  parameter  RAM_NUM_BYTES     = 1;
  parameter  ADDR_NUM_BYTES    = 2;
  parameter  RES_NUM_BYTES     = 1;
  parameter  BYTE_EN_NUM_BYTES = 3;
  parameter  DATA_NUM_BYTES    = 24;

  typedef enum bit [7:0] {
    SRCB = 8'd1,             // Symbol RCB
    PRCB = 8'd2,             // Price RCB
    VRCB = 8'd4,             // Volume RCB
    ORCB = 8'd8              // Order RCB
  } t_RAM_ENCODING;

  typedef enum {
    WAIT,
    LD,
    CMP
  } t_sef_st;

  typedef struct packed {
    logic         [CMD_NUM_BYTES*8-1:0] cmd;
    logic         [RAM_NUM_BYTES*8-1:0] ram;
    logic          [ADDR_NUM_BYTES*8:0] addr;
    logic           [RES_NUM_BYTES*8:0] res;
    logic     [BYTE_EN_NUM_BYTES*8-1:0] byte_en;
    logic        [DATA_NUM_BYTES*8-1:0] data;
  } t_host_msg_map;

endpackage