// ---------------------------------------------------------------------------
//
//  Copyright 2014 IMC. All Rights Reserved.
//
//  Description: Common elements to the Tick2Trade blocks
//
// ---------------------------------------------------------------------------
package t2t_pkg;

  // ------------------------------------------------------------
  // Message elements
  // ------------------------------------------------------------
  // Number of bytes in each field
  parameter MSG_TYPE_BYTES   = 3;
  parameter MSG_SYMID_BYTES  = 2;
  parameter MSG_PRICE1_BYTES = 3;
  parameter MSG_PRICE2_BYTES = 5;
  parameter MSG_PRICE_BYTES  = MSG_PRICE1_BYTES + MSG_PRICE2_BYTES;
  parameter MSG_VOL2_BYTES   = 3;
  parameter MSG_VOL3_BYTES   = 1;
  parameter MSG_VOL_BYTES    = MSG_VOL2_BYTES + MSG_VOL3_BYTES;

  // Offsets for message field
  // First beat
  parameter MSG_WIDTH   = 64;
  parameter MSG_TYPE    = 40;
  parameter MSG_SYMID   = 24;
  // Second beat
  parameter MSG_PRICE   = 24;
  // Third beat
  parameter MSG_VOL     = 56;
  
  typedef struct packed {
    bit [(MSG_TYPE_BYTES*8)-1  :0]  msg_type;
    bit [(MSG_SYMID_BYTES*8)-1 :0]  symid;
    bit [(MSG_PRICE1_BYTES*8)-1:0]  price_up;
  } t_msg_beat1;

  typedef struct packed {
    bit [(MSG_PRICE2_BYTES*8)-1:0] price_dn;
    bit [(MSG_VOL2_BYTES*8)-1  :0] vol_up;
  } t_msg_beat2;

  typedef struct packed {
    bit [(MSG_VOL3_BYTES*8)-1:0] vol_dn;
    bit [MSG_VOL-1           :0] unused;
  } t_msg_beat3;

  typedef union packed {
    t_msg_beat1                 beat1;
    t_msg_beat2                 beat2;
    t_msg_beat3                 beat3;
    bit         [MSG_WIDTH-1:0] raw;
  } t_dec_msg;

  // Message Type encoding
  parameter  MSG_NEW           = 24'h4E_45_57; // ASCII "NEW"

  // ------------------------------------------------------------
  // packet structure
  // ------------------------------------------------------------
  typedef struct packed {
    logic      valid;
    logic      sop;
    logic      eop;
    t_dec_msg  data;
  } t_avalon_msg;

endpackage
