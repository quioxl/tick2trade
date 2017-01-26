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
  parameter MSG_TYPE_BYTES  = 3;
  parameter MSG_SYMID_BYTES = 2;
  parameter MSG_PRICE_BYTES = 8;
  parameter MSG_VOL_BYTES   = 4;

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
    bit [MSG_WIDTH-1:MSG_TYPE]  msg_type;
    bit [MSG_TYPE-1 :MSG_SYMID] symid;
    bit [MSG_SYMID-1:0]         price_up;
  } t_msg_beat1;

  typedef struct packed {
    bit [MSG_WIDTH-1:MSG_PRICE] price_dn;
    bit [MSG_PRICE-1:0]         vol_up;
  } t_msg_beat2;

  typedef struct packed {
    bit [MSG_WIDTH-1:MSG_VOL] vol_dn;
    bit [MSG_VOL-1  :0]       unused;
  } t_msg_beat3;

  typedef union packed {
    t_msg_beat1                 beat1;
    t_msg_beat2                 beat2;
    t_msg_beat3                 beat3;
    bit         [MSG_WIDTH-1:0] raw;
  } t_dec_msg;

  // Message Type encoding
  parameter  MSG_NEW           = 24'h4E_45_57; // ASCII "NEW"

endpackage
