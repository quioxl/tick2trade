// The layering agent consists of a sequencer but no actual driver; instead this
// agent creates and starts a special "layering" sequence whose job is to act
// like a driver in handshaking with a sequencer (up_seqr in this case) and 
// sending resulting transactions to a downstream sequencer (avalon_seqr_h)
class feed_layering extends uvm_component;
  `uvm_component_utils(feed_layering)

  function new(string name, uvm_component parent);
    super.new(name,parent);
  endfunction

  uvm_sequencer #(avalon_message_item) feed_message_seqr_h;
  uvm_sequencer #(avalon_seq_item_base) avalon_seqr_h;

  virtual task run_phase(uvm_phase phase);
    feed_message_to_avalon_seq seq_h;
    seq_h = feed_message_to_avalon_seq::type_id::create("seq_h");
    seq_h.up_seqr = feed_message_seqr_h;
    seq_h.start(avalon_seqr_h);
  endtask

endclass