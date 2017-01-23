////////////////////////////////////////////////////////////////////////////
// host_driver - the memory agent driver
////////////////////////////////////////////////////////////////////////////
class host_driver extends uvm_driver #(host_item);
  
  //Register with the Factory
  `uvm_component_utils(host_driver)

  const string report_id = "HOST_DRIVER";
  
  // stimulus handle
  REQ                       transaction_h;

  //Done bit
  bit                       done = 1;

  //Config object handle
  host_config                host_cfg_h;
  
  // virtual interface
  virtual host_interface     host_interface_h;
  
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new
  
  function void build_phase(uvm_phase phase);
    //super.build_phase(phase);  //Don't call - Large Performance Impact
    //Get the config object
  endfunction : build_phase
  
  function void connect_phase(uvm_phase phase);
    if (host_cfg_h == null)
      `uvm_fatal(report_id, "Agent did not push config down to Driver")
    else
      host_interface_h = host_cfg_h.host_intf;
  endfunction : connect_phase
  
  task run_phase(uvm_phase phase);
    `uvm_info(report_id,  "running memory agent driver",UVM_LOW )
    // set everything to zero before the reset
    host_interface_h.in_config_valid    <= '0;
    host_interface_h.in_config_data     <= '0;
    
    // Wait for reset to deassert.....
    @(posedge host_interface_h.reset_n);
    //Now go into a loop to service sequences to communicate
    forever @(posedge host_interface_h.clk) begin
      
      // Tell the sequencer that we need a new transaction
      seq_item_port.get_next_item(transaction_h);
      done = 0;

      host_interface_h.in_config_valid <= 1;
      host_interface_h.in_config_data  <= transaction_h.data;
      //Could add a timeout on the accept signal
      while (host_interface_h.in_config_accept == 0)
        @(posedge host_interface_h.clk);
      host_interface_h.in_config_valid <= 0;
      host_interface_h.in_config_data <= $urandom();
      
      done = 1;
      seq_item_port.item_done();
      
    end    // forever     
  endtask : run_phase

  //Implementing the phase_ready_to_end function to check if we are done
  // sending a transaction when we are ready to end simulation.  We check
  // for the post_shutdown_phase because that is running in parallel with the
  // run_phase and the run_phase won't end until the post_shutdown_phase ends.
  function void phase_ready_to_end(uvm_phase phase);
    if (!done && phase.is(uvm_post_shutdown_phase::get())) begin
      fork
        wait_for_done(phase);
      join_none
    end
  endfunction : phase_ready_to_end
  
  
  task wait_for_done(uvm_phase phase);
    phase.raise_objection(this, "Giving Host Driver extra time to finish");
    fork
      wait (done == 1);
      begin
        #10000;
        `uvm_error(report_id, "Timed Out waiting for Transaction to finish")
      end
    join_any
    disable fork;
    phase.drop_objection(this, "Finished giving Host Driver extra time to finish");
  endtask : wait_for_done
  
endclass : host_driver
