//////////////////////////////////////////////////////////////////////////////
// stimulus_c - the basic transaction(stimulus) object.
//////////////////////////////////////////////////////////////////////////////
class host_item extends uvm_sequence_item;

  //Register with the Factory
  `uvm_object_utils(host_item)

  const string report_id = "HOST_ITEM";

  //256-bit data to be sent over host interface
  rand bit [255:0] data;

  function new(string name = "host_item");
    super.new(name);   
  endfunction : new

  
  //In order to get debug or status information printed to a simulator
  // transcript or a log file from a data object there needs to be a way to 
  // convert the objects contents into a string representation - this is the 
  // purpose of the convert2string() method. Calling the method will return a
  // string detailing the values of each of the properties formatted for 
  // displaying or writing to a file. The format is determined by the user.
  function string convert2string();
    // Note you could use \t (tab) and \n (newline) to format the data in
    // columns.  The enumerated op_code types .name() method returns a
    // string corresponding to its value
    //Update to use union to show data in different ways
    return $sformatf("Data: 0x%032x", data);
  endfunction : convert2string


  //The do_print() method is called by the uvm_object print() method. Its 
  // original purpose was to print out a string representation of an uvm data 
  // object using one of the uvm_printer policy classes. However, a higher 
  // performance version of the same functionality can be achieved by 
  // implementing the method as a wrapper around a $display() call that takes 
  // the string returned by a convert2string() call as an argument.
  function void do_print(uvm_printer printer);
    if(printer.knobs.sprint == 0) begin
      $display(convert2string());
    end
    else begin
      printer.m_string = convert2string();
    end 
  endfunction: do_print

  
  //The do_compare method is called by the uvm_object compare() method and it
  // is used to compare two data objects of the same type to determine 
  // whether their contents are equal. The do_compare() method should only be 
  // coded for those properties which can be compared.
  //The uvm_comparer policy object has to be passed to the do_compare() 
  // method for compatability with the virtual method template, but it is not 
  // necessary to use it in the comparison function and performance can be 
  // improved by not using it.
  function bit do_compare(uvm_object rhs, uvm_comparer comparer);
    host_item rhs_;
    
    //If the cast fails, comparison has also failed
    //A check for null is not needed because that is done in the compare()
    // function which calls do_compare()
    if (!$cast(rhs_, rhs)) return 0;
    
    //This is a bit contrived because it compares a write cycle to a read 
    // cycle so the data is on a different bus.  It would probably be better
    // to move to just "data" at this level and let the driver work out if 
    // it is to or from at the pin level
    return (super.do_compare(rhs, comparer) &&
          (data == rhs_.data));
  endfunction : do_compare
         

  //The purpose of the do_copy method is to provide a means of making a deep 
  // copy of a data object.  The do_copy method is either used on its own or 
  // via the uvm_objects clone() method which allows independent duplicates 
  // of a data object to be created.
  //Note that the rhs argument is of type uvm_object since it is a virtual 
  // method, and that it therefore needs to be cast to the actual transaction
  // type before its fields can be copied. A design consideration for this 
  // method is that it may not always make sense to copy all property values 
  // from one object to another.
  function void do_copy(uvm_object rhs);
    host_item rhs_;

    if(!$cast(rhs_, rhs)) begin
      `uvm_fatal(report_id, "Cast failed in do_copy()");
      return;
    end
    
    super.do_copy(rhs); // Chain the copy with parent classe
    data = rhs_.data;
  endfunction :do_copy

  /* Use the default clone
  function uvm_object clone();
    host_item t = new this;  //Shallow Copy
    `uvm_info(report_id, "cloning", UVM_LOW)
    return t;
  endfunction : clone*/


  //The do_report() method is intended to support the viewing of data objects 
  // as transactions in a waveform GUI. Like the printing data object 
  // methods, the principle is that the fields that are recorded are visible 
  // in the transaction viewer. The underlying implementation of the 
  // do_record() method is simulator specific and for Questa involves the use 
  // of the $add_attribute() system call.
  //In order to get transaction viewing to work with Questa you need to:
  //  * Implement the do_report() method as shown
  //  * Use the Questa uvm closed kit - i.e. The compiled version of UVM 
  //   shipped with Questa
  //  * Set the recording_detail config item to UVM_FULL in your test or env
  //   set_config_int("*", "recording_detail", UVM_FULL);
  //   uvm_config_db#(int)::set(this, "*", "recording_detail", UVM_FULL);
  
  // do_record:
  function void do_record(uvm_recorder recorder);
    super.do_record(recorder); // To record any inherited data members
    `uvm_record_field("data", data)
  endfunction : do_record
  
endclass : host_item
