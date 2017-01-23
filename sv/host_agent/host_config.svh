////////////////////////////////////////////////////////////////////////////
// host_config - The config class for the host_agent
////////////////////////////////////////////////////////////////////////////
class host_config extends uvm_object;
  //Register with the factory
  `uvm_object_utils(host_config)

  //Virtual Interface Handle
  virtual host_interface             host_intf;

  //Specify the config values
  uvm_active_passive_enum    active = UVM_ACTIVE;

  // Convenience function that first gets the object out of the UVM database
  // and reports an error if the object is not present in the database, then
  // casts it to the correct config object type, again checking for errors
  static function host_config get_config( uvm_component comp, string cfg_name = "host_cfg");
    string report_id = "HOST_CONFIG";
    host_config host_cfg_h;
    
    if( !uvm_config_db#(host_config)::get(comp, "", cfg_name , host_cfg_h) ) begin
      comp.uvm_report_error( report_id, $sformatf("Cannot get() configuration %s from uvm_config_db. Have you set() it?", cfg_name),,`__FILE__, `__LINE__ );
      return null;
    end
    return host_cfg_h;
  endfunction : get_config
  
endclass : host_config
