// ---------------------------------------------------------------------------
//
//  Description: Performs the async crossing between Host CFG Clock and
//               core clock
//
// ---------------------------------------------------------------------------

module hpb_sync 
#(
  parameter HPB_ASYNC_HOST  = 0                     // Indicates if CDC is required
) (

  // Clk/Reset
  input                      clk,                   // Core clock
  input                      reset_n,               // Active low core reset

  input                      aclk,                  // Host Async Clk
  input                      areset_n,              // Host Async Reset

  // Interfaces
  host_interface             host_if,               // Host Interface on Async Clock
  host_interface             host_sync_if           // Host IF synchronized to core clock

);

generate 
  // Synchronous host clock
  if (HPB_ASYNC_HOST == 0) begin : sync_gen

    always_comb begin
      //Input signals
      host_sync_if.clk              = host_if.clk;
      host_sync_if.reset_n          = host_if.reset_n;
      host_sync_if.in_config_valid  = host_if.in_config_valid;
      host_sync_if.in_config_data   = host_if.in_config_data;

      //Output signals
      host_if.in_config_accept = host_sync_if.in_config_accept;
    end

  // Asynchronous host clock
  end else begin  : async_gen

    // Synchronization stategy:
    // Since host interface already uses a valid/accept handshake -
    // 1. Convert the valid pulses to levels (toggle previous level) in aclk clock domain
    // 2. Double flop this level into the host clock domain 
    // 3. Double flop the data into the host clock domain
    // 4. Use an edge detector in the host clock domain to create the corresponding new valid pulse
    // 5. Data is sent with valid pulse which is safely synchronized to host clock domain
    // 6. Convert accept pulse into level (toggle previous level) in host clock domain
    // 7. Double flop accept pulse in aclk clock domain
    // 8. Use an edge detector in the aclk clock domain to create the corresponding accept pulse

    logic         aclk_valid_level;
    logic         clk_valid0;
    logic         clk_valid1;
    logic         clk_valid2;
    logic [255:0] clk_data0;
    logic [255:0] clk_data1;
    logic         clk_valid_pulse;
    logic         clk_accept_level;
    logic         aclk_accept0;
    logic         aclk_accept1;
    logic         aclk_accept2;
    logic         aclk_accept_pulse;

    // Convert incoming valid pulse to level (toggle) in aclk domain
    always_ff @(posedge aclk) begin
      if (!areset_n) begin
        aclk_valid_level <= 0;
      end else if (host_if.in_config_valid) begin
        aclk_valid_level  <= !aclk_valid_level;
      end
    end

    // Double flop valid and data in host clock domain. Extra valid flop is used for edge detection.
    always_ff @(posedge clk) begin
      if (!reset_n) begin
        clk_valid0  <= 0;
        clk_valid1  <= 0;
        clk_valid2  <= 0;
        clk_data0   <= 0;
        clk_data1   <= 0;
      end else begin
        clk_valid0  <= aclk_valid_level;
        clk_valid1  <= clk_valid0;
        clk_valid2  <= clk_valid1;
        clk_data0   <= host_if.in_config_data;
        clk_data1   <= clk_data0;
      end
    end

    // Edge detector for incoming valid level
    assign valid_edge_detect  = clk_valid1 ^ clk_valid2;

    // Generate pulse from edge detection
    always_ff @(posedge clk) begin
      if (!reset_n) begin
        clk_valid_pulse <= 0;
      end else if (clk_valid_pulse) begin
        clk_valid_pulse <= 0;
      end else if (valid_edge_detect) begin
        clk_valid_pulse <= 1;
      end
    end

    // Convert incoming accept pulse to level (toggle) in clk domain
    always_ff @(posedge clk) begin
      if (!areset_n) begin
        clk_accept_level <= 0;
      end else if (host_sync_if.in_config_accept) begin
        clk_accept_level  <= !clk_accept_level;
      end
    end

    // Double flop accept in aclk clock domain. Extra accept flow is used for edge detection.
    always_ff @(posedge aclk) begin
      if (!reset_n) begin
        aclk_accept0  <= 0;
        aclk_accept1  <= 0;
        aclk_accept2  <= 0;
      end else begin
        aclk_accept0  <= clk_accept_level;
        aclk_accept1  <= aclk_accept0;
        aclk_accept2  <= aclk_accept1;
      end
    end

    // Edge detector for incoming accept level
    assign accept_edge_detect  = aclk_accept1 ^ aclk_accept2;

    // Generate pulse from edge detction
    always_ff @(posedge aclk) begin
      if (!reset_n) begin
        aclk_accept_pulse <= 0;
      end else if (aclk_accept_pulse) begin
        aclk_accept_pulse <= 0;
      end else if (accept_edge_detect) begin
        aclk_accept_pulse <= 1;
      end
    end

    // Drive interafces
    always_comb begin
      //Input signals
      host_sync_if.clk              = clk;
      host_sync_if.reset_n          = reset_n;
      host_sync_if.in_config_valid  = clk_valid_pulse;
      host_sync_if.in_config_data   = clk_data1;

      //Output signals
      host_if.in_config_accept = aclk_accept_pulse;
    end

  end
  
endgenerate

endmodule // hpb_sync