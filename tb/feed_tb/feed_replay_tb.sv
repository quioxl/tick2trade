`timescale 1ns/1ns

module feed_replay_tb ();

  bit clk;
  bit reset_n;
  bit valid;
  bit startofpacket;
  bit endofpacket;
  bit [63:0] data;
  bit [2:0] empty;

  initial begin
    clk = 1'b0;
    forever #5ns clk = ~clk;
  end

  feed_decoder DUT (.clk(clk),
                    .reset_n(reset_n),
                    .in_ready(),
                    .in_valid(valid),
                    .in_startofpacket(startofpacket),
                    .in_endofpacket(endofpacket),
                    .in_data(data),
                    .in_empty(empty),
                    .in_error(1'b0),
                    .out_ready(1'b1),
                    .out_valid(),
                    .out_startofpacket(),
                    .out_endofpacket(),
                    .out_data(),
                    .out_empty(),
                    .out_error());

  int fd;
  int count;
  int code;

  initial begin
    $dumpfile("feed.vcd");
    $dumpvars(0);
    fd = $fopen("feed_record.txt","r");
    if (fd==0) $fatal("Unable to open feed_record.txt");
    do begin
      @(clk);
      code = $fscanf(fd,"%d:%b %b %b %b %b %b",count,reset_n,valid,startofpacket,endofpacket,data,empty);
    end while (code == 7);
    $fclose(fd);
    $finish();
  end

endmodule