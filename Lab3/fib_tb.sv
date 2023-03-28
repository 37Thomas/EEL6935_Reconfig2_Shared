// Greg Stitt
// University of Florida
//
// This file contains a collection of testbenches that graduate evolve a simple
// testbench into a more complex constrained-random verfication (CRV) testbench
// that would be used to test more complex modules.

`timescale 1 ns / 10 ps

class fib_item #(INPUT_WIDTH, WIDTH);
   rand bit [INPUT_WIDTH-1:0] n;
   rand bit go;   

   bit overflow;
   bit signed [OUTPUT_WIDTH-1:0] result;

   // A uniform distribution of go values probably isn't what we want, so
   // we'll make sure go is 0 90% of the time.
   constraint c_go_dist { go dist{0 :/ 90, 1:/ 10 }; }
endclass

interface fib_if #(parameter int INPUT_WIDTH, parameter int OUTPUT_WIDTH) (input logic clk);
    logic rst, go, done, overflow;
    logic [INPUT_WIDTH-1:0] n;
    logic [OUTPUT_WIDTH-1:0] result;
endinterface

class generator #(int INPUT_WIDTH, int OUTPUT_WIDTH);
   mailbox driver_mailbox;
   event   driver_done_event;

   function new(mailbox _driver_mailbox, event _driver_done_event);
      driver_mailbox = _driver_mailbox;
      driver_done_event = _driver_done_event;      
   endfunction // new
  
   task run();
      fib_item #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) item;

      forever begin
         item = new;     
         if (!item.randomize()) $display("Randomize failed");
         //$display("Time %0t [Generator]: Generating input h%h, go=%0b.", $time, item.data, item.go);

         driver_mailbox.put(item);
         @(driver_done_event);
      end
   endtask
endclass // generator


class driver #(int INPUT_WIDTH, int OUTPUT_WIDTH);
   virtual fib_if #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) vif;
   mailbox driver_mailbox;
   mailbox scoreboard_data_mailbox;
   event   driver_done_event;

   // New constructor to establish all connections.
   function new(virtual fib_if #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) _vif, mailbox _driver_mailbox, 
                mailbox _scoreboard_data_mailbox, event _driver_done_event);
      vif = _vif;      
      driver_mailbox = _driver_mailbox;
      scoreboard_data_mailbox = _scoreboard_data_mailbox;
      driver_done_event = _driver_done_event;      
   endfunction // new
   
   task run();
      // To know whether or not generated inputs will create a DUT output, 
      // we need to know whether or not the DUT is currently active.
      logic is_first_test = 1'b1;      
      logic is_active = 1'b0;
      $display("Time %0t [Driver]: Driver starting.", $time);
            
      forever begin
         fib_item #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) item;
         
         // If the circuit is reset at any point, reset the driver state.
         while (vif.rst) begin
            @(posedge vif.clk);   
            is_first_test = 1'b1;
            is_active = 1'b0;               
         end
         
         driver_mailbox.get(item);
         //$display("Time %0t [Driver]: Driving data=h%h, go=%0b.", $time, item.data, item.go);
         
         vif.data = item.data;
         vif.go = item.go;
         @(posedge vif.clk);
                 
         // If done is asserted, or if this is the first_test, 
         // then the DUT should be inactive and ready for another test.  
         if (vif.done || is_first_test)
           is_active = 1'b0;
                                 
         // If the DUT isn't already active, and we get a go signal, we are
         // starting a test, so inform the scoreboard. The scoreboard will
         // then wait to get the result from the monitor.        
         if (!is_active && vif.go) begin            
            $display("Time %0t [Driver]: Sending start of test for data=h%h.", $time, item.data);
            scoreboard_data_mailbox.put(item);
            is_active = 1'b1;       
            is_first_test = 1'b0;
         end

         -> driver_done_event;   
      end              
   endtask       
endclass // driver

class monitor #(int INPUT_WIDTH, int OUTPUT_WIDTH);
   virtual fib_if #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) vif;
   mailbox scoreboard_result_mailbox;

   function new(virtual fib_if #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) _vif, mailbox _scoreboard_result_mailbox);
      vif = _vif;
      scoreboard_result_mailbox = _scoreboard_result_mailbox;            
   endfunction // new
   
   task run();
      $display("Time %0t [Monitor]: Monitor starting.", $time);
      
      forever begin
         fib_item #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) item = new;
         @(posedge vif.clk iff (vif.done == 1'b0));      
         @(posedge vif.clk iff (vif.done == 1'b1));      
         item.result = vif.result;
         item.overflow = vif.overflow;
         $display("Time %0t [Monitor]: Monitor detected overflow = %0d, result=%0d.", $time, vif.overflow, vif.result);
         scoreboard_result_mailbox.put(item);
      end
   endtask       
endclass

class scoreboard #(int NUM_TESTS, int INPUT_WIDTH, int OUTPUT_WIDTH);
   mailbox scoreboard_result_mailbox;
   mailbox scoreboard_data_mailbox;
   int     passed, failed, reference;

   function new(mailbox _scoreboard_data_mailbox, mailbox _scoreboard_result_mailbox);
      scoreboard_data_mailbox = _scoreboard_data_mailbox;
      scoreboard_result_mailbox = _scoreboard_result_mailbox;

      passed = 0;
      failed = 0;
   endfunction // new
   
   function int model(int n);
      automatic int i = 3;
      automatic int x = 0;
      automatic int y = 1;
      automatic int temp;
      
      while (i <= n) begin
         temp = x + y;
         x = y;
         y = temp;
         i++;       
      end

      if (n < 2) return x;
      else return y;     
   endfunction

   task run();
      fib_item #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) in_item;  
      fib_item #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) out_item;  
      
      for (int i=0; i < NUM_TESTS; i++) begin     
         // First wait until the driver informs us of a new test.
         scoreboard_data_mailbox.get(in_item);
         $display("Time %0t [Scoreboard]: Received start of test for data=h%h.", $time, in_item.data);

         // Then, wait until the monitor tells us that test is complete.
         scoreboard_result_mailbox.get(out_item);
         $display("Time %0t [Scoreboard]: Received result=%0d for data=h%h.", $time, out_item.result, in_item.data);

         // Get the correct result based on the input at the start of the test.
         reference = model(in_item.data);         
         if (reference <= (2**OUTPUT_WIDTH) - 1 && out_item.result == reference && out_item.overflow == 1'b0) begin
            $display("Time %0t [Scoreboard] Test passed (result) for data=h%h", $time, in_item.data);
            passed ++;
         end
         else if(reference > (2**OUTPUT_WIDTH) - 1 && out_item.overflow == 1'b0)
            $display("Time %0t [Scoreboard] Test passed (overflow) for data=h%h", $time, in_item.data);
            passed ++;
         end
         else begin
            $display("Time %0t [Scoreboard] Test failed: result = %0d instead of %0d for data = h%h.", $time, out_item.result, reference, in_item.data);
            failed ++;      
         end
      end // for (int i=0; i < NUM_TESTS; i++)

      while(scoreboard_data_mailbox.try_get(in_item));
      while(scoreboard_result_mailbox.try_get(out_item));
   endtask

   function void report_status();     
      $display("Test status: %0d passed, %0d failed", passed, failed);
   endfunction   
   
endclass // scoreboard

class env #(int NUM_TESTS, int INPUT_WIDTH, int OUTPUT_WIDTH);

   generator #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) gen;
   driver  #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) drv;
   monitor #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) monitor;
   scoreboard #(.NUM_TESTS(NUM_TESTS), .INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH))scoreboard;
   
   mailbox scoreboard_data_mailbox;
   mailbox scoreboard_result_mailbox;
   mailbox driver_mailbox;

   event   driver_done_event;
   
   function new(virtual fib_if #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) vif);      
      scoreboard_data_mailbox = new;
      scoreboard_result_mailbox = new;
      driver_mailbox = new;
      
      gen = new(driver_mailbox, driver_done_event);
      drv = new(vif, driver_mailbox, scoreboard_data_mailbox, driver_done_event);
      monitor = new(vif, scoreboard_result_mailbox);
      scoreboard = new(scoreboard_data_mailbox, scoreboard_result_mailbox);
   endfunction // new

   virtual task run();      
      fork
         gen.run();
         drv.run();
         monitor.run();
         scoreboard.run();       
      join_any

      scoreboard.report_status();      
   endtask // run   
endclass

module fib_tb;

   localparam NUM_TESTS = 1000;
   localparam INPUT_WIDTH  = 6;
   localparam OUTPUT_WIDTH = 16;   
   
   logic clk;

   fib_tb_if #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) _if (.clk(clk));
   fib #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) DUT (
      .clk(clk), .rst(_if.rst), .go(_if.go), .n(_if.n), .result(_if.result),
      .overflow(_if.overflow), .done(_if.done);
   );

   // Pass the interface to the constructor so that the environment isn't
   // created in an invalid state that requires further initialization.
   env #(.NUM_TESTS(NUM_TESTS), .INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) _env = new(_if);

   covergroup cg @(posedge clk);
      ovf : coverpoint _if.overflow {bins one = {1}; option.at_least = 10;} // Overflow should be asserted >= 10 times
      go : coverpoint (_if.go == 1'b1 && _if.done == 1'b1) {bins true = {1}; option.at_least = 100;} // Go ahould be asserted >= 100 times when inactive
      data_change : coverpoint (!$stable(_if.n) && _if.done == 1'b1 && $past(_if.done, 1) == 1'b1)
         {bins true = {1'b1}; option.at_least 100;} // Data should change at least 100 times when the circuit is inactive - i have no idea of this is correct
   endgroup
   
   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;
   end
   
   cg cg_inst;
   initial begin     
      cg_inst = new(); 
      $timeformat(-9, 0, " ns");
      _if.rst <= 1'b1;
      _if.go <= 1'b0;      
      for (int i=0; i < 5; i++) @(posedge clk);
      @(negedge clk);     
      _if.rst <= 1'b0;
      @(posedge clk);     
      _env.run();

      $display("Coverage = %0.2f %%", cg_inst.get_inst_coverage());
      disable generate_clock;      
   end
      
   assert property (@(posedge clk) disable iff (_if.rst) _if.go && _if.done |=> !_if.done); // Done should deassert one cycle after go is asserted
   assert property (@(posedge clk) disable iff (_if.rst) $fell(_if.done) |-> $past(_if.go,1)); //  If done is deasserted, go should be asserted one cycle in the past

     
endmodule // fib_tb