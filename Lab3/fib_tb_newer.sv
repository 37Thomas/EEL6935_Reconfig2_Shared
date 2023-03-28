// Greg Stitt
// University of Florida
//
// This file contains a collection of testbenches that graduate evolve a simple
// testbench into a more complex constrained-random verfication (CRV) testbench
// that would be used to test more complex modules.

`timescale 1 ns / 10 ps

class fib_item #(INPUT_WIDTH, OUTPUT_WIDTH);
   rand bit [INPUT_WIDTH-1:0] n;
   rand bit go;   

   bit overflow;
   bit signed [OUTPUT_WIDTH-1:0] result;

   // A uniform distribution of go values probably isn't what we want, so
   // we'll make sure go is 0 90% of the time.
   constraint c_go_dist { go dist{0 :/ 90, 1:/ 10 }; }
endclass

interface fib_bfm #(parameter int INPUT_WIDTH, parameter int OUTPUT_WIDTH) (input logic clk);
   logic             rst, go, done, overflow;
   logic [INPUT_WIDTH-1:0] data;
   logic signed [OUTPUT_WIDTH-1:0] result;

   // With this wait_for_done task, the method for waiting to completion is 
   // defined in one place, which makes it easy to change. The implementation 
   // details are also hidden from the rest of the testbench, which makes it
   // more readable and concise.
   //
   // IMPORTANT: If there is any chance of these tasks being called by multiple
   // threads during the same timestep, they need to be automatic.
   // Remove the automatic keyword to see what happens. In my tests, only
   // one thread would match these events, requiring all other threads to wait
   // until they happen again, which means a monitor could miss seeing done
   // if it was only asserted for one cycle.
   task automatic wait_for_done();
      @(posedge clk iff (done == 1'b0));
      @(posedge clk iff (done == 1'b1));      
   endtask
 
   // Similarly, we can create other commonly used functionality that can be
   // called from different points in our testbench. These tasks are very useful
   // because they provide a layer of abstraction where common functionality
   // has a single definition within the BFM.
   
   // Reset the design.
   task automatic reset(int cycles);
      rst <= 1'b1;
      go <= 1'b0;      
      for (int i=0; i < cycles; i++) @(posedge clk);
      @(negedge clk);
      rst <= 1'b0;
      @(posedge clk);      
   endtask

   // Start the DUT with the specified data by creating a 1-cycle pulse on go.
   task automatic start(input logic [INPUT_WIDTH-1:0] data_);    
      data <= data_;
      go <= 1'b1;      
      @(posedge clk);

      // IMPORTANT: This has to be a non-blocking assignment to give other 
      // threads a chance to see that go was 1 on this rising edge. A blocking
      // assignment can cause a race condition. Alternatively, you could wait 
      // for a small amount of time before setting go back to 0, but that 
      // should be avoided.
      go <= 1'b0;    
   endtask // start
   
   // Helper code to detect when the DUT starts executing. This task internally
   // tracks the active status of the DUT and sends an event every time it
   // becomes active. With this strategy, the implementation specific details
   // are limited to the BFM and are hidden from the testbench.
   event active_event;  
   logic is_active = 1'b0;    
   task automatic monitor();
      //logic is_active;
      is_active = 1'b0;
            
      forever begin
         @(posedge clk);
         if (rst) is_active = 1'b0;
         else begin         
            if (done) is_active = 1'b0;     
            if (!is_active && go) begin                
               is_active = 1'b1;
               // The event is needed because there will be times in the
               // simulation where go and done are asserted at the same time.
               // If the code simply used @(posedge is_active) to detect the
               // start of a test, it would miss these instances because 
               // there wouldn't be a rising edge on is_active. It would simply
               // remain active between two consecutive tests.
               -> active_event;        
            end
         end
      end      
   endtask // monitor
endinterface

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
         $display("Time %0t [Scoreboard]: Received start of test for data=h%h.", $time, in_item.n);

         // Then, wait until the monitor tells us that test is complete.
         scoreboard_result_mailbox.get(out_item);
         $display("Time %0t [Scoreboard]: Received result=%0d for data=h%h.", $time, out_item.result, in_item.n);

         // Get the correct result based on the input at the start of the test.
         reference = model(in_item.n);         
         if (reference <= (2**OUTPUT_WIDTH) - 1 && out_item.result == reference && out_item.overflow == 1'b0) begin
            $display("Time %0t [Scoreboard] Test passed (result) for data=h%h", $time, in_item.n);
            passed ++;
         end
         else if(reference > (2**OUTPUT_WIDTH) - 1 && out_item.overflow == 1'b0)
            $display("Time %0t [Scoreboard] Test passed (overflow) for data=h%h", $time, in_item.n);
            passed ++;
         end
         else begin
            $display("Time %0t [Scoreboard] Test failed: result = %0d instead of %0d for data = h%h.", $time, out_item.result, reference, in_item.n);
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

class generator #(int INPUT_WIDTH, int OUTPUT_WIDTH, bit CONSECUTIVE_INPUTS);
   mailbox driver_mailbox;
   event   driver_done_event;

   function new(mailbox _driver_mailbox, event _driver_done_event);
      driver_mailbox = _driver_mailbox;
      driver_done_event = _driver_done_event;      
   endfunction // new
  
   task run();
      fib_item #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) item;

      // Start the consecutive sequence at 0. This could also be modified with
      // another configuration parameter.
      bit [INPUT_WIDTH-1:0] n = '0;     
      
      forever begin
         item = new;     
         if (!CONSECUTIVE_INPUTS) begin
            if (!item.randomize()) $display("Randomize failed");
            //$display("Time %0t [Generator]: Generating input h%h, go=%0b.", $time, item.n, item.go); 
         end
         else begin
            item.n = n;
            n ++;        
         end
         driver_mailbox.put(item);
         @(driver_done_event);
      end     
   endtask
endclass // generator

// Here we create a new class start_monitor that replaces the responsibility
// of detecting when the DUT is started, which was previously handled by the
// driver.

class start_monitor #(int INPUT_WIDTH, int OUTPUT_WIDTH);
   virtual           fib_bfm #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) bfm;
   mailbox           scoreboard_data_mailbox;

   function new(virtual fib_bfm #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) bfm, 
                mailbox _scoreboard_data_mailbox);
      this.bfm = bfm;      
      scoreboard_data_mailbox = _scoreboard_data_mailbox;
   endfunction // new

   task run();
      fork
         // Start the BFM monitor to track the active status.
         bfm.monitor();
         detect_start();         
      join_any
   endtask
   
   task detect_start();    
      forever begin
         fib_item #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) item = new;

         // Wait until the DUT becomes active.
         @(bfm.active_event);    
         item.n = bfm.n;
         $display("Time %0t [start_monitor]: Sending start of test for data=h%h.", $time, item.n);
         scoreboard_data_mailbox.put(item);      
      end              
   endtask       
endclass

// The done_monitor class is similar to the previous version, but since there 
// are now multiple monitoring responsibilities, this class is solely 
// responsible for monitoring for done events.

class done_monitor #(int INPUT_WIDTH, int OUTPUT_WIDTH);
   virtual           fib_bfm #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) bfm;
   mailbox           scoreboard_result_mailbox;

   function new(virtual fib_bfm #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) bfm, 
                mailbox _scoreboard_result_mailbox);
      this.bfm = bfm;
      scoreboard_result_mailbox = _scoreboard_result_mailbox;            
   endfunction // new
   
   task run();
      $display("Time %0t [Monitor]: Monitor starting.", $time);
      
      forever begin
         fib_item #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) item = new;

         // Here we use the BFM method to make the monitor independent from the
         // wait implementation.
         bfm.wait_for_done();
         item.result = bfm.result;
         item.overflow = bfm.overflow;
         $display("Time %0t [Monitor]: Monitor detected result=%0d.", $time, bfm.result);
         scoreboard_result_mailbox.put(item);
      end
   endtask       
endclass

// The new driver class uses the new BFM, and also no longer monitors for the
// beginning of tests, which eliminates the need for the scoreboard mailbox.

class driver #(int INPUT_WIDTH, int OUTPUT_WIDTH, bit ONE_TEST_AT_A_TIME=1'b0);
   virtual           fib_bfm #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) bfm;
   mailbox           driver_mailbox;
   event             driver_done_event;

   function new(virtual fib_bfm #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) bfm, 
                mailbox _driver_mailbox, 
                event   _driver_done_event);
      this.bfm = bfm;      
      driver_mailbox = _driver_mailbox;
      driver_done_event = _driver_done_event;      
   endfunction // new
   
   task run();
      fib_item #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) item;
      $display("Time %0t [Driver]: Driver starting.", $time);

      if (ONE_TEST_AT_A_TIME) begin
         forever begin
            driver_mailbox.get(item);

            // With the new BFM, we can just call the start method instead of
            // driving the signals directly.
            bfm.start(item.n);

            // Similarly, now we call the BFM to Wait for DUT completion, which
            // makes the driver independent of the implementation details.
            bfm.wait_for_done();            
            $display("Time %0t [Driver]: Detected done.", $time);           
            -> driver_done_event;           
         end
      end 
      else begin         
         forever begin                      
            driver_mailbox.get(item);
            //$display("Time %0t [Driver]: Driving data=h%h, go=%0b.", $time, item.n, item.go);

            // Here we don't use the BFM start method simply because we don't
            // necessarily want to start the DUT. We just want to drive the
            // inputs
            bfm.n = item.n;
            bfm.go = item.go;
            @(posedge bfm.clk);
            -> driver_done_event;
         end
      end              
   endtask       
endclass

class env #(int NUM_TESTS, int INPUT_WIDTH, int OUTPUT_WIDTH, 
             bit CONSECUTIVE_INPUTS=1'b0,
             bit ONE_TEST_AT_A_TIME=1'b0 );

   // I tend to use an _h suffix for handles to avoid variables having the same
   // name as the class. Since I use done_monitor_h and start_monitor_h, I
   // made all the other use the same convention.
   //
   // I have no idea why the conventional style of SystemVerilog is to not
   // capitalize class names like in other OOP languages. For example,
   //    Done_Monitor #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) done_monitor
   // would solve this problem. I have also seen other people simply add a
   // number suffix, or sometimes a _ suffix or prefix.
   generator #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH), .CONSECUTIVE_INPUTS(CONSECUTIVE_INPUTS)) gen_h;
   driver  #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH), .ONE_TEST_AT_A_TIME(ONE_TEST_AT_A_TIME)) drv_h;
   done_monitor #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) done_monitor_h;
   start_monitor #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) start_monitor_h;
   scoreboard #(.NUM_TESTS(NUM_TESTS), .INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) scoreboard_h;

   mailbox scoreboard_data_mailbox;
   mailbox scoreboard_result_mailbox;
   mailbox driver_mailbox;

   event   driver_done_event;
   
   function new(virtual fib_bfm #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) bfm);      
      scoreboard_data_mailbox = new;
      scoreboard_result_mailbox = new;
      driver_mailbox = new;
      
      gen_h = new(driver_mailbox, driver_done_event);
      drv_h = new(bfm, driver_mailbox, driver_done_event);
      done_monitor_h = new(bfm, scoreboard_result_mailbox);
      start_monitor_h = new(bfm, scoreboard_data_mailbox);
      scoreboard_h = new(scoreboard_data_mailbox, scoreboard_result_mailbox);
   endfunction // new
     
   function void report_status();
      scoreboard_h.report_status();
   endfunction
   
   virtual task run();      
      fork
         gen_h.run();
         drv_h.run();
         done_monitor_h.run();
         start_monitor_h.run();
         scoreboard_h.run();     
      join_any

      disable fork;      
   endtask // run   
endclass // env


// The new test class uses the new environment, and replaces some code with a
// call to a BFM method.

class test #(string NAME="default_test_name", 
              int NUM_TESTS, 
              int INPUT_WIDTH, int OUTPUT_WIDTH, 
              bit CONSECUTIVE_INPUTS=1'b0,
              bit ONE_TEST_AT_A_TIME=1'b0, 
              int REPEATS=0);

   virtual        fib_bfm #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) bfm;
   env #(.NUM_TESTS(NUM_TESTS),
          .INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH),
          .CONSECUTIVE_INPUTS(CONSECUTIVE_INPUTS),
          .ONE_TEST_AT_A_TIME(ONE_TEST_AT_A_TIME)) env_h;

   function new(virtual fib_bfm #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) bfm);
      this.bfm = bfm;
      env_h = new(bfm);
   endfunction // new

   function void report_status();
      $display("Results for Test %0s", NAME);      
      env_h.report_status();
   endfunction
   
   task run();
      $display("Time %0t [Test]: Starting test %0s.", $time, NAME);
      
      // Repeat the tests the specified number of times.
      for (int i=0; i < REPEATS+1; i++) begin
         if (i > 0) $display("Time %0t [Test]: Repeating test %0s (pass %0d).", $time, NAME, i+1);
         
         // We update the test to use the BFM reset method.
         bfm.reset(5);
         env_h.run();
         @(posedge bfm.clk);     
      end
      $display("Time %0t [Test]: Test completed.", $time);      
   endtask   
endclass

// Module: fib_tb
// Description: This testbench uses the new BFM and test class.

module fib_tb;

   localparam NUM_TESTS = 1000;
   localparam INPUT_WIDTH  = 6;
   localparam OUTPUT_WIDTH = 16;  
   logic      clk;
   
   fib_tb_bfm #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) _if (.clk(clk));
   fib #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) DUT (
      .clk(clk), .rst(_if.rst), .go(_if.go), .n(_if.n), .result(_if.result),
      .overflow(_if.overflow), .done(_if.done);
   );

   test #(.NAME("Random Test"), .NUM_TESTS(NUM_RANDOM_TESTS), .INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH), .REPEATS(NUM_REPEATS)) test0 = new(bfm);
   test #(.NAME("Consecutive Test"), .NUM_TESTS(NUM_CONSECUTIVE_TESTS), .INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH), .CONSECUTIVE_INPUTS(1'b1), .ONE_TEST_AT_A_TIME(1'b1), .REPEATS(NUM_REPEATS)) test1 = new(bfm);

   covergroup cg @(posedge clk);
      ovf : coverpoint _if.overflow {bins one = {1}; option.at_least = 10;} // Overflow should be asserted >= 10 times
      go : coverpoint ($rise(_if.go) && _if.is_active == 1'b0) {bins true = {1}; option.at_least = 100;} // Go ahould be asserted >= 100 times when inactive
      data_change : coverpoint (!$stable(_if.n) && _if.is_active == 1'b1)
         {bins true = {1'b1}; option.at_least 100;} // Data should change at least 100 times when the circuit is active
      all_n : coverpoint _if.n iff(_if.is_active == 1'b0 && _if.go == 1'b1) {option.auto_bin_max = 2**OUTPUT_WIDTH} // Every value of n when DUT is inactive and go is asserted
   endgroup

   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;
   end

   cg cg_inst;
   initial begin     
      cg_inst = new();    
      $timeformat(-9, 0, " ns");
      test0.run();      
      test1.run();
      test0.report_status();
      test1.report_status();      
      disable generate_clock;      
   end
      
   assert property (@(posedge bfm.clk) disable iff (bfm.rst) bfm.go && bfm.done |=> !bfm.done);
   assert property (@(posedge bfm.clk) disable iff (bfm.rst) $fell(bfm.done) |-> $past(bfm.go,1));
     
endmodule // fib_tb