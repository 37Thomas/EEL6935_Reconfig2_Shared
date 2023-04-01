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

   bit timeout;

   constraint c_go_dist { go dist{0 :/ 90, 1:/ 10 }; }
endclass

interface fib_bfm #(parameter int INPUT_WIDTH, parameter int OUTPUT_WIDTH) (input logic clk);
   logic             rst, go, done, overflow;
   logic [INPUT_WIDTH-1:0] n;
   logic signed [OUTPUT_WIDTH-1:0] result;

   task automatic wait_for_done();
      @(posedge clk iff (done == 1'b0));
      @(posedge clk iff (done == 1'b1));      
   endtask

   task automatic wait_for_done_timeout();
      fork //Waits for either done to be asserted or for 200us to pass before exiting to account for infinite loops
         wait_for_done();
         #200us;
      join_any     
   endtask
   
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
   task automatic start(input logic [INPUT_WIDTH-1:0] n_);    
      n <= n_;
      go <= 1'b1;      
      @(posedge clk);

      go <= 1'b0;    
   endtask // start
   
   event active_event;
   logic is_active;
 
   task automatic monitor();
      is_active = 1'b0;
            
      forever begin
         @(posedge clk);
         if (rst) is_active = 1'b0;
         else begin         
            if (done) is_active = 1'b0;     
            if (!is_active && go) begin                
               is_active = 1'b1;

               -> active_event;        
            end
         end
      end 
   endtask // monitor
endinterface

class scoreboard #(int NUM_TESTS, int INPUT_WIDTH, int OUTPUT_WIDTH);
   mailbox      scoreboard_result_mailbox;
   mailbox      scoreboard_data_mailbox;
   int          passed, failed;
   int          ovf_corr, ovf_imp, ovf_not, res_corr, res_inc, timeout;
   int unsigned reference;

   function new(mailbox _scoreboard_data_mailbox, mailbox _scoreboard_result_mailbox);
      scoreboard_data_mailbox = _scoreboard_data_mailbox;
      scoreboard_result_mailbox = _scoreboard_result_mailbox;

      passed = 0;
      failed = 0;
      ovf_corr = 0;
      ovf_imp = 0;
      ovf_not = 0;
      res_corr = 0;
      res_inc = 0;
      timeout = 0;
      
   endfunction // new
   
   function int model(int n);
      automatic int unsigned i = 3;
      automatic int unsigned x = 0;
      automatic int unsigned y = 1;
      automatic int unsigned temp;
      
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
         $display("Time %0t [Scoreboard]: Received start of test for n=%0d.", $time, in_item.n);

         // Then, wait until the monitor tells us that test is complete.
         scoreboard_result_mailbox.get(out_item);
         $display("Time %0t [Scoreboard]: Received result=%0d for n=%0d.", $time, out_item.result, in_item.n);

         // Get the correct result based on the input at the start of the test.
	 if(out_item.timeout) begin
	    $display("Time %0t [Scoreboard]: Test timed out for n=%0d.", $time, in_item.n);
	    failed ++;
	    timeout ++;
	 end
	 else begin
            reference = model(in_item.n);         
            if (reference <= (2**OUTPUT_WIDTH) - 1) begin // && out_item.result == reference && out_item.overflow == 1'b0) begin
	       if(out_item.overflow != 1'b0) begin
		  $display("Time %0t [Scoreboard] Test failed (result): overflow asserted for n=%0d.", $time, out_item.overflow);
		  failed ++;
		  ovf_imp ++;
	       end
	       else if(out_item.result != reference) begin
		  $display("Time %0t [Scoreboard] Test failed (result): result=%0d instead of %0d for n=%0d.", $time, out_item.result, reference, in_item.n);
		  failed ++;
		  res_inc ++;
	       end
	       else begin
		  $display("Time %0t [Scoreboard] Test passed (result) for n=%0d.", $time, in_item.n);
		  passed ++;
		  res_corr ++;
	       end
            end
            else begin // Output is larger than can fit, should assert overflow
	       if(out_item.overflow == 1'b1) begin
		  $display("Time %0t [Scoreboard] Test passed (overflow) for n=%0d", $time, in_item.n);
		  passed ++;
		  ovf_corr ++;
	       end
	       else begin
		  $display("Time %0t [Scoreboard] Test failed (overflow): overflow not asserted, result=%0d for n=%0d.", $time, out_item.result, in_item.n);
		  failed ++;
		  ovf_not ++;
	       end
            end // else: !if(reference <= (2**OUTPUT_WIDTH) - 1)
	 end
      end // for (int i=0; i < NUM_TESTS; i++)

      while(scoreboard_data_mailbox.try_get(in_item));
      while(scoreboard_result_mailbox.try_get(out_item));
   endtask

   function void report_status();     
      $display("Test status: %0d passed, %0d failed", passed, failed);
      $display("Correct result: %0d, Overflow properly asserted: %0d", res_corr, ovf_corr);
      $display("Overflow improperly asserted: %0d, Overflow not asserted: %0d, Incorrect result: %0d, Timeout: %0d", ovf_imp, ovf_not, res_inc, timeout);
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

      // Start the consecutive sequence at 0. 
      bit [INPUT_WIDTH-1:0] n = '0;     
      
      forever begin // Generate items until # of valid items (go = 1) reached
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
         //$display("Time %0t [start_monitor]: Sending start of test for n=%0d.", $time, item.n);
         scoreboard_data_mailbox.put(item);      
      end              
   endtask       
endclass

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

         bfm.wait_for_done_timeout();
         item.result = bfm.result;
         item.overflow = bfm.overflow;

         if(bfm.done != 1'b1) item.timeout = 1'b1;
         else item.timeout = 1'b0;

         $display("Time %0t [Monitor]: Monitor detected overflow=%0d, result=%0d.", $time, bfm.overflow, bfm.result);
         scoreboard_result_mailbox.put(item);
      end
   endtask       
endclass

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

            bfm.start(item.n);

            bfm.wait_for_done_timeout();     

            if(bfm.done != 1'b1) bfm.reset(1);

            //$display("Time %0t [Driver]: Detected done.", $time);           
            -> driver_done_event;           
         end
      end 
      else begin         
         forever begin                      
            driver_mailbox.get(item);
            //$display("Time %0t [Driver]: Driving data=h%h, go=%0b.", $time, item.n, item.go);

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

module fib_tb;

   localparam NUM_RANDOM_TESTS = 100;
   localparam NUM_CONSECUTIVE_TESTS = 66;
   localparam INPUT_WIDTH  = 6;
   localparam OUTPUT_WIDTH = 16;  
   localparam NUM_REPEATS = 1; // 0 = no repeats
   
   logic      clk;
   
   fib_bfm #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) _if (.clk(clk));
   fib #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) DUT (
      .clk(clk), .rst(_if.rst), .go(_if.go), .n(_if.n), .result(_if.result),
      .overflow(_if.overflow), .done(_if.done)
   );

   test #(.NAME("Random Test"), .NUM_TESTS(NUM_RANDOM_TESTS), .INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH), .REPEATS(NUM_REPEATS)) test0 = new(_if);
   test #(.NAME("Consecutive Test"), .NUM_TESTS(NUM_CONSECUTIVE_TESTS), .INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH), .CONSECUTIVE_INPUTS(1'b1), .ONE_TEST_AT_A_TIME(1'b1), .REPEATS(NUM_REPEATS)) test1 = new(_if);

   covergroup cg_clk @(posedge clk);
      go  : coverpoint (_if.go == 1'b1 && _if.done == 1'b1) {bins true = {1'b1}; option.at_least = 100;} // Go ahould be asserted >= 100 times when inactive
   endgroup // cg_clk

   covergroup cg_done @(posedge _if.done);
      ovf : coverpoint _if.overflow {bins one = {1'b1}; option.at_least = 10;} // Overflow should be asserted >= 10 times at the end of an execution (rising edge of done)
   endgroup // cg_done

   covergroup cg_act @(_if.active_event);
      all_n : coverpoint _if.n
         {option.at_least = 1; option.auto_bin_max = 2**OUTPUT_WIDTH;} // Every value of n when DUT is inactive and go is asserted (invalid inputs set to 0)
   endgroup // cg_act

   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;
   end

   cg_clk cg_clk_inst;
   cg_done cg_done_inst;
   cg_act cg_act_inst;
   
   initial begin     
      cg_clk_inst = new();
      cg_done_inst = new(); 
      cg_act_inst = new(); 
      $timeformat(-9, 0, " ns");
      test0.run();      
      test1.run();
      test0.report_status();
      test1.report_status();      
      disable generate_clock;      
   end
   
   // Done should be reset once cycle after go is enabled while inactive
   done_clear_after_go : assert property (@(posedge _if.clk) disable iff (_if.rst) _if.go && _if.done |=> !_if.done);

   // Done should only be reset if go was enabled on the previous cycle
   go_assert_before_done : assert property (@(posedge _if.clk) disable iff (_if.rst) $fell(_if.done) |-> $past(_if.go,1));

   // Result and overflow should retain their values upon completion (while done = 1 and has not changed, i.e. result/overflow may change at the assertion of done)
   res_stable_on_done : assert property (@(posedge _if.clk) ($stable(_if.done) && _if.done) |-> $stable(_if.result));
   ovf_stable_on_done : assert property (@(posedge _if.clk) ($stable(_if.done) && _if.done) |-> $stable(_if.overflow));
   

   // n should change while active several times, needs to be manually checked for 100 times
   n_change_active : cover property (@(posedge _if.clk) !$stable(_if.n) |-> _if.is_active);
     
endmodule // fib_tb
