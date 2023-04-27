// part1.cpp
//
// This SYCL program should create a parallel (vectorized) version of the following
// sequential code:
//
// for (int i=0; i < VECTOR_SIZE; i++)
//   z[i] = x[i] + y[i];
//
// TODO: The provided code has some errors and missing code. Some of these will cause
// compiler errors. Some will cause runtime errors. You need to fix them an ensure that
// the output tests pass (you will see SUCCESS!) in the terminal.

#include <iostream>
#include <vector>
#include <random>

#include <CL/sycl.hpp>

const int NUM_INPUTS = 100000;

class vector_add;

int main(int argc, char* argv[]) { 
  
  std::vector<int> x_h(NUM_INPUTS);
  std::vector<int> y_h(NUM_INPUTS);
  std::vector<int> z_h(NUM_INPUTS);
  std::vector<int> correct_out(NUM_INPUTS);

  // Use C++11 randomization for input
  std::random_device rd;
  std::mt19937 gen(rd());
  std::uniform_int_distribution<> dist(-100, 100);

  for (size_t i=0; i < NUM_INPUTS; i++) {
    x_h[i] = dist(gen);
    y_h[i] = dist(gen);
    z_h[i] = 0;

    // Calculate correct outputs for comparison.
    correct_out[i] = x_h[i] + y_h[i];
  }
  

  try {
    cl::sycl::queue queue(cl::sycl::default_selector_v);
    
    cl::sycl::buffer<int, 1> x_buf {x_h.data(), cl::sycl::range<1>(x_h.size()) };
    cl::sycl::buffer<int, 1> y_buf {y_h.data(), cl::sycl::range<1>(y_h.size()) };
    cl::sycl::buffer<int, 1> z_buf {z_h.data(), cl::sycl::range<1>(z_h.size()) };
    
    queue.submit([&](cl::sycl::handler& handler) {

	cl::sycl::accessor x_d(x_buf, handler, cl::sycl::read_only);
	cl::sycl::accessor y_d(y_buf, handler, cl::sycl::read_only); //change 1
	cl::sycl::accessor z_d(z_buf, handler, cl::sycl::write_only);

	handler.parallel_for<class vector_add>(cl::sycl::range<1> { NUM_INPUTS }, [=](cl::sycl::id<1> i) {
	    z_d[i] = x_d[i] + y_d[i]; // change 2
	  });

      });

    queue.wait();
  }
  // change 3
	catch (cl::sycl::exception& e) {
    std::cout << e.what() << std::endl;
    return 1;	
	}
    // Check for correctness.
    if (z_h == correct_out) {
      std::cout << "SUCCESS!" << std::endl;
    }
    else {
      std::cout << "ERROR: Execution failed." << std::endl;
    }    
  

  return 0;
}
