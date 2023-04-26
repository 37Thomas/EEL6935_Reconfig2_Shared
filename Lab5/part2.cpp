// part2.cpp
// This SYCL program will create a parallel version of the following
// sequential code:
//
// for (int i=0; i < VECTOR_SIZE; i++) {
//   int temp = b * a[i] + c;
//   if (temp > 127)
//     d[i] = 127;
//   else if (temp < -128)
//     d[i] = -128
//   else
//     d[i] = temp;
// }
//
//
// You will do this using two separate kernels. The first kernel will
// perform:
//
// int temp = b * a[i] + c;
//
// and the second kernel will perform the rest:
//
//   if (temp > 127)
//     d[i] = 127;
//   else if (temp < -128)
//     d[i] = -128
//   else
//     d[i] = temp;
//
// To do this, the SYCL code converts the temp variable into an array/vector.
// so each iteration's temp value can be transferred betweeen kernels.
//
// The first kernel should run on a GPU and the second should run on a CPU.
//
// Fill in the missing parts of the code until the execution reports SUCCESS!
//
// IMPORTANT: Do not change any of the existing code to get yours to work.
//
// Thomas Le, Haritha Vipinakumar
// Spring 2023

#include <iostream>
#include <vector>
#include <random>

#include <CL/sycl.hpp>

const int VECTOR_SIZE = 10000;

// Names of the two kernels
class b_x_a_plus_c;
class clip;

int main(int argc, char* argv[]) {
  
  float b, c;
  std::vector<int> a_h(VECTOR_SIZE);
  std::vector<int> d_h(VECTOR_SIZE);
  std::vector<int> correct_out(VECTOR_SIZE);
  
  std::vector<int> temp(VECTOR_SIZE);  
  
  std::random_device rd;
  std::mt19937 gen(rd());
  std::uniform_real_distribution<> dist(-100, 100);
  std::uniform_real_distribution<> dist2(-4, 4);
  
  b = dist2(gen);
  c = dist2(gen);
  for (size_t i=0; i < VECTOR_SIZE; i++) {
    a_h[i] = dist(gen);
    d_h[i] = 0;

    float x = b * a_h[i] + c;
    correct_out[i] = x > 127 ? 127 : x < -128 ? -128 : x;
  }

  try {
    // Create the queue for each device.
    cl::sycl::queue queue_cpu(cl::sycl::cpu_selector_v);
    cl::sycl::queue queue_gpu(cl::sycl::gpu_selector_v);

    // Create the necessary buffers.
    cl::sycl::buffer<int, 1> a_buf {a_h.data(), cl::sycl::range<1>(a_h.size()) };
    cl::sycl::buffer<int, 1> temp_buf {temp.data(), cl::sycl::range<1>(temp.size()) };
    cl::sycl::buffer<int, 1> d_buf {d_h.data(), cl::sycl::range<1>(d_h.size()) };

    // Execute the first kernel.
    queue_gpu.submit([&](cl::sycl::handler& handler) {

	cl::sycl::accessor a_d(a_buf, handler, cl::sycl::read_only);
	cl::sycl::accessor temp(temp_buf, handler, cl::sycl::write_only);

	// parallel_for for the first kernel.
  handler.parallel_for<class b_x_a_plus_c>(cl::sycl::range<1> { a_h.size() }, [=](cl::sycl::id<1> i) {
	    temp[i] = b * a_d[i] + c;
  });
	
      });

    // Execute the second kernel.
    queue_cpu.submit([&](cl::sycl::handler& handler) {

	cl::sycl::accessor temp(temp_buf, handler, cl::sycl::read_only);
	cl::sycl::accessor d_d(d_buf, handler, cl::sycl::write_only);
	
	// parallel_for for the second kernel.
  handler.parallel_for<class clip>(cl::sycl::range<1> { d_d.size() }, [=](cl::sycl::id<1> i) {
	    d_d[i] = temp[i] > 127 ? 127 : temp[i] < -128 ? -128 : temp[i];
  });

      });

    queue_cpu.wait();
  }
  catch (cl::sycl::exception& e) {
    std::cout << e.what() << std::endl;
    return 1;
  }
  
  if (d_h != correct_out) {
    std::cout << "ERROR: Execution failed." << std::endl;
    return 1;
  }
  
std::cout << "SUCCESS!" << std::endl;    
  return 0;
}
