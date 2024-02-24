// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

#include <systemc>
#include <iostream>
#include <fstream>
#include <deque>
#include <string>
#include <math.h>
#include <queue>

#include <sys/mman.h>


#define WordWidth 6
#define DW 512
#define DW_BYTE 64
#define DW_ALIGN 6
#define AW 32
#define axi_addr_t uint32_t

using namespace sc_core;
using namespace sc_dt;

SC_MODULE(axi_sc_mem){

  //Signals
  sc_in<bool> clk;
  sc_in<uint32_t> aw_id;
  sc_in<uint32_t> aw_len;
  sc_in<uint32_t> aw_size;
  sc_in<bool> aw_user;
  sc_in<bool> aw_valid;
  sc_out<bool> aw_ready;
  sc_in<uint32_t> ar_id;
  sc_in<uint32_t> ar_len;
  sc_in<uint32_t> ar_size;
  sc_in<bool> ar_user;
  sc_in<bool> ar_valid;
  sc_out<bool> ar_ready;
  sc_out<uint32_t> r_id;
  sc_out<uint32_t> r_resp;
  sc_out<bool> r_last;
  sc_out<bool> r_user;
  sc_out<bool> r_valid;
  sc_in<bool> r_ready;
  sc_in<bool> w_last;
  sc_in<bool> w_user;
  sc_in<bool> w_valid;
  sc_out<bool> w_ready;
  sc_out<uint32_t> b_id;
  sc_out<uint32_t> b_resp;
  sc_out<bool> b_user;
  sc_out<bool> b_valid;
  sc_in<bool> b_ready;
  sc_in<uint32_t> aw_addr;
  sc_in<uint32_t> ar_addr;
  sc_out<sc_bv<DW>> r_data;
  sc_in<sc_bv<DW>> w_data;

  //memory for simluation
  unsigned char *mem;

  //trace file 
  std::ofstream ar_file, r_file;

  //queues structures
  struct ax_t
  {
    uint32_t id;
    uint32_t addr;
    uint32_t size;
    uint32_t len;
    uint32_t byte_offset;
  };

  struct read_data_t
  {
    uint32_t id;
    sc_bv<DW> data;
    bool last;
  };

  struct write_data_t
  {
    sc_bv<DW> data;
    bool last;
  };

  //queues
  std::queue<ax_t>      ar_queue;
  std::queue<ax_t>      aw_queue;
  std::queue<read_data_t>   r_queue;
  std::queue<write_data_t>  w_queue;
  std::queue<uint32_t>    b_queue;
  int ax_queue_max_size;
  int num_complete_in_flight_write_data;

  //base address
  uint64_t base_addr;

  //memory size
  uint64_t mem_size_bytes;

  void preloadBytes(uint64_t addr, unsigned char data)
  {
  	if (addr < base_addr)
  	{
  		std::cout << "Error preloadByte at: " << addr << std::endl;
  		SC_REPORT_FATAL("axi_sc_mem.preloadBytes", "The addr is less than base_addr");
  	}
  	else if (addr - base_addr > mem_size_bytes)
  	{
  		std::cout << "Error preloadByte at: " << addr << std::endl;
  		SC_REPORT_FATAL("axi_sc_mem.preloadBytes", "The addr is larger than memory size");
  	}
  	mem[addr - base_addr] = data;
	}

	void getAXIByteLane(uint32_t start_addr, uint32_t iter, uint32_t size, uint32_t &lower_lane, uint32_t & upper_lane)
  {
    if (size>=DW_ALIGN)
    {
      lower_lane = 0;
      upper_lane = DW/8-1;
    } else {
      sc_bv<AW> current_addr = start_addr + iter*((uint32_t)(pow(2,size)));
      lower_lane = current_addr.range(DW_ALIGN-1, 0).to_uint();
      upper_lane = lower_lane + pow(2,size) -1;
    }
  }

	void updateState()
  {
    int nr_read = 0 , nr_write = 0;
    while(true){
      std::cout << sc_time_stamp() <<": updateState ----- Read 0x"<< nr_read << "----- Write 0x"<< nr_write << "---------------->\r";

    	//////////
      //  AR  //
      //////////

      if (ar_valid.read() && ar_ready.read())
      {
        // std::cout << sc_time_stamp() <<"AXI ar handshack-->" \
        //         << ar_id.read() << "," \
        //         << ar_addr.read() << "," \
        //         << ar_size.read() << "," \
        //         << ar_len.read() \
        //         << std::endl;
        ar_file << ar_id.read() << "," \
                << ar_addr.read() << "," \
                << ar_size.read() << "," \
                << ar_len.read() << "," << sc_time_stamp() << "\n";
        ax_t ar;
        ar.id = ar_id.read();
        ar.addr = ar_addr.read() - base_addr;
        ar.size = ar_size.read();
        ar.len = ar_len.read()+1;
        sc_bv<AW> addr = ar.addr;
        ar.byte_offset = addr.range(WordWidth-1,0).to_uint();
        //valid address
        if (ar.byte_offset != 0)
        {
          std::cout << sc_time_stamp() << "Unaligned read transfter at: 0x" << ar.addr << std::endl;
        }
        //size limitation
        if (ar.addr > mem_size_bytes)
        {
        	std::cout << "Error axi read at: " << ar.addr << std::endl;
        	SC_REPORT_FATAL("axi_sc_mem.ar", "The addr is larger than memory size");
        }
        ar_queue.push(ar);
        nr_read++;
      }

      if (ar_queue.size()<ax_queue_max_size)
      {
        ar_ready.write(true);
      } else {
        ar_ready.write(false);
      }

      //////////////
      //  AR -> R //
      //////////////

      if (!ar_queue.empty() && r_queue.size()<ax_queue_max_size)
      {
      	//fetch ar
      	ax_t ar = ar_queue.front();

      	//get data
        for (int i = 0; i < ar.len; ++i)
        {
        	read_data_t rd;
          uint32_t lower_lane, upper_lane;
        	getAXIByteLane(ar.addr,i,ar.size,lower_lane,upper_lane);
        	for (uint32_t j = 0; j < DW/8; ++j)
          {
            if (j>= lower_lane && j<=upper_lane)
            {
              rd.data.range(8*(j+1)-1, j*8) = mem[ar.addr + ar.byte_offset + i*((uint32_t)(pow(2,ar.size)))+j-lower_lane];
            } else {
              rd.data.range(8*(j+1)-1, j*8) = 0;
            }
          }
          rd.id = ar.id;
          rd.last = (i==ar.len-1);
          r_queue.push(rd);
        }

        //pop ar
        ar_queue.pop();
      }

      /////////
      //  R  //
      /////////

      if (r_valid.read() && r_ready.read())
      {
        r_file  << r_id.read() << "," \
                << r_resp.read() << "," \
                << r_last.read() << "," \
                << r_data.read().range(64-1,0).to_uint() << "," \
                << r_data.read().range(128-1,64).to_uint() << "," \
                << r_data.read().range(192-1,128).to_uint() << "," \
                << r_data.read().range(256-1,192).to_uint() << "," \
                << r_data.read().range(320-1,256).to_uint() << "," \
                << r_data.read().range(384-1,320).to_uint() << "," \
                << r_data.read().range(448-1,384).to_uint() << "," \
                << r_data.read().range(512-1,448).to_uint() << "\n";
        // std::cout <<"AXI r handshack-->" \
        //         << r_id.read() << "," \
        //         << r_resp.read() << "," \
        //         << r_last.read() << "," \
        //         << r_data.read().range(64-1,0).to_uint() << "," \
        //         << r_data.read().range(128-1,64).to_uint() << "," \
        //         << r_data.read().range(192-1,128).to_uint() << "," \
        //         << r_data.read().range(256-1,192).to_uint() << "," \
        //         << r_data.read().range(320-1,256).to_uint() << "," \
        //         << r_data.read().range(384-1,320).to_uint() << "," \
        //         << r_data.read().range(448-1,384).to_uint() << "," \
        //         << r_data.read().range(512-1,448).to_uint() \
        //         << std::endl;
        r_queue.pop();
      }

      if (!r_queue.empty())
      {
        read_data_t rd = r_queue.front();
        r_id.write(rd.id);
        r_data.write(rd.data);
        r_resp.write(0);
        r_last.write(rd.last);
        r_user.write(0);
        r_valid.write(true);
      } else {
        r_valid.write(false);
      }

    	//////////
      //  AW  //
      //////////

    	if (aw_valid.read() && aw_ready.read())
      {
        // std::cout <<"AXI aw handshack" << std::endl;
        ax_t aw;
        aw.id = aw_id.read();
        aw.addr = aw_addr.read() - base_addr;
        aw.size = aw_size.read();
        aw.len = aw_len.read()+1;
        sc_bv<AW> addr = aw.addr;
        aw.byte_offset = addr.range(WordWidth-1,0).to_uint();
        if (aw.byte_offset != 0)
        {
          std::cout << sc_time_stamp() << "Unaligned write transfter at: 0x" << aw.addr << std::endl;
        }
        //size limitation
        if (aw.addr > mem_size_bytes)
        {
        	std::cout << "Error axi write at: " << aw.addr << std::endl;
        	SC_REPORT_FATAL("axi_sc_mem.aw", "The addr is larger than memory size");
        }
        aw_queue.push(aw);
        nr_write++;
      }    

      if (aw_queue.size()<ax_queue_max_size)
      {
        aw_ready.write(true);
      } else {
        aw_ready.write(false);
      } 

      /////////
      //  W  //
      /////////

      if (w_valid.read() && w_ready.read())
      {
        // std::cout <<"AXI w handshack" << std::endl;
        write_data_t wd;
        wd.data = w_data.read();
        wd.last = w_last.read();
        if (w_last.read())
        {
          ++num_complete_in_flight_write_data;
        }
        w_queue.push(wd);
      }

      w_ready.write(true);

      ///////////////////
      //  AW + W -> B  //
      ///////////////////

      if (!aw_queue.empty() && ! w_queue.empty() && num_complete_in_flight_write_data>0 && b_queue.size()<ax_queue_max_size)
      {
        ax_t aw = aw_queue.front();

        for (uint32_t i = 0; i < aw.len; ++i)
				{
				  write_data_t wd = w_queue.front();
				  uint32_t lower_lane, upper_lane;
				  getAXIByteLane(aw.addr,i,aw.size,lower_lane,upper_lane);
				  for (uint32_t j = 0; j < DW/8; ++j)
				  {
				    if (j>= lower_lane && j<=upper_lane)
				    {
				      mem[aw.addr + aw.byte_offset + i*((uint32_t)(pow(2,aw.size)))+j-lower_lane] = (unsigned char)(wd.data.range(8*(j+1)-1, j*8).to_uint());
				    } 
				  }
				  w_queue.pop();
				}

				b_queue.push(aw.id);

				num_complete_in_flight_write_data--;

				aw_queue.pop();
      }

      /////////
      //  B  //
      /////////

      if (b_valid.read() && b_ready.read())
      {
        // std::cout <<"AXI b handshack" << std::endl;
        b_queue.pop();
      }

      if (!b_queue.empty())
      {
        uint32_t id = b_queue.front();
        b_id.write(id);
        b_resp.write(0);
        b_user.write(0);
        b_valid.write(true);
      } else {
        b_valid.write(false);
      }

      //////////////////////////////////////
      //  Trigger at Every Clock Posedge  //
      //////////////////////////////////////
      
      wait();
    }
    std::cout << "terminate by AXI4-TLM converter" << std::endl;
    sc_stop();
  }




  SC_CTOR(axi_sc_mem) :
  num_complete_in_flight_write_data(0),
	ax_queue_max_size(10),
	base_addr(0x80000000),
	mem_size_bytes(117440512)
  {
    SC_THREAD(updateState);
    sensitive << clk.pos();
    ar_file.open("AXI_trace_ar.csv");
    r_file.open("AXI_trace_r.csv");
    ar_file << "id,addr,size,len,time\n";
    r_file << "id,resp,last,data_list\n";
    mem = (unsigned char *)mmap(nullptr, mem_size_bytes, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON | MAP_NORESERVE, -1, 0);
  }

  ~axi_sc_mem(){
    ar_file.close();
    r_file.close();
    free(mem);
  }

};