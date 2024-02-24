#include <systemc>
#include <iostream>
#include <fstream>
#include <deque>
#include <string>
#include <math.h>
#include <queue>

#include <tlm>
#include <systemc>
#include <tlm_utils/simple_initiator_socket.h>
#include <tlm_utils/peq_with_cb_and_phase.h>
#include "MemoryManager.h"
// #include "AXI_Definition.h"

using namespace sc_core;
using namespace tlm;

SC_MODULE(AXI4_to_TLM)
{

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
  sc_in<axi_addr_t> aw_addr;
  sc_in<axi_addr_t> ar_addr;
  sc_out<sc_bv<DW>> r_data;
  sc_in<sc_bv<DW>> w_data;

  //queues structures
  struct ax_t
  {
    uint32_t id;
    axi_addr_t addr;
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
  std::list<ax_t>       ar_tlm_list;
  std::queue<ax_t>      aw_queue;
  std::queue<read_data_t>   r_queue;
  std::queue<write_data_t>  w_queue;
  std::queue<uint32_t>    b_tlm_queue;
  std::queue<uint32_t>    b_queue;
  int ax_queue_max_size;
  int num_complete_in_flight_write_data;
  long long base_addr;

  //tlm utilities
  tlm_utils::simple_initiator_socket<AXI4_to_TLM> iSocket;
    tlm_utils::peq_with_cb_and_phase<AXI4_to_TLM> payloadEventQueue;
    MemoryManager memoryManager;
    
    //Cycle contorl
    int nr_cycle_cnt;
    int wakeup_per_cycles;

    //Write to AXI trace file
    ofstream ar_file, r_file;

    void updateState()
    {
      int nr_read = 0 , nr_write = 0;
      int watch_dog_notice = 0;
      while(true){
        // std::cout << sc_time_stamp() <<": updateState ---------------------------->" << nr_cycle_cnt << std::endl;
        std::cout << sc_time_stamp() <<": updateState ----- Read 0x"<< nr_read << "----- Write 0x"<< nr_write << "---------------->\r";

        //Read phase
        if (ar_valid.read() && ar_ready.read())
        {
          // std::cout <<"AXI ar handshack-->" << nr_cycle_cnt << std::endl;
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
          if (addr.range(WordWidth-1,0).to_uint() != 0)
          {
            std::cout << sc_time_stamp() << "Unaligned read transfter at: 0x" << ar.addr << std::endl;
          }
          //size limitation
          // ar.addr = addr.range(20,0).to_uint();
          ar_queue.push(ar);
          nr_read ++;
        }

        if (ar_queue.size()<ax_queue_max_size)
        {
          ar_ready.write(true);
        } else {
          ar_ready.write(false);
        }

        if (!ar_queue.empty() && ar_tlm_list.size()<ax_queue_max_size)
        {
          sendReadPayload();
        }

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
          // std::cout <<"AXI r handshack-->"<< nr_cycle_cnt << std::endl;
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

      //Write phase 
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
          if (addr.range(WordWidth-1,0).to_uint() != 0)
          {
            std::cout << sc_time_stamp() << "Unaligned write transfter at: 0x" << aw.addr << std::endl;
          }
          //size limitation
          // aw.addr = addr.range(20,0).to_uint();
          aw_queue.push(aw);
          nr_write ++ ;
        }    

        if (aw_queue.size()<ax_queue_max_size)
        {
          aw_ready.write(true);
        } else {
          aw_ready.write(false);
        } 

        if (w_valid.read() && w_ready.read())
        {
          // std::cout <<"AXI w handshack" << std::endl;
          write_data_t wd;
          wd.data = w_data.read();
          // wd.strb = w_strb.read();
          wd.last = w_last.read();
          if (w_last.read())
          {
            ++num_complete_in_flight_write_data;
          }
          w_queue.push(wd);
        }

        w_ready.write(true);

        if (!aw_queue.empty() && ! w_queue.empty() && num_complete_in_flight_write_data>0 && b_tlm_queue.size()<ax_queue_max_size)
        {
          sendWritePayload();
        }

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

        nr_cycle_cnt -- ;
        if (nr_cycle_cnt <=0)
        {
          // watch dog
          if (0/*nr_read == 0 && nr_write == 0*/)
          {
            watch_dog_notice ++;
            if (watch_dog_notice >50)
            {
              std::cout << "error : the program is stalling !!!" << std::endl;
              break;
            }
          } else {
            watch_dog_notice = 0;
          }
          //reload
          nr_cycle_cnt = wakeup_per_cycles;
          //announce
          // std::cout << sc_time_stamp() << " has reads: 0x" << nr_read << " writes: 0x" << nr_write << std::endl; 
          //reset reads/writes
          // nr_read = 0;
          // nr_write = 0;
        }
        
        wait();
      }
      std::cout << "terminate by AXI4-TLM converter" << std::endl;
      sc_stop();
    }


    void sendReadPayload()
    {

      ax_t ar = ar_queue.front();
      uint32_t num_byte = ar.len*pow(2,ar.size) + ar.byte_offset;

      // std::cout << sc_time_stamp() <<": ------ send read payload -> addr:0x" << ar.addr + base_addr << " size:0x" << ar.size << " len:0x" << ar.len << std::endl;

    tlm_generic_payload& payload = memoryManager.allocate(num_byte);
    payload.acquire();
    payload.set_address(ar.addr); 
    payload.set_response_status(tlm::TLM_INCOMPLETE_RESPONSE);
    payload.set_dmi_allowed(false);
    payload.set_byte_enable_length(0);
    payload.set_data_length(num_byte);
    payload.set_command(tlm::TLM_READ_COMMAND);

    sendToTarget(payload,tlm::BEGIN_REQ,SC_ZERO_TIME);

    //update queues
    ar_tlm_list.push_back(ar);
    ar_queue.pop();
  }

  void sendWritePayload()
  {
    ax_t aw = aw_queue.front();
    uint32_t num_byte = aw.len*pow(2,aw.size) + aw.byte_offset;

    // std::cout << sc_time_stamp() <<": send write payload -> addr:0x" << aw.addr + base_addr << " size:0x" << aw.size << " len:0x" << aw.len << " byte offest:0x" << aw.byte_offset << std::endl;

    tlm_generic_payload& payload = memoryManager.allocate(num_byte);
    payload.acquire();
    payload.set_address(aw.addr); 
    payload.set_response_status(tlm::TLM_INCOMPLETE_RESPONSE);
    payload.set_dmi_allowed(false);
    payload.set_byte_enable_length(0);
    payload.set_data_length(num_byte);
    payload.set_command(tlm::TLM_WRITE_COMMAND);

    unsigned char * data_ptr = (unsigned char*)malloc(payload.get_data_length());
    

    for (uint32_t i = 0; i < aw.len; ++i)
    {
      write_data_t wd = w_queue.front();
      uint32_t lower_lane, upper_lane;
      getAXIByteLane(aw.addr,i,aw.size,lower_lane,upper_lane);
      for (uint32_t j = 0; j < DW/8; ++j)
      {
        if (j>= lower_lane && j<=upper_lane)
        {
          data_ptr[aw.byte_offset + i*((uint32_t)(pow(2,aw.size)))+j-lower_lane] = (unsigned char)(wd.data.range(8*(j+1)-1, j*8).to_uint());
        } 
      }
      w_queue.pop();
    }

    memcpy(payload.get_data_ptr(), data_ptr , payload.get_data_length());
    free(data_ptr);

    sendToTarget(payload,tlm::BEGIN_REQ,SC_ZERO_TIME);

    b_tlm_queue.push(aw.id);
    aw_queue.pop();
    num_complete_in_flight_write_data--;
  }

  void sendToTarget(tlm_generic_payload &payload, const tlm_phase &phase, const sc_time &delay)
  {
      tlm_phase TPhase = phase;
      sc_time TDelay = delay;
      iSocket->nb_transport_fw(payload, TPhase, TDelay);
  }

  tlm_sync_enum nb_transport_bw(tlm_generic_payload &payload, tlm_phase &phase, sc_time &bwDelay){
        payloadEventQueue.notify(payload, phase, bwDelay);
      return TLM_ACCEPTED;
    }

    void getAXIByteLane(axi_addr_t start_addr, uint32_t iter, uint32_t size, uint32_t &lower_lane, uint32_t & upper_lane)
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

  void peqCallback(tlm_generic_payload &payload,const tlm_phase &phase){
      if (phase == END_REQ)
      {
        // std::cout << sc_time_stamp() <<"recieve a END_REQ" << std::endl;
      }
      else if (phase == BEGIN_RESP)
      {
        if (payload.get_command() == tlm::TLM_READ_COMMAND)
        {
          // std::cout << sc_time_stamp() <<": GET read response" << std::endl;

          unsigned char * data_ptr = (unsigned char*)malloc(payload.get_data_length());
          memcpy(data_ptr, payload.get_data_ptr(), payload.get_data_length());

          //find the corresponding request
          ax_t ar;
          {
            std::list<ax_t>::iterator it;
            int find_out = 0;
            for (it = ar_tlm_list.begin(); it != ar_tlm_list.end(); ++it)
            {
              ar = *it;
              if (ar.addr == payload.get_address() && ar.len*DW_BYTE == payload.get_data_length())
              {
                find_out = 1;
                ar_tlm_list.erase(it);
                break;
              }
            }
            if (find_out == 0)
            {
              SC_REPORT_FATAL("AXI4_to_TLM", "How could? can not find corresponding request!");
            }
          }

          if (ar.addr != payload.get_address() || ar.len*DW_BYTE != payload.get_data_length())
          {
            std::cout << ar.addr << " : " << payload.get_address() << std::endl;
            std::cout << ar.len*DW_BYTE << " : " << payload.get_data_length() << std::endl;
            SC_REPORT_FATAL("AXI4_to_TLM", "What FxxK!!!!");
          }
          for (uint32_t i = 0; i < ar.len; ++i)
          {
            read_data_t rd;
            uint32_t lower_lane, upper_lane;
            getAXIByteLane(ar.addr,i,ar.size,lower_lane,upper_lane);
            for (uint32_t j = 0; j < DW/8; ++j)
            {
              if (j>= lower_lane && j<=upper_lane)
              {
                rd.data.range(8*(j+1)-1, j*8) = data_ptr[ar.byte_offset + i*((uint32_t)(pow(2,ar.size)))+j-lower_lane];
              } else {
                rd.data.range(8*(j+1)-1, j*8) = 0;
              }
            }
            rd.id = ar.id;
            rd.last = (i==ar.len-1);
            r_queue.push(rd);
          }

          free(data_ptr);

        } else if (payload.get_command() == tlm::TLM_WRITE_COMMAND){
          // std::cout << sc_time_stamp() <<": GET write response" << std::endl;
          uint32_t id = b_tlm_queue.front();
          b_queue.push(id);
          b_tlm_queue.pop();
        }
      
          payload.release();
          sendToTarget(payload, END_RESP, SC_ZERO_TIME);
      }
      else
      {
          SC_REPORT_FATAL("TrafficInitiator", "PEQ was triggered with unknown phase");
      }
    }

  SC_CTOR(AXI4_to_TLM) :
  iSocket("socket"), 
  ar_file("AXI_trace_ar.csv"),
  r_file("AXI_trace_r.csv"),
    payloadEventQueue(this, &AXI4_to_TLM::peqCallback),
    memoryManager(true),
    ax_queue_max_size(1000),
    num_complete_in_flight_write_data(0),
    base_addr(0x80000000),
    nr_cycle_cnt(2000),
    wakeup_per_cycles(2000)
  {
    SC_THREAD(updateState);
    sensitive << clk.pos();
    iSocket.register_nb_transport_bw(this, &AXI4_to_TLM::nb_transport_bw);
    ar_file << "id,addr,size,len,time\n";
    r_file << "id,resp,last,data_list\n";
  }

  ~AXI4_to_TLM(){
    ar_file.close();
    r_file.close();
  }
};
