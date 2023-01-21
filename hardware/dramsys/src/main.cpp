/*
 * Copyright (c) 2015, Technische Universität Kaiserslautern
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * 3. Neither the name of the copyright holder nor the names of its
 *    contributors may be used to endorse or promote products derived from
 *    this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER
 * OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * Authors:
 *    Robert Gernhardt
 *    Matthias Jung
 *    Luiza Correa
 *    Lukas Steiner
 *    Derek Christ
 */

#include <iostream>
#include <memory>
#include <string>
#include <utility>
#include <vector>
#include <list>
#include <chrono>
#include <DRAMSysConfiguration.h>
#include <memory>
#include <systemc>

#include "simulation/DRAMSys.h"
#include "TraceSetup.h"
#include "TrafficInitiator.h"

#include "axi_sc_mem.h"
#include "Vmempool_dramsys_tb.h"
#include "elfloader.h"
#include "AXI4_to_TLM.h"

#ifdef RECORDING
#include "simulation/DRAMSysRecordable.h"
#endif

using namespace sc_core;

std::string pathOfFile(const std::string &file)
{
    return file.substr(0, file.find_last_of('/'));
}

int main(int argc, char **argv)
{
    return sc_main(argc, argv);
}

SC_MODULE(mempool_rst_dv)
{
  sc_out<bool> rst_n;
  sc_in<bool> clk;

  void run()
  {
    std::cout << "Start drive rst_n " << std::endl; 

    rst_n = false;

    for (int i = 0; i < 5; ++i)
    {
        wait();
    }

    rst_n = true;
    while(1) {wait();}

    sc_stop();
  }

  SC_CTOR(mempool_rst_dv)
  {
    SC_THREAD(run);
    sensitive << clk.pos();
  }

};

int sc_main(int argc, char **argv)
{
    sc_set_time_resolution(1, SC_PS);

    std::string resources;
    std::string simulationJson;
    // Run only with default config (ddr3-example.json):
    if (argc == 1)
    {
        // Get path of resources:
        resources = pathOfFile(argv[0])
                    + std::string("/../../../DRAMSys/DRAMSys/library/resources/");
        simulationJson = resources + "simulations/ddr3-example.json";
    }
    // Run with specific config but default resource folders:
    else if (argc == 2)
    {
        // Get path of resources:
        resources = pathOfFile(argv[0])
                    + std::string("/../../../DRAMSys/DRAMSys/library/resources/");
        simulationJson = argv[1];
    }
    // Run with spefific config and specific resource folder:
    else if (argc == 3)
    {
        simulationJson = argv[1];
        resources = argv[2];
    }

    std::vector<std::unique_ptr<TrafficInitiator>> players;

    DRAMSysConfiguration::Configuration configLib = DRAMSysConfiguration::from_path(simulationJson, resources);

    // Instantiate DRAMSys:
    std::unique_ptr<DRAMSys> dramSys;

#ifdef RECORDING
    if (configLib.simConfig.databaseRecording.value_or(false))
        dramSys = std::make_unique<DRAMSysRecordable>("DRAMSys", configLib);
    else
#endif
        dramSys = std::make_unique<DRAMSys>("DRAMSys", configLib);



    // if (!configLib.traceSetup.has_value())
    //     SC_REPORT_FATAL("sc_main", "No tracesetup section provided.");

    // // Instantiate STL Players:
    // TraceSetup setup(dramSys->getConfig(), configLib.traceSetup.value(), resources, players);

    // // Bind STL Players with DRAMSys:
    // for (auto& player : players)
    //         player->iSocket.bind(dramSys->tSocket);


    //Define clock signal 
    sc_clock clk{"clk", 1, SC_NS, 0.5};
    std::cout << "Define clock" << std::endl; 

    //Definition of signals
    sc_signal<bool> rst_ni;
    sc_signal<bool> eoc_valid;

    sc_signal<uint32_t> aw_id;
    sc_signal<uint32_t> aw_len;
    sc_signal<uint32_t> aw_size;
    sc_signal<bool> aw_user;
    sc_signal<bool> aw_valid;
    sc_signal<bool> aw_ready;
    sc_signal<uint32_t> ar_id;
    sc_signal<uint32_t> ar_len;
    sc_signal<uint32_t> ar_size;
    sc_signal<bool> ar_user;
    sc_signal<bool> ar_valid;
    sc_signal<bool> ar_ready;
    sc_signal<uint32_t> r_id;
    sc_signal<uint32_t> r_resp;
    sc_signal<bool> r_last;
    sc_signal<bool> r_user;
    sc_signal<bool> r_valid;
    sc_signal<bool> r_ready;
    sc_signal<bool> w_last;
    sc_signal<bool> w_user;
    sc_signal<bool> w_valid;
    sc_signal<bool> w_ready;
    sc_signal<uint32_t> b_id;
    sc_signal<uint32_t> b_resp;
    sc_signal<bool> b_user;
    sc_signal<bool> b_valid;
    sc_signal<bool> b_ready;
    sc_signal<uint32_t> aw_addr;
    sc_signal<uint32_t> ar_addr;
    sc_signal<sc_bv<DW>> r_data;
    sc_signal<sc_bv<DW>> w_data;

    std::unique_ptr<Vmempool_dramsys_tb> mempool;
    mempool = std::make_unique<Vmempool_dramsys_tb>("mempool");
    std::cout << "Instanciate a mempool" << std::endl;
    mempool->clk_i(clk);
    mempool->rst_ni(rst_ni);
    //AW
    mempool->aw_id(aw_id);
    mempool->aw_len(aw_len);
    mempool->aw_size(aw_size);
    mempool->aw_addr(aw_addr);
    mempool->aw_user(aw_user);
    mempool->aw_valid(aw_valid);
    mempool->aw_ready(aw_ready);
    //AR
    mempool->ar_id(ar_id);
    mempool->ar_len(ar_len);
    mempool->ar_size(ar_size);
    mempool->ar_addr(ar_addr);
    mempool->ar_user(ar_user);
    mempool->ar_valid(ar_valid);
    mempool->ar_ready(ar_ready);
    //R
    mempool->r_id(r_id);
    mempool->r_data(r_data);
    mempool->r_resp(r_resp);
    mempool->r_last(r_last); 
    mempool->r_user(r_user);
    mempool->r_valid(r_valid);
    mempool->r_ready(r_ready);
    //W
    mempool->w_data(w_data);
    mempool->w_last(w_last);
    mempool->w_user(w_user);
    mempool->w_valid(w_valid);
    mempool->w_ready(w_ready);
    //B
    mempool->b_id(b_id);
    mempool->b_resp(b_resp);
    mempool->b_user(b_user);
    mempool->b_valid(b_valid);
    mempool->b_ready(b_ready);
    //EoC
    mempool->eoc_valid(eoc_valid);
    std::cout << "Connect all ara system signals" << std::endl;

    //Reset driver
    mempool_rst_dv rst_dv("rst_dv");
    rst_dv.clk(clk);
    rst_dv.rst_n(rst_ni);
    std::cout << "Instanciate a reset driver" << std::endl;

    std::unique_ptr<AXI4_to_TLM> conv;
    conv = std::make_unique<AXI4_to_TLM>("AXI4_to_TLM");
    conv->iSocket.bind(dramSys->tSocket);
    // std::unique_ptr<axi_sc_mem> conv;
    // conv = std::make_unique<axi_sc_mem>("axi_sc_mem");

    conv->clk(clk);
    //AW
    conv->aw_id(aw_id);
    conv->aw_len(aw_len);
    conv->aw_size(aw_size);
    conv->aw_addr(aw_addr);
    conv->aw_user(aw_user);
    conv->aw_valid(aw_valid);
    conv->aw_ready(aw_ready);
    //AR
    conv->ar_id(ar_id);
    conv->ar_len(ar_len);
    conv->ar_size(ar_size);
    conv->ar_addr(ar_addr);
    conv->ar_user(ar_user);
    conv->ar_valid(ar_valid);
    conv->ar_ready(ar_ready);
    //R
    conv->r_id(r_id);
    conv->r_data(r_data);
    conv->r_resp(r_resp);
    conv->r_last(r_last);
    conv->r_user(r_user);
    conv->r_valid(r_valid);
    conv->r_ready(r_ready);
    //W
    conv->w_data(w_data);
    // conv->w_strb(w_strb);
    conv->w_last(w_last);
    conv->w_user(w_user);
    conv->w_valid(w_valid);
    conv->w_ready(w_ready);
    //B
    conv->b_id(b_id);
    conv->b_resp(b_resp);
    conv->b_user(b_user);
    conv->b_valid(b_valid);
    conv->b_ready(b_ready);

    //Memory pre-loading

    long long dram_base=0x80000000;
    Configuration config;
    config.loadMemSpec(configLib.memSpec);
    uint64_t dramChannelSize = config.memSpec->getSimMemSizeInBytes() / config.memSpec->numberOfChannels;
    std::cout << "Dram Size: " << dramChannelSize << std::endl;
    std::cout << "Dram Base Addr: 0x" << std::hex << dram_base << std::endl;
    unsigned char * dram_memory_ptr = dramSys->getDramBasePointer();

    // elfloader_read_elf("hello_world.elf", conv->mem_size_bytes, conv->base_addr, conv->mem);
    elfloader_read_elf("/scratch/msc22f8/dramsys_mempool/mempool/software/bin/hello_world", dramChannelSize, dram_base, dram_memory_ptr);

    std::cout << "Load program done" << std::endl; 

    // Store the starting of the simulation in wallclock time:
    auto start = std::chrono::high_resolution_clock::now();

    // Start SystemC Simulation:
    sc_set_stop_mode(SC_STOP_FINISH_DELTA);
    // for (int i = 0; i < 2000; ++i)  
    while (!Verilated::gotFinish())
    { 
        sc_start(1, SC_NS); 
        if (eoc_valid.read())
        {
            std::cout << "Mempool EOC Stop!!!!!!!!" << std::endl; 
            break;
        }
    }
    // while (!Verilated::gotFinish()) { sc_start(1, SC_NS); }

    if (!sc_end_of_simulation_invoked())
    {
        SC_REPORT_WARNING("sc_main", "Simulation stopped without explicit sc_stop()");
        sc_stop();
    }

    auto finish = std::chrono::high_resolution_clock::now();
    std::chrono::duration<double> elapsed = finish - start;
    std::cout << "Simulation took " + std::to_string(elapsed.count()) + " seconds." << std::endl;
    mempool.release();
    conv.release();
    return 0;
}
