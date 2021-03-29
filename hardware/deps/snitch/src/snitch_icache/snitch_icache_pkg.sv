// Copyright (c) 2017-2018 ETH Zurich, University of Bologna
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.
//
// Fabian Schuiki <fschuiki@iis.ee.ethz.ch>

package snitch_icache_pkg;

    typedef struct packed {
      logic l0_miss;
      logic l0_hit;
      logic l0_prefetch;
      logic l0_double_hit;
    } icache_events_t;

    typedef struct packed {
        // Parameters passed to the root module.
        int NR_FETCH_PORTS;
        int LINE_WIDTH;
        int LINE_COUNT;
        int SET_COUNT;
        int PENDING_COUNT;
        int L0_LINE_COUNT;
        int FETCH_AW;
        int FETCH_DW;
        int FILL_AW;
        int FILL_DW;
        bit L1_TAG_SCM;
        bit EARLY_LATCH;

        // Derived values.
        int FETCH_ALIGN;
        int FILL_ALIGN;
        int LINE_ALIGN;
        int COUNT_ALIGN;
        int SET_ALIGN;
        int TAG_WIDTH;
        int L0_TAG_WIDTH;
        int L0_EARLY_TAG_WIDTH;
        int ID_WIDTH_REQ;
        int ID_WIDTH_RESP;
        int PENDING_IW; // refill ID width
    } config_t;

endpackage
