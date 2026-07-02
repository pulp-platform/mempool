#ifndef _FLEX_RUNTIME_H_
#define _FLEX_RUNTIME_H_
#include <stdint.h>
#include "flex_cluster_arch.h"
#include "flex_alloc.h"

#ifdef MEMPOOL_CLUSTER_UNIT
// Prevent mempool's alloc.h from being included (same types, conflicting defs)
#define _ALLOC_H_
#include "encoding.h"
// Mempool compatibility wrappers
// (must be declared before runtime.h, which calls them inside mempool_init())
static inline void alloc_init(alloc_t *alloc, void *base, const uint32_t size) {
  flex_cluster_alloc_init(alloc, base, size);
}
static inline alloc_t *get_alloc_l1() { return flex_get_allocator_l1(); }
alloc_t *get_alloc_tile(const uint32_t tile_id);
static inline void *simple_malloc(const uint32_t size) { return flex_l1_malloc(size); }
static inline void simple_free(void *const ptr) { flex_l1_free(ptr); }
static inline void alloc_dump(alloc_t *alloc) { flex_dump_heap(); }
#include "runtime.h"
#include "synchronization.h"
#endif

#define ARCH_NUM_CLUSTER            (ARCH_NUM_CLUSTER_X*ARCH_NUM_CLUSTER_Y)
#define ARCH_SYNC_SIZE              (ARCH_SYNC_INTERLEAVE + ARCH_SYNC_SPECIAL_MEM)
#define cluster_index(x,y)          ((y)*ARCH_NUM_CLUSTER_X+(x))
#define local(offset)               (ARCH_CLUSTER_TCDM_BASE+offset)
#define zomem(offset)               (ARCH_CLUSTER_ZOMEM_BASE+offset)
#define remote_cid(cid,offset)      (ARCH_CLUSTER_TCDM_REMOTE+cid*ARCH_CLUSTER_TCDM_SIZE+offset)
#define remote_xy(x,y,offset)       (ARCH_CLUSTER_TCDM_REMOTE+cluster_index(x,y)*ARCH_CLUSTER_TCDM_SIZE+offset)
#define remote_pos(pos,offset)      (ARCH_CLUSTER_TCDM_REMOTE+cluster_index(pos.x,pos.y)*ARCH_CLUSTER_TCDM_SIZE+offset)
#define hbm_addr(offset)            ((uint64_t)ARCH_HBM_START_BASE+(uint64_t)offset)
#define hbm_west(nid,offset)        ((uint64_t)ARCH_HBM_START_BASE+((uint64_t)nid)*(uint64_t)ARCH_HBM_NODE_ADDR_SPACE+(uint64_t)offset)
#define hbm_north(nid,offset)       ((uint64_t)ARCH_HBM_START_BASE+((uint64_t)nid)*(uint64_t)ARCH_HBM_NODE_ADDR_SPACE+(uint64_t)ARCH_HBM_NODE_ADDR_SPACE*(uint64_t)ARCH_NUM_CLUSTER_Y+(uint64_t)offset)
#define hbm_east(nid,offset)        ((uint64_t)ARCH_HBM_START_BASE+((uint64_t)nid)*(uint64_t)ARCH_HBM_NODE_ADDR_SPACE+(uint64_t)ARCH_HBM_NODE_ADDR_SPACE*((uint64_t)ARCH_NUM_CLUSTER_Y+(uint64_t)ARCH_NUM_CLUSTER_X)+(uint64_t)offset)
#define hbm_south(nid,offset)       ((uint64_t)ARCH_HBM_START_BASE+((uint64_t)nid)*(uint64_t)ARCH_HBM_NODE_ADDR_SPACE+(uint64_t)ARCH_HBM_NODE_ADDR_SPACE*2*(uint64_t)ARCH_NUM_CLUSTER_Y+(uint64_t)ARCH_HBM_NODE_ADDR_SPACE*ARCH_NUM_CLUSTER_X+(uint64_t)offset)
#define is_hbm_region(addr)         (addr >= ARCH_HBM_START_BASE)
#define is_power_of_two(value)      (((value) & ((value) - 1)) == 0)

/*******************
* Cluster Position *
*******************/

typedef struct FlexPosition
{
    uint32_t x;
    uint32_t y;
}FlexPosition;

FlexPosition get_pos(uint32_t cluster_id) {
    FlexPosition pos;
    pos.x = cluster_id % ARCH_NUM_CLUSTER_X;
    pos.y = cluster_id / ARCH_NUM_CLUSTER_X;
    return pos;
}

//Methods
FlexPosition right_pos(FlexPosition pos) {
    uint32_t new_x = (pos.x + 1) % ARCH_NUM_CLUSTER_X;
    uint32_t new_y = pos.y;
    FlexPosition new_pos;
    new_pos.x = new_x;
    new_pos.y = new_y;
    return new_pos;
}

FlexPosition left_pos(FlexPosition pos) {
    uint32_t new_x = (pos.x + ARCH_NUM_CLUSTER_X - 1) % ARCH_NUM_CLUSTER_X;
    uint32_t new_y = pos.y;
    FlexPosition new_pos;
    new_pos.x = new_x;
    new_pos.y = new_y;
    return new_pos;
}

FlexPosition top_pos(FlexPosition pos) {
    uint32_t new_x = pos.x;
    uint32_t new_y = (pos.y + 1) % ARCH_NUM_CLUSTER_Y;
    FlexPosition new_pos;
    new_pos.x = new_x;
    new_pos.y = new_y;
    return new_pos;
}

FlexPosition bottom_pos(FlexPosition pos) {
    uint32_t new_x = pos.x;
    uint32_t new_y = (pos.y + ARCH_NUM_CLUSTER_Y - 1) % ARCH_NUM_CLUSTER_Y;
    FlexPosition new_pos;
    new_pos.x = new_x;
    new_pos.y = new_y;
    return new_pos;
}

uint32_t flex_get_cluster_id(){
    volatile uint32_t * cluster_reg      = (volatile uint32_t *) ARCH_CLUSTER_REG_BASE;
    return *cluster_reg;
}

/*******************
*  Core Position   *
*******************/

uint32_t flex_get_core_id(){
    uint32_t hartid;
    asm volatile("csrr %0, mhartid" : "=r"(hartid));
    return hartid;
}

uint32_t flex_is_dm_core(){
    uint32_t hartid;
    asm volatile("csrr %0, mhartid" : "=r"(hartid));
    return (hartid == ARCH_NUM_CORE_PER_CLUSTER-1);
}

uint32_t flex_is_first_core(){
    uint32_t hartid;
    asm volatile("csrr %0, mhartid" : "=r"(hartid));
    return (hartid == 0);
}

/********************
*  Data Allocation  *
********************/

// Back-adaptation for other config fills to pass CI
#ifndef ARCH_CLUSTER_HEAP_BASE
#define ARCH_CLUSTER_HEAP_BASE (0x00000000)
#define ARCH_CLUSTER_HEAP_END  (0x00000000)
#endif

/*
 * Desc: cluster-private heap allocator initialization
 */

extern char __l1_heap_start[];
extern char __hbm_heap_start[];

static inline void flex_alloc_init(){
    uint32_t CID = flex_get_cluster_id();
    // volatile uint32_t * heap_start      = (volatile uint32_t *) (ARCH_CLUSTER_HEAP_BASE + 0x1000);
    volatile uint32_t * heap_start      = (volatile uint32_t *) __l1_heap_start;
    volatile uint32_t * heap_end        = (volatile uint32_t *) ARCH_CLUSTER_HEAP_END;
    volatile uint32_t   heap_size       = (uint32_t)heap_end - (uint32_t)heap_start;
    if (flex_is_first_core()){
        flex_cluster_alloc_init(flex_get_allocator_l1(), (void *)heap_start, heap_size);
    }

    // HBM allocator
    uint32_t hbm_nodes = 4; // bowwang: hardcoded for now
    volatile uint32_t * hbm_heap_start      = (volatile uint32_t *) __hbm_heap_start;
    volatile uint32_t * hbm_heap_end        = (volatile uint32_t *) (ARCH_HBM_START_BASE + (ARCH_HBM_NODE_ADDR_SPACE * hbm_nodes));
    volatile uint32_t   hbm_heap_size       = (uint32_t)hbm_heap_end - (uint32_t)hbm_heap_start;
    if (flex_is_first_core()){
        flex_cluster_alloc_init(flex_get_allocator_hbm(), (void *)hbm_heap_start, hbm_heap_size);
    }

    // allocation init summary
    if (CID==0 && flex_is_first_core()){
        printf("[Alloc] >>> L1  allocator:    0x%p\n", &alloc_l1);
        printf("[Alloc] >>> L1  first block:  0x%p\n", (&alloc_l1)->first_block);
        printf("[Alloc] >>> L1  heap start:   0x%p, size: 0x%x\n\n", heap_start, heap_size);
        printf("[Alloc] >>> HBM allocator:    0x%p\n", &alloc_hbm);
        printf("[Alloc] >>> HBM first block:  0x%p\n", (&alloc_hbm)->first_block);
        printf("[Alloc] >>> HBM heap start:   0x%p, size: 0x%x\n\n", hbm_heap_start, hbm_heap_size);
    }

    return;
}


/*******************
*  Global Barrier  *
*******************/

uint32_t flex_get_enable_value(){
    volatile uint32_t * amo_reg      = (volatile uint32_t *) (ARCH_CLUSTER_REG_BASE+4);
    return *amo_reg;
}

uint32_t flex_get_disable_value(){
    volatile uint32_t * amo_reg      = (volatile uint32_t *) (ARCH_CLUSTER_REG_BASE+24);
    return *amo_reg;
}

uint32_t flex_get_barrier_num_cluster(){
    volatile uint32_t * info_reg      = (volatile uint32_t *) (ARCH_CLUSTER_REG_BASE+8);
    return *info_reg;
}

uint32_t flex_get_barrier_num_cluster_x(){
    volatile uint32_t * info_reg      = (volatile uint32_t *) (ARCH_CLUSTER_REG_BASE+12);
    return *info_reg;
}

uint32_t flex_get_barrier_num_cluster_y(){
    volatile uint32_t * info_reg      = (volatile uint32_t *) (ARCH_CLUSTER_REG_BASE+16);
    return *info_reg;
}

void flex_annotate_barrier(uint32_t type){
    volatile uint32_t * info_reg      = (volatile uint32_t *) (ARCH_CLUSTER_REG_BASE+20);
    *info_reg = type;
}

void flex_reset_barrier(uint32_t* barrier){
    *barrier = flex_get_disable_value();
}

uint32_t flex_amo_fetch_add(uint32_t* barrier){
    return __atomic_fetch_add(barrier, flex_get_enable_value(), __ATOMIC_RELAXED);
}

void flex_intra_cluster_sync(){
#ifdef MEMPOOL_CLUSTER_UNIT
    // Mempool-based cluster: use plain barrier for repeated intra-cluster sync.
    // [mempool_barrier_init() | flex_barrier_init() | flex_barrier_xy_init()] must be done once before first use.
    uint32_t num_cores = mempool_get_core_count();
    mempool_barrier(num_cores);
#else
    // Snitch-based cluster: use hardware barrier CSR
    asm volatile("csrr x0, 0x7C2" ::: "memory");
#endif
}

inline void flex_wakeup_clusters(uint8_t row_mask, uint8_t col_mask)
{
    volatile uint32_t * wakeup_reg   = (volatile uint32_t *) (ARCH_CLUSTER_REG_BASE+28);
    uint32_t value = (((uint32_t)col_mask) << 16) | row_mask;
    *wakeup_reg = value;
}

inline void flex_wakeup_all_clusters()
{
    volatile uint32_t * wakeup_reg   = (volatile uint32_t *) (ARCH_CLUSTER_REG_BASE+28);
    uint32_t value = flex_get_disable_value();
    *wakeup_reg = value;
}

void flex_barrier_init(){
#ifdef MEMPOOL_CLUSTER_UNIT
    // Initialize mempool barrier state once before using repeated intra-cluster barriers.
    uint32_t core_id = mempool_get_core_id();
    mempool_barrier_init(core_id);
#endif
    volatile uint32_t * barrier      = (volatile uint32_t *) ARCH_SYNC_BASE;
    volatile uint32_t * cluster_reg  = (volatile uint32_t *) ARCH_CLUSTER_REG_BASE;

    if (flex_is_dm_core()){
        if (flex_get_cluster_id() == 0)
        {
            // __atomic_store_n(barrier, 0, __ATOMIC_RELAXED);
            flex_reset_barrier(barrier);
            flex_wakeup_all_clusters();
        }
        *cluster_reg = flex_get_enable_value();
    }

    flex_intra_cluster_sync();
}

void flex_global_barrier(){
    volatile uint32_t * barrier      = (volatile uint32_t *) ARCH_SYNC_BASE;
    volatile uint32_t * cluster_reg  = (volatile uint32_t *) ARCH_CLUSTER_REG_BASE;

    flex_intra_cluster_sync();

    if (flex_is_dm_core()){
        flex_annotate_barrier(0);
        if ((flex_get_barrier_num_cluster() - flex_get_enable_value()) == flex_amo_fetch_add(barrier)) {
            flex_reset_barrier(barrier);
            flex_wakeup_all_clusters();
        }
        *cluster_reg = flex_get_enable_value();
        flex_annotate_barrier(0);
    }

    flex_intra_cluster_sync();
}

void flex_global_barrier_polling(){
    volatile uint32_t * barrier      = (volatile uint32_t *) ARCH_SYNC_BASE;
    volatile uint32_t * barrier_iter = (volatile uint32_t *) (ARCH_SYNC_BASE + 4);

    flex_intra_cluster_sync();

    if (flex_is_dm_core()){
        flex_annotate_barrier(0);
        // Remember previous iteration
        uint32_t prev_barrier_iteration = *barrier_iter;

        if ((flex_get_barrier_num_cluster() - flex_get_enable_value()) == flex_amo_fetch_add(barrier)) {
            flex_reset_barrier(barrier);
            flex_amo_fetch_add(barrier_iter);
        } else {
            while((*barrier_iter) == prev_barrier_iteration);
        }
        flex_annotate_barrier(0);
    }

    flex_intra_cluster_sync();
}

void flex_barrier_xy_init(){
#ifdef MEMPOOL_CLUSTER_UNIT
    // Initialize mempool barrier state once before using repeated intra-cluster barriers.
    uint32_t core_id = mempool_get_core_id();
    mempool_barrier_init(core_id);
#endif
    FlexPosition        pos          = get_pos(flex_get_cluster_id());
    uint32_t            pos_x_middel = (ARCH_NUM_CLUSTER_X)/2;
    uint32_t            pos_y_middel = (ARCH_NUM_CLUSTER_Y)/2;
    volatile uint32_t * barrier_y    = (volatile uint32_t *) (ARCH_SYNC_BASE+(cluster_index(pos_x_middel,pos_y_middel)*ARCH_SYNC_SIZE)+16);
    volatile uint32_t * cluster_reg  = (volatile uint32_t *) ARCH_CLUSTER_REG_BASE;

    if (flex_is_dm_core()){
        if (flex_get_cluster_id() == 0)
        {
            flex_reset_barrier(barrier_y);
            for (int i = 0; i < ARCH_NUM_CLUSTER_Y; ++i)
            {
                volatile uint32_t * barrier_x = (volatile uint32_t *) (ARCH_SYNC_BASE+(cluster_index(pos_x_middel,i)*ARCH_SYNC_SIZE)+8);
                flex_reset_barrier(barrier_x);
            }
            flex_wakeup_all_clusters();
        }
        *cluster_reg = flex_get_enable_value();
    }

    flex_intra_cluster_sync();
}

void flex_global_barrier_xy(){

    flex_intra_cluster_sync();

    if (flex_is_dm_core()){
        flex_annotate_barrier(0);

        FlexPosition        pos          = get_pos(flex_get_cluster_id());
        uint32_t            pos_x_middel = (flex_get_barrier_num_cluster_x())/2;
        uint32_t            pos_y_middel = (flex_get_barrier_num_cluster_y())/2;
        volatile uint32_t * barrier_x    = (volatile uint32_t *) (ARCH_SYNC_BASE+(cluster_index(pos_x_middel,pos.y       )*ARCH_SYNC_SIZE)+8);
        volatile uint32_t * barrier_y    = (volatile uint32_t *) (ARCH_SYNC_BASE+(cluster_index(pos_x_middel,pos_y_middel)*ARCH_SYNC_SIZE)+16);
        volatile uint32_t * cluster_reg  = (volatile uint32_t *) ARCH_CLUSTER_REG_BASE;

        //First Barrier X
        if ((flex_get_barrier_num_cluster_x() - flex_get_enable_value()) == flex_amo_fetch_add(barrier_x)) {
            flex_reset_barrier(barrier_x);

            //For cluster synced X, then sync Y
            if ((flex_get_barrier_num_cluster_y() - flex_get_enable_value()) == flex_amo_fetch_add(barrier_y))
            {
                flex_reset_barrier(barrier_y);
                flex_wakeup_all_clusters();
            }
        }
        *cluster_reg = flex_get_enable_value();

        flex_annotate_barrier(0);
    }

    flex_intra_cluster_sync();
}

void flex_global_barrier_xy_polling(){

    flex_intra_cluster_sync();

    if (flex_is_dm_core()){
        flex_annotate_barrier(0);

        FlexPosition        pos          = get_pos(flex_get_cluster_id());
        uint32_t            pos_x_middel = (flex_get_barrier_num_cluster_x())/2;
        uint32_t            pos_y_middel = (flex_get_barrier_num_cluster_y())/2;
        volatile uint32_t * barrier_x    = (volatile uint32_t *) (ARCH_SYNC_BASE+(cluster_index(pos_x_middel,pos.y       )*ARCH_SYNC_SIZE)+8);
        volatile uint32_t * barrier_ix   = (volatile uint32_t *) (ARCH_SYNC_BASE+(cluster_index(pos_x_middel,pos.y       )*ARCH_SYNC_SIZE)+12);
        volatile uint32_t * barrier_y    = (volatile uint32_t *) (ARCH_SYNC_BASE+(cluster_index(pos_x_middel,pos_y_middel)*ARCH_SYNC_SIZE)+16);
        volatile uint32_t * barrier_iy   = (volatile uint32_t *) (ARCH_SYNC_BASE+(cluster_index(pos_x_middel,pos_y_middel)*ARCH_SYNC_SIZE)+20);

        // Remember previous iteration
        uint32_t prev_barrier_iter_x     = *barrier_ix;
        uint32_t prev_barrier_iter_y     = *barrier_iy;

        //First Barrier X
        if ((flex_get_barrier_num_cluster_x() - flex_get_enable_value()) == flex_amo_fetch_add(barrier_x)) {
            flex_reset_barrier(barrier_x);

            //For cluster synced X, then sync Y
            if ((flex_get_barrier_num_cluster_y() - flex_get_enable_value()) == flex_amo_fetch_add(barrier_y))
            {
                flex_reset_barrier(barrier_y);
                flex_amo_fetch_add(barrier_iy);
            } else {
                while((*barrier_iy) == prev_barrier_iter_y);
            }

            flex_amo_fetch_add(barrier_ix);
        } else {
            while((*barrier_ix) == prev_barrier_iter_x);
        }

        flex_annotate_barrier(0);
    }

    flex_intra_cluster_sync();
}

/*******************
*        EoC       *
*******************/

void flex_eoc(uint32_t val){
    volatile uint32_t * eoc_reg = (volatile uint32_t *) ARCH_SOC_REGISTER_EOC;
    *eoc_reg = val;
}

/*******************
*   Perf Counter   *
*******************/

void flex_timer_start(){
    volatile uint32_t * start_reg    = (volatile uint32_t *) (ARCH_SOC_REGISTER_EOC + 8);
    *start_reg = flex_get_enable_value();
}

void flex_timer_end(){
    volatile uint32_t * end_reg = (volatile uint32_t *) (ARCH_SOC_REGISTER_EOC + 12);
    *end_reg = flex_get_enable_value();
}

/*******************
*      Logging     *
*******************/

void flex_log_char(char c){
    uint32_t data = (uint32_t) c;
    volatile uint32_t * log_reg = (volatile uint32_t *)(ARCH_SOC_REGISTER_EOC + 16);
    *log_reg = data;
}

void flex_print(char * str){
    for (int i = 0; str[i] != '\0'; i++) {
        flex_log_char(str[i]);
    }
}

void flex_print_int(uint32_t data){
    volatile uint32_t * log_reg = (volatile uint32_t *)(ARCH_SOC_REGISTER_EOC + 20);
    *log_reg = data;
}

/************************
*      Stop at Time     *
************************/

void flex_sat(uint32_t val){
    volatile uint32_t * sat_reg = (volatile uint32_t *) (ARCH_SOC_REGISTER_EOC + 40);
    *sat_reg = val;
}

#endif