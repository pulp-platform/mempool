#include "flex_runtime.h"
#include "flex_printf.h"

int main()
{
    uint32_t eoc_val = 0;
    flex_barrier_xy_init();
    flex_global_barrier_xy();
    /**************************************/
    /*  Program Execution Region -- Start */
    /**************************************/

    uint32_t cluster_id = flex_get_cluster_id();
    uint32_t core_id = flex_get_core_id();

    if (cluster_id == 0 && core_id == 0)
    {
        printf("Hello! I am core %d in cluster %d\n", core_id, cluster_id);
        printf("[System Configuration]\n");
        printf("    num_cluster_x           = %d\n", ARCH_NUM_CLUSTER_X);
        printf("    num_cluster_y           = %d\n", ARCH_NUM_CLUSTER_Y);
        printf("    num_core_per_cluster    = %d\n", ARCH_NUM_CORE_PER_CLUSTER);
        printf("[Cluster L1 Configuration]\n");
        printf("    cluster_tcdm_base       = 0x%08x\n", ARCH_CLUSTER_TCDM_BASE);
        printf("    cluster_tcdm_size       = 0x%08x\n", ARCH_CLUSTER_TCDM_SIZE);
        printf("    cluster_tcdm_remote     = 0x%08x\n", ARCH_CLUSTER_TCDM_REMOTE);
        printf("[HBM Configuration]\n");
        printf("    hbm_start_base          = 0x%08x\n", ARCH_HBM_START_BASE);
        printf("    hbm_node_addr_space     = 0x%08x\n", ARCH_HBM_NODE_ADDR_SPACE);
        printf("    num_node_per_ctrl       = %d\n", ARCH_NUM_NODE_PER_CTRL);
    }

    /**************************************/
    /*  Program Execution Region -- Stop  */
    /**************************************/
    flex_global_barrier_xy();
    flex_eoc(eoc_val);
    return 0;
}