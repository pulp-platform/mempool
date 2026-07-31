#include "mc_runtime.h"

int main() {
    uint32_t eoc_val = 0;
    mc_barrier_xy_init();
    mc_global_barrier_xy();
    uint32_t core_id = mc_get_core_id();
    uint32_t cluster_id = mc_get_cluster_id();

    if (core_id == 0 && cluster_id == 0) {
        mc_print("=== ID Queries ===\n");

        mc_print("core_id=");
        mc_print_int(core_id);
        mc_print("\n");

        mc_print("cluster_id=");
        mc_print_int(cluster_id);
        mc_print("\n");

        mc_print("is_first_core=");
        mc_print_int(mc_is_first_core());
        mc_print("\n");

        mc_print("is_dm_core=");
        mc_print_int(mc_is_dm_core());
        mc_print("\n");

        // Mempool-level queries
        mc_print("mempool_core_id=");
        mc_print_int(mempool_get_core_id());
        mc_print("\n");

        mc_print("mempool_tile_id=");
        mc_print_int(mempool_get_tile_id());
        mc_print("\n");

        mc_print("mempool_group_id=");
        mc_print_int(mempool_get_group_id());
        mc_print("\n");

        mc_print("mempool_core_count=");
        mc_print_int(mempool_get_core_count());
        mc_print("\n");

        // FlexCluster position
        McPosition pos = get_pos(cluster_id);
        mc_print("pos.x=");
        mc_print_int(pos.x);
        mc_print(" pos.y=");
        mc_print_int(pos.y);
        mc_print("\n");

        mc_print("PASS\n");
        mc_eoc(0);
    }

    mc_global_barrier_xy();
    mc_eoc(eoc_val);
    return 0;
}
