#include "flex_runtime.h"

int main() {
    uint32_t eoc_val = 0;
    flex_barrier_xy_init();
    flex_global_barrier_xy();
    uint32_t core_id = flex_get_core_id();
    uint32_t cluster_id = flex_get_cluster_id();

    if (core_id == 0 && cluster_id == 0) {
        flex_print("=== ID Queries ===\n");

        flex_print("core_id=");
        flex_print_int(core_id);
        flex_print("\n");

        flex_print("cluster_id=");
        flex_print_int(cluster_id);
        flex_print("\n");

        flex_print("is_first_core=");
        flex_print_int(flex_is_first_core());
        flex_print("\n");

        flex_print("is_dm_core=");
        flex_print_int(flex_is_dm_core());
        flex_print("\n");

        // Mempool-level queries
        flex_print("mempool_core_id=");
        flex_print_int(mempool_get_core_id());
        flex_print("\n");

        flex_print("mempool_tile_id=");
        flex_print_int(mempool_get_tile_id());
        flex_print("\n");

        flex_print("mempool_group_id=");
        flex_print_int(mempool_get_group_id());
        flex_print("\n");

        flex_print("mempool_core_count=");
        flex_print_int(mempool_get_core_count());
        flex_print("\n");

        // FlexCluster position
        FlexPosition pos = get_pos(cluster_id);
        flex_print("pos.x=");
        flex_print_int(pos.x);
        flex_print(" pos.y=");
        flex_print_int(pos.y);
        flex_print("\n");

        flex_print("PASS\n");
        flex_eoc(0);
    }

    flex_global_barrier_xy();
    flex_eoc(eoc_val);
    return 0;
}
