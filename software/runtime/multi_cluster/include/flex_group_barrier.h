#ifndef _FLEX_GROUP_BARRIER_H_
#define _FLEX_GROUP_BARRIER_H_

#include "flex_runtime.h"
#include "flex_cluster_arch.h"

/*****************************************
*  Grid Group Synchronization functions  *
*****************************************/

typedef struct GridSyncGroupInfo
{
    //General information
    uint32_t valid_grid;
    uint32_t grid_x_dim;
    uint32_t grid_y_dim;
    uint32_t grid_x_num;
    uint32_t grid_y_num;

    //Local information
    uint32_t this_grid_id;
    uint32_t this_grid_id_x;
    uint32_t this_grid_id_y;
    uint32_t this_grid_left_most;
    uint32_t this_grid_right_most;
    uint32_t this_grid_top_most;
    uint32_t this_grid_bottom_most;
    uint32_t this_grid_cluster_num;
    uint32_t this_grid_cluster_num_x;
    uint32_t this_grid_cluster_num_y;

    //Sync information
    uint8_t  wakeup_row_mask;
    uint8_t  wakeup_col_mask;
    uint32_t sync_x_cluster;
    uint32_t sync_y_cluster;
    volatile uint32_t * sync_x_point;
    volatile uint32_t * sync_x_piter;
    volatile uint32_t * sync_y_point;
    volatile uint32_t * sync_y_piter;
}GridSyncGroupInfo;

GridSyncGroupInfo grid_sync_group_init(uint32_t grid_x_dim, uint32_t grid_y_dim){
	GridSyncGroupInfo info;

	//Calculate information
	info.valid_grid = 1;
	info.grid_x_dim = grid_x_dim;
	info.grid_y_dim = grid_y_dim;

	if (grid_x_dim == 0 || grid_y_dim == 0)
	{
		info.valid_grid = 0;
		return info;
	}

    if (!(is_power_of_two(grid_x_dim) && is_power_of_two(grid_y_dim)))
    {
        info.valid_grid = 0;
        return info;
    }

	info.grid_x_num = (ARCH_NUM_CLUSTER_X + grid_x_dim - 1)/grid_x_dim;
	info.grid_y_num = (ARCH_NUM_CLUSTER_Y + grid_y_dim - 1)/grid_y_dim;

	FlexPosition pos = get_pos(flex_get_cluster_id());
	info.this_grid_id_x = pos.x/grid_x_dim;
	info.this_grid_id_y = pos.y/grid_y_dim;
	info.this_grid_id   = info.grid_x_num * info.this_grid_id_y + info.this_grid_id_x;
	info.this_grid_left_most = info.this_grid_id_x * grid_x_dim;
	info.this_grid_right_most = (info.this_grid_id_x + 1) * grid_x_dim - 1;
	info.this_grid_right_most = info.this_grid_right_most >= ARCH_NUM_CLUSTER_X? ARCH_NUM_CLUSTER_X - 1 : info.this_grid_right_most;
	info.this_grid_bottom_most = info.this_grid_id_y * grid_y_dim;
	info.this_grid_top_most = (info.this_grid_id_y + 1) * grid_y_dim - 1;
	info.this_grid_top_most = info.this_grid_top_most >= ARCH_NUM_CLUSTER_Y? ARCH_NUM_CLUSTER_Y - 1 : info.this_grid_top_most;
	info.this_grid_cluster_num_x = info.this_grid_right_most + 1 - info.this_grid_left_most;
	info.this_grid_cluster_num_y = info.this_grid_top_most + 1 - info.this_grid_bottom_most;
    info.this_grid_cluster_num   = info.this_grid_cluster_num_x * info.this_grid_cluster_num_y;

    info.wakeup_row_mask= ~(info.grid_x_dim - 1);
    info.wakeup_col_mask= ~(info.grid_y_dim - 1);
	info.sync_x_cluster = (info.this_grid_left_most + info.this_grid_right_most)/2;
	info.sync_y_cluster = (info.this_grid_bottom_most + info.this_grid_top_most)/2;
	info.sync_x_point   = (volatile uint32_t *) (ARCH_SYNC_BASE+(cluster_index(info.sync_x_cluster,pos.y              )*ARCH_SYNC_SIZE)+24);
    info.sync_x_piter   = (volatile uint32_t *) (ARCH_SYNC_BASE+(cluster_index(info.sync_x_cluster,pos.y              )*ARCH_SYNC_SIZE)+28);
    info.sync_y_point   = (volatile uint32_t *) (ARCH_SYNC_BASE+(cluster_index(info.sync_x_cluster,info.sync_y_cluster)*ARCH_SYNC_SIZE)+32);
    info.sync_y_piter   = (volatile uint32_t *) (ARCH_SYNC_BASE+(cluster_index(info.sync_x_cluster,info.sync_y_cluster)*ARCH_SYNC_SIZE)+36);

	if (flex_get_core_id() == 0)
	{
		//Reset synchronization point
		volatile uint32_t * local_sync_point_for_group_level1 = (volatile uint32_t *) (ARCH_SYNC_BASE+(flex_get_cluster_id()*ARCH_SYNC_SIZE)+24);
		volatile uint32_t * local_sync_point_for_group_level2 = (volatile uint32_t *) (ARCH_SYNC_BASE+(flex_get_cluster_id()*ARCH_SYNC_SIZE)+32);
		*local_sync_point_for_group_level1 = 0;
		*local_sync_point_for_group_level2 = 0;
	}

	return info;
}


void grid_sync_group_barrier_xy(GridSyncGroupInfo * info){

    flex_intra_cluster_sync();

    if (flex_is_dm_core()){
        flex_annotate_barrier(0);

    	volatile uint32_t * cluster_wfi_reg  = (volatile uint32_t *) ARCH_CLUSTER_REG_BASE;

        //First Barrier X
        if ((info->this_grid_cluster_num_x - flex_get_enable_value()) == flex_amo_fetch_add(info->sync_x_point)) {
            flex_reset_barrier(info->sync_x_point);

            //For cluster synced X, then sync Y
            if ((info->this_grid_cluster_num_y - flex_get_enable_value()) == flex_amo_fetch_add(info->sync_y_point))
            {
                flex_reset_barrier(info->sync_y_point);
                flex_wakeup_clusters(info->wakeup_row_mask,info->wakeup_col_mask);
            }
        }
        *cluster_wfi_reg = flex_get_enable_value();

        flex_annotate_barrier(0);
    }

    flex_intra_cluster_sync();
}

void grid_sync_group_barrier_xy_polling(GridSyncGroupInfo * info){

    flex_intra_cluster_sync();

    if (flex_is_dm_core()){
        flex_annotate_barrier(0);

        // Remember previous iteration
        uint32_t prev_barrier_iter_x     = *(info->sync_x_piter);
        uint32_t prev_barrier_iter_y     = *(info->sync_y_piter);

        //First Barrier X
        if ((info->this_grid_cluster_num_x - flex_get_enable_value()) == flex_amo_fetch_add(info->sync_x_point)) {
            flex_reset_barrier(info->sync_x_point);

            //For cluster synced X, then sync Y
            if ((info->this_grid_cluster_num_y - flex_get_enable_value()) == flex_amo_fetch_add(info->sync_y_point))
            {
                flex_reset_barrier(info->sync_y_point);
                flex_amo_fetch_add(info->sync_y_piter);
            } else {
                while((*(info->sync_y_piter)) == prev_barrier_iter_y);
            }

            flex_amo_fetch_add(info->sync_x_piter);
        } else {
            while((*(info->sync_x_piter)) == prev_barrier_iter_x);
        }
        flex_annotate_barrier(0);
    }

    flex_intra_cluster_sync();
}

#endif