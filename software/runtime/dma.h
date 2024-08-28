// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich

// ATTENTION: The DMA is in a very preliminary state and likely to cause issues.

#ifndef _DMA_H_
#define _DMA_H_

#include <stdbool.h>
#include <stdint.h>

#include "mempool_dma_frontend.h"
#include "runtime.h"

#define DMA_BASE(id) (0x40010000 + (id * 0x10000))

static inline void dma_config(uint32_t cluster_id, bool decouple, bool deburst,
                              bool serialize) {
  volatile uint32_t *_dma_conf_reg =
      (volatile uint32_t *)(DMA_BASE(cluster_id) +
                            MEMPOOL_DMA_FRONTEND_CONF_REG_OFFSET);
  // Configure the DMA
  uint32_t config = 0;
  config |= (uint32_t)decouple << MEMPOOL_DMA_FRONTEND_CONF_DECOUPLE_BIT;
  config |= (uint32_t)deburst << MEMPOOL_DMA_FRONTEND_CONF_DEBURST_BIT;
  config |= (uint32_t)serialize << MEMPOOL_DMA_FRONTEND_CONF_SERIALIZE_BIT;
  *_dma_conf_reg = config;
}

static inline uint32_t dma_idle(uint32_t cluster_id) {
  volatile uint32_t *_dma_status_reg =
      (volatile uint32_t *)(DMA_BASE(cluster_id) +
                            MEMPOOL_DMA_FRONTEND_STATUS_REG_OFFSET);
  return (*_dma_status_reg) & (0x1 << MEMPOOL_DMA_FRONTEND_STATUS_BUSY_BIT);
}

static inline uint32_t dma_done(uint32_t cluster_id) {
  volatile uint32_t *_dma_done_reg =
      (volatile uint32_t *)(DMA_BASE(cluster_id) +
                            MEMPOOL_DMA_FRONTEND_DONE_REG_OFFSET);
  return *_dma_done_reg;
}

static inline void dma_wait(uint32_t cluster_id) {
  while (!dma_done(cluster_id))
    ;
}

void dma_memcpy_nonblocking(uint32_t cluster_id, void *dest, const void *src,
                            size_t len) {
  volatile uint32_t *_dma_src_reg =
      (volatile uint32_t *)(DMA_BASE(cluster_id) +
                            MEMPOOL_DMA_FRONTEND_SRC_ADDR_REG_OFFSET);
  volatile uint32_t *_dma_dst_reg =
      (volatile uint32_t *)(DMA_BASE(cluster_id) +
                            MEMPOOL_DMA_FRONTEND_DST_ADDR_REG_OFFSET);
  volatile uint32_t *_dma_len_reg =
      (volatile uint32_t *)(DMA_BASE(cluster_id) +
                            MEMPOOL_DMA_FRONTEND_NUM_BYTES_REG_OFFSET);
  volatile uint32_t *_dma_id_reg =
      (volatile uint32_t *)(DMA_BASE(cluster_id) +
                            MEMPOOL_DMA_FRONTEND_NEXT_ID_REG_OFFSET);
  // Configure the DMA
  *_dma_src_reg = (uint32_t)src;
  *_dma_dst_reg = (uint32_t)dest;
  *_dma_len_reg = (uint32_t)len;
  // Full memory barrier
  __sync_synchronize();
  // Launch the transfer
  (void)*_dma_id_reg;
  // Full memory barrier
  __sync_synchronize();
}

void dma_memcpy_blocking(uint32_t cluster_id, void *dest, const void *src,
                         size_t len) {
  dma_memcpy_nonblocking(cluster_id, dest, src, len);
  dma_wait(cluster_id);
}
#endif // _DMA_H_
