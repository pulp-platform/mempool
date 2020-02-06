#include "printf.h"
#include <stdint.h>
#include <string.h>
#include "encoding.h"

volatile uint32_t atomic __attribute__ ((section (".l1")));

extern volatile uint32_t tcdm_start_address_reg;
extern volatile uint32_t tcdm_end_address_reg;

int main(uint32_t coreid, uint32_t num_cores) {
    //TODO(sriedel): This is a hack, to be fixed when MemPool has a fence mechanism.
    if (coreid == 0)
      atomic = 0;

    while (atomic != coreid);

    printf("Core %d says Hello!\n", coreid);
    // increment mutex
    //__atomic_add_fetch(&atomic, 1, __ATOMIC_RELAXED);
    atomic++;
    // wait until all cores have finished
    while (atomic != num_cores);
    return 0;
}
