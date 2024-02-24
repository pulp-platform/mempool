#ifndef _ELFLOADER_H
#define _ELFLOADER_H

#include <fesvr/elf.h>
#include <fesvr/memif.h>

#include <cstring>
#include <string>
#include <sys/stat.h>
#include <fcntl.h>
#include <sys/mman.h>
#include <assert.h>
#include <unistd.h>
#include <stdlib.h>
#include <stdio.h>
#include <vector>
#include <map>
#include <iostream>

char elfloader_get_section (long long* address, long long* len);
char elfloader_read_section (long long address, unsigned char * buf);
void elfloader_read_elf(const char* filename, long long dest_size, long long dest_base_addr, unsigned char * dest_buffer);

#endif