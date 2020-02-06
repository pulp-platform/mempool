# Copyright 2019 ETH Zurich and University of Bologna.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#    http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# Author: Matheus Cavalcante, ETH Zurich

include $(CURDIR)/common/runtime.mk

all: bin/hello_world
#all: bin/gradient

bin/%: %/main.c.o $(RUNTIME)
	mkdir -p $(shell dirname $@)
	$(RISCV_CC) -Iinclude $(RISCV_LDFLAGS) -o $@ $^ -T$(CURDIR)/common/link.ld
	$(RISCV_STRIP) $@ -g -S -d --strip-debug
	$(RISCV_OBJDUMP) -D $@ > $@.dump

clean:
	rm -rf $(EXE)
	rm -rf $(OBJ)
	rm -rf $(DHRYSTONE_OBJ)
	rm -rf $(COREMARK_OBJ)
	rm -rf *.dump

.PHONY: clean
