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

PROJECT_DIR="$(dirname "$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")")"

# Import functions
source ${PROJECT_DIR}/scripts/functions.sh

# Set installation directories for toolchains
INSTALL_PREFIX=install
export INSTALL_DIR=${PROJECT_DIR}/${INSTALL_PREFIX}
export LLVM_INSTALL_DIR=${INSTALL_DIR}/llvm
export HALIDE_INSTALL_DIR=${INSTALL_DIR}/halide
export GCC_INSTALL_DIR=${INSTALL_DIR}/riscv-gcc

# Configure PATH for RISC-V toolchain and PULP-SDK
export PULP_RISCV_GCC_TOOLCHAIN=${GCC_INSTALL_DIR}
GCC_BIN_PATH=${PULP_RISCV_GCC_TOOLCHAIN}/bin
[[ ":$PATH:" != *":${GCC_BIN_PATH}:"* ]] && export PATH="${GCC_BIN_PATH}:${PATH}"

# Specify preferred tool versions
rm -rf ${INSTALL_DIR}/bin
set_preferred_tool CMAKE cmake-3.7.1
set_preferred_tool CXX   g++-8.2.0
set_preferred_tool CC    gcc-8.2.0

# Hack for the PULP-SDK, which ignores the environment variables for some modules but respects it for others
TOOL_DIR=${INSTALL_DIR}/bin
mkdir -p ${INSTALL_DIR}/bin
[[ "${TOOL_DIR}" != *"${CMAKE}"*  ]] && ln -sf ${CMAKE} ${TOOL_DIR}/cmake
[[ "${TOOL_DIR}" != *"${CXX}"*    ]] && ln -sf ${CXX}   ${TOOL_DIR}/g++
[[ "${TOOL_DIR}" != *"${CC}"*     ]] && ln -sf ${CC}    ${TOOL_DIR}/gcc
[[ ":$PATH:" != *":${TOOL_DIR}:"* ]] && export PATH="${TOOL_DIR}:${PATH}"

# Git SSH or HTTPS
GIT_USE_SSH=1
# Do not enable SSH if we are the GitLab CI runner
[[ -z $GITLAB_CI ]] && export PULP_GITHUB_SSH=${GIT_USE_SSH}

# Source PULP-SDK setup if it is built
PULP_SDK_SOURCEME=${PROJECT_DIR}/toolchain/pulp-sdk/sourceme.sh
if [[ -r ${PULP_SDK_SOURCEME} ]]; then
    source ${PULP_SDK_SOURCEME}
else
    echo "PULP-SDK sourceme.sh file not found at ${PULP_SDK_SOURCEME}"
fi
