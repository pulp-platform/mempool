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

# Specify a desired tool version
# Usage:   set_preferred_tool ENV_NAME TOOL_VERSION
# Example: set_preferred_tool CXX      g++-8.2.0
function set_preferred_tool() {
    if [[ $# -ne 2 ]]; then
        echo "set_preferred_tool: Require two arguments: 1: env variable name, 2 tool version"
    fi

    if [[ -x $(command -v $2) ]]; then
        export $1=$(command -v $2)
    else
        echo "Your preferred $1 version ($2) does not exist!"
    fi
}
