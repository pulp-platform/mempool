#!/usr/bin/env bash
# Copyright 2020 ETH Zurich and University of Bologna.
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

# Author: Samuel Riedel, ETH Zurich


if [[ -n "$CI_MERGE_REQUEST_ID" ]]; then
  # Make sure we have the latest version of the target branch
  git fetch origin $CI_MERGE_REQUEST_TARGET_BRANCH_NAME
  base="origin/$CI_MERGE_REQUEST_TARGET_BRANCH_NAME"
elif [[ -n "$1" ]]; then
  base="$1"
else
  base="HEAD~1"
fi

echo "Comparing HEAD to $base"

# Check for clang format
files=$(git diff --name-only $base HEAD)
EXIT_STATUS=0

# Only check files that still exist
files=$(echo "$files" | xargs ls -d 2>/dev/null)

# Only check C and C++ files for clang-format compatibility
echo "Checking C/C++ files for clang-format compliance"
clang_files=$(echo "$files" | grep -P "(?<!\.ld)\.(h|c|cpp)\b")
# Remove files from dependencies
clang_files=$(echo "$clang_files" | grep -vP "hardware/deps/")
clang_files=$(echo "$clang_files" | grep -vP "toolchain/")
clang_files=$(echo "$clang_files" | grep -vP "be/")
for file in $clang_files; do
  echo $file
  ./.gitlab-ci.d/run_clang_format.py \
    --clang-format-executable install/llvm/bin/clang-format \
    $file || EXIT_STATUS=$?
done

# Check for trailing whitespaces and tabs
echo "Checking for trailing whitespaces and tabs"
git diff --check $base HEAD -- \
    ':(exclude)**.def' \
    ':(exclude)**.patch' \
    ':(exclude)toolchain/**' \
    ':(exclude)apps/riscv-tests/**' \
    || EXIT_STATUS=$?

exit $EXIT_STATUS
