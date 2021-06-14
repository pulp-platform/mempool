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

# Execute from git's root dir
cd $(git rev-parse --show-toplevel 2>/dev/null)

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

# Remove files from dependencies
files=$(echo "$files" | grep -vP "hardware/deps/")
files=$(echo "$files" | grep -vP "toolchain/")

# Only check C and C++ files for clang-format compatibility
echo "Checking C/C++ files for clang-format compliance"
clang_files=$(echo "$files" | grep -P "(?<!\.ld)\.(h|c|cpp)\b")
for file in $clang_files; do
  echo $file
  ./scripts/run_clang_format.py \
    --clang-format-executable install/llvm/bin/clang-format \
    $file || EXIT_STATUS=$?
done

# Only check python files for flake8 compatibility
if [[ -n "$GITLAB_CI" ]]; then
  # Special case for gitlab ci, since it has an old default python
  python3=$(command -v python3.6) || EXIT_STATUS=$?
else
  python3=$(command -v python3) || EXIT_STATUS=$?
fi

echo "Checking python files for flake8 compliance"
py_files=$(echo "$files" | grep -P "\.(py)\b")
for file in $py_files; do
  echo $file
  $python3 -m flake8 $file || EXIT_STATUS=$?
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
