// Copyright 2024 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "kmp/team.hpp"
#include "kmp/types.h"
#include <array>
#include <utility>

namespace kmp {

namespace runtime {

template <std::size_t... Is>
constexpr std::array<Thread, sizeof...(Is)>
sequencetoArray(std::integer_sequence<kmp_uint32, Is...> /*unused*/) {
  return {{Is...}};
}

std::array<Thread, NUM_CORES> threads =
    sequencetoArray(std::make_integer_sequence<kmp_uint32, NUM_CORES>{});

Team defaultTeam(0, 0);

std::optional<kmp_uint32> requestedNumTeams;
std::optional<kmp_uint32> requestedThreadLimit;
kmp_uint32 numTeams = 1;

Barrier teamsBarrier(NUM_GROUPS);

} // namespace runtime

} // namespace kmp
