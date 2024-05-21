#include "kmp/team.hpp"
#include "kmp/types.h"
#include <array>
#include <utility>

extern "C" {
#include "runtime.h"
}

namespace kmp {

namespace runtime {

template <std::size_t... Is>
constexpr std::array<Thread, sizeof...(Is)>
sequencetoArray(std::integer_sequence<kmp_uint32, Is...> /*unused*/) {
  return {{Is...}};
}

std::array<Thread, NUM_CORES> threads =
    sequencetoArray(std::make_integer_sequence<kmp_uint32, NUM_CORES>{});

Team defaultTeam(0, NUM_CORES, std::nullopt);

} // namespace runtime

} // namespace kmp
