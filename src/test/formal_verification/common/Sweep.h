#pragma once

#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

namespace xrpl::test::formal_verification {

// Offsets applied to each moved value of a hardcoded cusp row: two units either side, and the row
// itself.
constexpr std::int64_t kAroundCusp[] = {-2, -1, 0, 1, 2};

// A row that sits exactly on its cusp, and every case tested around it.
template <class Row>
struct AroundCusp
{
    Row cusp;
    std::vector<Row> cases;
};

// Each row with its members `first` and `second` moved by every pair of offsets in kAroundCusp,
// keeping the moved rows `valid` accepts.
template <class Row, std::size_t N, class Valid>
std::vector<AroundCusp<Row>>
aroundCusp(Row const (&rows)[N], std::int64_t Row::* first, std::int64_t Row::* second, Valid valid)
{
    std::vector<AroundCusp<Row>> groups;
    for (Row const& row : rows)
    {
        AroundCusp<Row> group{.cusp = row, .cases = {}};
        for (std::int64_t const dFirst : kAroundCusp)
        {
            for (std::int64_t const dSecond : kAroundCusp)
            {
                Row moved = row;
                moved.*first += dFirst;
                moved.*second += dSecond;
                if (valid(moved))
                    group.cases.push_back(moved);
            }
        }
        groups.push_back(group);
    }
    return groups;
}

// A single value moved by kAroundCusp.
inline std::vector<AroundCusp<std::int64_t>>
aroundCusp(std::int64_t value)
{
    AroundCusp<std::int64_t> group{.cusp = value, .cases = {}};
    for (std::int64_t const d : kAroundCusp)
        group.cases.push_back(value + d);
    return {group};
}

// A single-value row as it appears in failure messages.
inline std::string
describe(std::int64_t value)
{
    return "value " + std::to_string(value);
}

}  // namespace xrpl::test::formal_verification
