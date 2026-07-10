#!/bin/bash
# Test runner for Miracula using features.m

# Colors
GREEN='\033[0;32m'
RED='\033[0;31m'
NC='\033[0m' # No Color

echo "=================================================="
echo " Running Miracula Language Verification Tests"
echo "=================================================="

# Arrays of expressions and expected outputs
declare -a exprs=(
  "val_add"
  "val_sub"
  "val_mul"
  "val_mod"
  "is_equal"
  "is_not_equal"
  "is_less_than"
  "abs (0 - 5)"
  "factorial 5"
  "add_two 8"
  "fib 6"
  "list_len [1, 2, 3, 4]"
  "first_element (9, 10)"
  "swap_pair (1, 2)"
  "is_lowercase_a 'a'"
  "is_lowercase_a 'b'"
  "get_head"
  "get_tail"
  "hd lazy_range"
  "hd (tl lazy_range)"
  "evens_up_to_10"
  "cartesian_product"
  "filter_first_elements"
  "add_five 10"
  "result_closure"
  "first_three_ones"
)

declare -a expecteds=(
  "7"
  "3"
  "42"
  "1"
  "1"
  "1"
  "1"
  "5"
  "120"
  "10"
  "8"
  "4"
  "9"
  "(2,1)"
  "1"
  "0"
  "10"
  "[20,30]"
  "1"
  "2"
  "[2,4,6,8,10]"
  "[(1,4),(1,5),(1,6),(2,4),(2,5),(2,6),(3,4),(3,5),(3,6)]"
  "[1,3,5]"
  "15"
  "15"
  "3"
)

failed=0
total=${#exprs[@]}

for ((i=0; i<total; i++)); do
  expr="${exprs[$i]}"
  expected="${expecteds[$i]}"
  
  output=$(echo "$expr" | ./miracula features.m 2>/dev/null | sed -n 's/.*Result:[[:space:]]*//p')
  
  # Strip trailing/leading spaces
  output=$(echo "$output" | xargs)
  
  if [ "$output" = "$expected" ]; then
    echo -e "Test $((i+1))/$total: ${GREEN}PASS${NC} -> $expr = $output"
  else
    echo -e "Test $((i+1))/$total: ${RED}FAIL${NC} -> $expr"
    echo -e "  Expected: $expected"
    echo -e "  Got:      $output"
    failed=$((failed + 1))
  fi
done

echo "=================================================="
if [ $failed -eq 0 ]; then
  echo -e "${GREEN}ALL $total TESTS PASSED!${NC}"
  exit 0
else
  echo -e "${RED}$failed/$total TESTS FAILED!${NC}"
  exit 1
fi
