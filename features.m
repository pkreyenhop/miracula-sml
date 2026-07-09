|| ==============================================================================
|| MIRACULA LANGUAGE FEATURES SHOWCASE
|| This file demonstrates every language feature supported by the Miracula engine.
|| Lines starting with '||' are treated as comments and ignored by the loader.
|| ==============================================================================

|| ------------------------------------------------------------------------------
|| 1. Basic Arithmetic and Comparisons
|| ------------------------------------------------------------------------------
|| Miracula supports standard integer arithmetic and comparison operators.
|| Addition (+), Subtraction (-), Multiplication (*), Modulo (mod).
|| Comparisons: ==, !=, <, >, <=, >=.

val_add = 3 + 4
val_sub = 10 - 7
val_mul = 6 * 7
val_mod = 10 mod 3

is_equal     = 5 == 5
is_not_equal = 5 != 6
is_less_than = 3 < 10


|| ------------------------------------------------------------------------------
|| 2. Conditionals (ifzero and if)
|| ------------------------------------------------------------------------------
|| 'ifzero' executes the 'then' branch if the condition is 0, else the 'else' branch.
|| 'if' executes the 'then' branch if the condition is non-zero (true), else the 'else' branch.

abs n = if n < 0 then 0 - n else n

factorial n = ifzero n then 1 else n * factorial (n - 1)


|| ------------------------------------------------------------------------------
|| 3. Lambda Abstractions
|| ------------------------------------------------------------------------------
|| Anonymous functions are defined using the backslash '\' and dot '.' syntax.

add_two = \x. x + 2
apply_lambda = (\x. x * 2) 5


|| ------------------------------------------------------------------------------
|| 4. Pattern Matching and Multi-Equation Functions
|| ------------------------------------------------------------------------------
|| Functions can be defined using multiple equations with pattern matching.
|| Patterns support integers, characters, empty lists ([]), cons (h:t), tuples,
|| and variable wildcards (_).

|| Pattern matching on Integers:
fib 0 = 0
fib 1 = 1
fib n = fib (n - 1) + fib (n - 2)

|| Pattern matching on Lists (empty list vs. cons cell):
list_len []     = 0
list_len (x:xs) = 1 + list_len xs

|| Pattern matching on Tuples and wildcards:
first_element (x, _) = x
swap_pair (x, y)     = (y, x)

|| Pattern matching on Characters:
is_lowercase_a 'a' = 1
is_lowercase_a _   = 0


|| ------------------------------------------------------------------------------
|| 5. List Operations (Consing, Concatenation, Ranges, and Primitives)
|| ------------------------------------------------------------------------------
|| Lists can be constructed using ':' (cons) or brackets '[1, 2]'.
|| Lists are concatenated using '++'.
|| 'hd' and 'tl' are built-in functions.
|| '[start..end]' creates a lazy range, evaluated only as elements are demanded.

list_cons = 1 : 2 : 3 : []
list_literal = [1, 2, 3]

list_append = [1, 2] ++ [3, 4]

get_head = hd [10, 20, 30]
get_tail = tl [10, 20, 30]

lazy_range = [1..1000]


|| ------------------------------------------------------------------------------
|| 6. ZF Expressions (List Comprehensions)
|| ------------------------------------------------------------------------------
|| List comprehensions use the '[expr | qualifiers]' syntax.
|| Qualifiers are separated by ';' and can be generators (pat <- src) or filters.

evens_up_to_10 = [x | x <- [1..10]; x mod 2 == 0]

cartesian_product = [(x, y) | x <- [1..3]; y <- [4..6]]

|| Nested generators matching specific patterns:
filter_first_elements = [x | (x, y) <- [(1, 2), (3, 4), (5, 6)]]


|| ------------------------------------------------------------------------------
|| 7. Operator Sectioning and Partial Application
|| ------------------------------------------------------------------------------
|| Binary operators wrapped in parentheses can be sectioned.
|| ( + ) desugars to \x. \y. x + y
|| ( + e ) desugars to \x. x + e
|| Sections are supported for '+', '-', and ':' (cons).

add_curried = ( + )
add_five = ( + 5 )

cons_element = ( : )
cons_to_empty = ( : [] )


|| ------------------------------------------------------------------------------
|| 8. Characters and Strings
|| ------------------------------------------------------------------------------
|| Character literals are single-quoted. String literals are double-quoted.
|| Strings are desugared at parse-time into lists of characters.

char_a = 'a'
char_escaped = '\n'

string_literal = "hello"
string_equivalent = 'h' : 'e' : 'l' : 'l' : 'o' : []


|| ------------------------------------------------------------------------------
|| 9. Lexical Scope and Closures
|| ------------------------------------------------------------------------------
|| Functions capture their surrounding lexical environment when defined.

make_adder x = \y. x + y
add_ten = make_adder 10
result_closure = add_ten 5


|| ------------------------------------------------------------------------------
|| 10. Lazy Evaluation and Cycle Detection
|| ------------------------------------------------------------------------------
|| Because expressions are evaluated call-by-need, infinite lists are possible.
|| Evaluating cyclic definitions triggers cycle/blackhole detection.

|| Infinite sequence of 1s:
ones = 1 : ones
first_three_ones = hd ones + hd (tl ones) + hd (tl (tl ones))

|| Cycle definition (evaluating this will trigger 'Blackhole' runtime exception):
|| cyclic_loop = cyclic_loop
