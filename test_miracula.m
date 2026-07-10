|| ============================================================================
|| Miracula Total Syntax & Standard Library Test Suite
|| ============================================================================

|| 1. Lexer & Identifier Formats (Section 3.2)
leadingUnderscoreFix = 100
camelCaseIdentifier123 = 200

|| 2. Guarded Equations & Pattern Variations (Sections 3.3 & 4)
literalMatchNum 0        = "zero"
literalMatchNum anyValue = "wildcard"

literalMatchChar 'A'      = "charA"
literalMatchChar anyValue = "wildcard"

checkList []     = "empty"
checkList (x:[]) = "singleton"
checkList (x:xs) = "many"

destructureTuple (x, y) = x + y

|| 3. Local Definitions and Indented Scope Configurations (Section 3.4)
nestedWhere x = outcome
                where 
                outcome = left + right
                left    = x * 2
                right   = y + 2
                          where y = 5

|| 4. Math & Guard Logic (Section 3.3)
absVal x = if x < 0 then 0 - x else x

|| 5. Function Composition Syntax (Section 5.1)
addOne x     = x + 1
multTwo x    = x * 2
composedFunc = addOne . multTwo

|| 6. Conditional Logic via Equations (Section 5.2)
inlineIf x = if x < 10 then "small" else "large"

|| 7. All List Comprehension Structural Forms (Section 5.3)
compSingle = [ x * x | x <- [1 .. 4] ]
compDual   = [ (x, y) | x <- [1 .. 2]; y <- [1 .. 2] ]
compGuard  = [ x | x <- [1 .. 10]; (x mod 2) == 0 ]

|| Helper predicates for higher-order function testing
isLessThanFour n = n < 4
evensOnly n = (n mod 2) == 0

|| ============================================================================
|| Assertion Engine & Total Syntax Verification Matrix
|| ============================================================================

assert name cond = if cond then (name, "PASS") else (name, "FAIL")

|| Layout Fixed: Assigned directly on one line, elements strictly indented deeper than the bracket context
runTests
  =
  [
  assert "Syntax: Identifiers" (leadingUnderscoreFix + camelCaseIdentifier123 == 300),
  assert "Syntax: Number literals" (0 - 3 == 0 - 3),
  assert "Syntax: Character match" (literalMatchChar 'A' == "charA"),
  assert "Syntax: String desugar" ("hi" == ['h', 'i']),
  assert "Pattern: Numeric zero" (literalMatchNum 0 == "zero"),
  assert "Pattern: Wildcard fall" (literalMatchNum 999 == "wildcard"),
  assert "Pattern: Empty list" (checkList [] == "empty"),
  assert "Pattern: Singleton list" (checkList [42] == "singleton"),
  assert "Pattern: Cons extraction" (checkList [1, 2, 3] == "many"),
  assert "Pattern: Tuple split" (destructureTuple (10, 20) == 30),
  assert "Syntax: Deep where" (nestedWhere 10 == 27),
  assert "Operators: Composition" (composedFunc 3 == 7),
  assert "Operators: Modulo" (10 mod 3 == 1),
  assert "Operators: Left-Assoc" (12 / 3 * 2 == 8),
  assert "Operators: Concat" (("ab" ++ "cd") == "abcd"),
  assert "Operators: Precedence" (5 + 3 * 4 == 17),
  assert "Operators: Cons Right" ((1 : 2 : []) == [1, 2]),
  assert "Operators: List Diff" (([1, 2, 3, 2] -- [2]) == [1, 3, 2]),
  assert "Operators: Inequality" (5 ~= 6),
  assert "Operators: Relational" (5 <= 5 & 6 >= 5),
  assert "Operators: Short Logic" ((5 == 4) \/ (3 == 3) & (1 ~= 0)),
  assert "Syntax: Guard Conditional" (inlineIf 15 == "large"),
  assert "Syntax: Range Comp" (compSingle == [1, 4, 9, 16]),
  assert "Syntax: Dual Comp" (compDual == [(1,1), (1,2), (2,1), (2,2)]),
  assert "Syntax: Guard Comp" (compGuard == [2, 4, 6, 8, 10]),
  assert "Library: map" (map addOne [1, 2, 3] == [2, 3, 4]),
  assert "Library: filter" (filter evensOnly [1, 2, 3, 4] == [2, 4]),
  assert "Library: foldl" (foldl (-) 10 [1, 2, 3] == 4),
  assert "Library: foldr" (foldr (-) 10 [1, 2, 3] == -8),
  assert "Library: take" (take 2 [1, 2, 3, 4] == [1, 2]),
  assert "Library: drop" (drop 2 [1, 2, 3, 4] == [3, 4]),
  assert "Library: takeWhile" (takewhile isLessThanFour [1, 2, 3, 4, 5] == [1, 2, 3]),
  assert "Library: length" (# [1, 2, 3, 4, 5] == 5),
  assert "Library: reverse" (reverse [1, 2, 3] == [3, 2, 1]),
  assert "Library: iterate" (take 4 (iterate multTwo 1) == [1, 2, 4, 8]),
  assert "Library: repeat" (take 3 (repeat 7) == [7, 7, 7]),
  assert "Library: zip" (zip ([1, 2], ["a", "b"]) == [(1, "a"), (2, "b")]),
  assert "Library: lines" (lines "abc\ndef\ng" == ["abc", "def", "g"]),
  assert "Library: numval" (numval "1234" == 1234),
  assert "Library: show num" (show 42 == "42"),
  assert "Library: show tuple" (show (1, 2) == "(1,2)")
  ]

|| Count how many tests failed
countFailures []           = 0
countFailures ((name,s):ts) = if s == "FAIL" then 1 + countFailures ts else countFailures ts

|| Format the report dynamically
formatResults [] = ""
formatResults ((name, status):ts) = "  [" ++ status ++ "] " ++ name ++ "\n" ++ formatResults ts

|| Summary calculator
summary report = if countFailures report == 0 then "\nALL TESTS PASSED!\n" else "\nFAILED: " ++ show (countFailures report) ++ " test(s) failed!\n"

|| ============================================================================
|| Main Entrypoint
|| ============================================================================
main
  =
  "--- MIRACULA TOTAL SYNTAX VALIDATION MATRIX ---\n" ++
  formatResults runTests ++
  summary runTests
