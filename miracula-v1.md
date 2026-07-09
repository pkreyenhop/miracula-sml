# Miracula v1: Technical Specification

This document provides a complete technical specification for **Miracula** (a lazy Miranda-like functional language interpreter). It is designed to contain sufficient detail to allow complete re-implementation of the language, parser, desugarer, runtime, and REPL in another programming language (e.g., Rust, Go, Haskell, or C++).

---

## 1. Abstract Syntax Tree (AST) & Environment

The interpreter operates on tree-based expressions (`node`), structural patterns (`parsed_pattern`), and list-comprehension qualifiers (`qualifier`).

### 1.1 Datatypes

#### AST Nodes (`node`)
*   **`Int(int)`**: Integer literal.
*   **`Char(char)`**: Character literal.
*   **`Var(string)`**: Variable reference (identifier).
*   **`Lam(string, node)`**: Lambda abstraction (`\x. body`).
*   **`Closure(string, node, env)`**: Lexical closure capturing its environment at creation.
*   **`App(node, node)`**: Function application (`e1 e2`).
*   **`Add(node, node)`**, **`Sub(node, node)`**, **`Mul(node, node)`**, **`Mod(node, node)`**: Integer arithmetic operations.
*   **`Eq(node, node)`**, **`Ne(node, node)`**, **`Lt(node, node)`**, **`Gt(node, node)`**, **`Le(node, node)`**, **`Ge(node, node)`**: Comparison operations.
*   **`IfZero(cond, then_branch, else_branch)`**: Branching condition: executes `then_branch` if `cond` is `0`, else `else_branch`.
*   **`If(cond, then_branch, else_branch)`**: Boolean branch: executes `then_branch` if `cond` is non-zero, else `else_branch`.
*   **`IfNil(cond, then_branch, else_branch)`**: List check: executes `then_branch` if `cond` evaluates to `Nil`, else `else_branch`.
*   **`Cons(head, tail)`**: List cell construction.
*   **`Nil`**: Empty list constructor (`[]`).
*   **`Range(start, end)`**: Lazy sequence range (`[start..end]`).
*   **`Append(list1, list2)`**: List concatenation (operator `++`).
*   **`Tuple(list of node)`**: Tuple literal `(e1, e2, ..., eN)`.
*   **`Proj(index, tuple_expr)`**: Tuple projection (0-indexed extraction of element `index` from a tuple).
*   **`ZF(body, qualifiers)`**: Unevaluated list comprehension (`[body | qualifiers]`).
*   **`ZFGenerator(pattern, qualifiers, current_list, body, env)`**: Internal runtime state for generating lazy list comprehension elements.
*   **`Thunk(reference to thunk_state)`**: Call-by-need memoized wrapper for delayed expression evaluation.
*   **`MatchError`**: Special marker indicating pattern-matching failure (triggers a runtime error when evaluated).

#### Thunk State (`thunk_state`)
A thunk wraps expressions to implement lazy evaluation. It is mutable (e.g., using references, pointers, or atomics) and exists in one of three states:
1.  **`Unevaluated(node, env)`**: Stores the original AST node and the lexical environment in which it was defined.
2.  **`Evaluating`**: Indicates that evaluation of the thunk is currently in progress. Used to detect infinite loops / cycles (the `Blackhole` exception).
3.  **`Evaluated(node)`**: Stores the computed Weak Head Normal Form (WHNF) result of the thunk to avoid re-computation.

#### Patterns (`parsed_pattern`)
Patterns are used in equation left-hand sides and list-comprehension generators:
*   **`PatInt(int)`**: Exact integer match.
*   **`PatChar(char)`**: Exact character match.
*   **`PatVar(string)`**: Variable binding. The variable name `"_"` acts as a wildcard (matches anything without binding).
*   **`PatNil`**: Matches empty list `[]`.
*   **`PatCons(head_pattern, tail_pattern)`**: Matches non-empty list `h:t`.
*   **`PatTuple(list of parsed_pattern)`**: Matches a tuple of patterns.

#### Qualifiers (`qualifier`)
Used in ZF list comprehensions:
*   **`Generator(parsed_pattern, source_expr)`**: Matches elements from `source_expr` list against the pattern (e.g., `x <- list`).
*   **`Filter(cond_expr)`**: A boolean expression filtering out elements if it evaluates to `0` (false).

### 1.2 Evaluation Environment (`env`)
An environment is a mapping from variable names (`string`) to AST `node`s. It must support lookup, insertion (extension), and folding.

---

## 2. Lexical Analysis (Lexer)

The lexer converts raw source code into a stream of tokens, skipping whitespace. 

### 2.1 Tokens
The language supports the following token types:

| Token Type | Representation in Source | Description |
| :--- | :--- | :--- |
| `TOK_LAMBDA` | `\` | Lambda abstraction symbol |
| `TOK_DOT` | `.` | Lambda body separator |
| `TOK_DOTDOT` | `..` | List range generator separator |
| `TOK_ARROW` | `->` | Type or case arrow (reserved for syntax) |
| `TOK_ASSIGN` | `=` | Variable / function assignment |
| `TOK_LPAREN` | `(` | Left parenthesis |
| `TOK_RPAREN` | `)` | Right parenthesis |
| `TOK_LBRACK` | `[` | Left square bracket |
| `TOK_RBRACK` | `]` | Right square bracket |
| `TOK_COMMA` | `,` | Separator |
| `TOK_COLON` | `:` | List cons operator |
| `TOK_SUB` | `-` | Subtraction |
| `TOK_ADD` | `+` | Addition |
| `TOK_MUL` | `*` | Multiplication |
| `TOK_IFZERO` | `ifzero` | Conditional keyword (checks for 0) |
| `TOK_IF` | `if` | Conditional keyword (checks for boolean/int) |
| `TOK_THEN` | `then` | Condition branch keyword |
| `TOK_ELSE` | `else` | Condition else-branch keyword |
| `TOK_MOD` | `mod` | Modulo keyword |
| `TOK_PIPE` | `\|` | ZF comprehension qualifier separator |
| `TOK_LARROW` | `<-` | ZF generator binding operator |
| `TOK_SEMICOLON`| `;` | ZF qualifier list separator |
| `TOK_EQ` | `==` | Equality test |
| `TOK_NE` | `!=` | Inequality test |
| `TOK_LT` | `<` | Less than |
| `TOK_GT` | `>` | Greater than |
| `TOK_LE` | `<=` | Less than or equal |
| `TOK_GE` | `>=` | Greater than or equal |
| `TOK_PP` | `++` | List append operator |
| `TOK_INT` | Digits (e.g. `42`) | Integer value |
| `TOK_VAR` | Identifier | Variable name or keyword |
| `TOK_CHAR` | `'c'` | Character literal (supports escapes) |
| `TOK_STRING` | `"str"` | String literal (desugars to list of characters) |
| `TOK_EOF` | Input End | End of file token |

### 2.2 Lexing Rules
1.  **Whitespace**: Skip spaces, tabs, and newlines.
2.  **Comments**: The lexer does not directly process comments. Comments are handled by the script preprocessor. Any line in a script starting with `||` is treated as a comment and skipped entirely.
3.  **Identifiers (`TOK_VAR`)**: A sequence starting with an alphabetical character or underscore `_`, followed by zero or more alphanumeric characters or `_`. If the sequence matches a keyword (`ifzero`, `if`, `then`, `else`, `mod`), it is lexed as that keyword token instead of `TOK_VAR`.
4.  **Integers (`TOK_INT`)**: Consecutive sequences of digits.
5.  **Character Literals (`TOK_CHAR`)**: Enclosed in single quotes (e.g., `'a'`). 
    *   Supports single escape characters starting with a backslash: `'\n'` (newline), `'\t'` (tab), `'\''` (single quote), and `'\\'` (backslash).
6.  **String Literals (`TOK_STRING`)**: Enclosed in double quotes (e.g., `"hello"`).
    *   Supports the same escape characters as character literals, plus `\"` (double quote).
    *   *Desugaring*: At parse time, a string literal is converted directly into a linked list of `Char` nodes ending in `Nil`. For example, `"hi"` becomes `Cons(Char('h'), Cons(Char('i'), Nil))`.

---

## 3. Grammar & Parsing

The parser processes tokens using recursive descent. It distinguishes between statement bindings (assignments) and expression evaluations.

### 3.1 Operator Precedence and Associativity

The table below lists operators from lowest to highest precedence:

| Operator / Construct | Associativity | Description |
| :--- | :--- | :--- |
| `\x. expr` | Right | Lambda Abstraction |
| `if`, `ifzero` | Right | Conditionals |
| `:` | Right | List Cons |
| `++` | Right | List Append |
| `==`, `!=`, `<`, `>`, `<=` , `>=` | Non-associative | Comparisons |
| `+`, `-` | Left | Addition, Subtraction |
| `*`, `mod` | Non-associative | Multiplication, Modulo |
| *Space* (implicit) | Left | Function Application |
| Atoms | N/A | Variables, Literals, Grouping `()`, Lists `[]` |

### 3.2 Parsing Grammar Rules

*   **`parse_expr`**:
    *   If `TOK_LAMBDA`, consume variable, expect `TOK_DOT`, and return `Lam(var, parse_expr())`.
    *   If `TOK_IFZERO`, consume condition `parse_expr()`, expect `TOK_THEN`, parse `then_expr = parse_expr()`, expect `TOK_ELSE`, parse `else_expr = parse_expr()`, and return `IfZero(cond, then_expr, else_expr)`.
    *   If `TOK_IF`, consume condition, expect `TOK_THEN`, parse `then_expr = parse_expr()`, expect `TOK_ELSE`, parse `else_expr = parse_expr()`, and return `If(cond, then_expr, else_expr)`.
    *   Otherwise, delegate to `parse_cons()`.

*   **`parse_cons`**:
    *   Parse `parse_pp()`. If the next token is `TOK_COLON`, consume it and return `Cons(left, parse_cons())`.

*   **`parse_pp`**:
    *   Parse `parse_comp()`. If the next token is `TOK_PP`, consume it and return `Append(left, parse_pp())`.

*   **`parse_comp`**:
    *   Parse `parse_add_sub()`. If followed by a comparison token (e.g. `==`, `<=`), consume it and return the corresponding operator node (e.g. `Eq(left, parse_add_sub())`).

*   **`parse_add_sub`**:
    *   Parse `parse_mod()`. Loop while the next token is `TOK_ADD` or `TOK_SUB`, accumulating left-leaning nodes: `Add(left, parse_mod())` or `Sub(left, parse_mod())`.

*   **`parse_mod`**:
    *   Parse `parse_app()`. If the next token is `TOK_MOD` or `TOK_MUL`, consume it and return `Mod(left, parse_app())` or `Mul(left, parse_app())`.

*   **`parse_app`**:
    *   Parse `parse_atom()`. While the next token is a valid atom start token (`TOK_INT`, `TOK_CHAR`, `TOK_STRING`, `TOK_VAR`, `TOK_LPAREN`, `TOK_LBRACK`), consume it and wrap application: `App(left, parse_atom())`.

*   **`parse_atom`**:
    *   `TOK_INT`: Return `Int(val)`.
    *   `TOK_CHAR`: Return `Char(val)`.
    *   `TOK_STRING`: Return desugared `Cons` chain ending in `Nil`.
    *   `TOK_VAR`: Return `Var(name)`.
    *   `TOK_LPAREN`: Operator sectioning and tuples.
        *   **Operator Sections**: 
            *   `( : )` desugars to `\x. \y. x : y` (`Lam("x", Lam("y", Cons(Var("x"), Var("y"))))`)
            *   `( : e )` desugars to `\x. x : e` (`Lam("x", Cons(Var("x"), e))`)
            *   `( + )` desugars to `\x. \y. x + y`
            *   `( + e )` desugars to `\x. x + e`
            *   `( - )` desugars to `\x. \y. x - y`
            *   `( - e )` desugars to `\x. x - e`
        *   **Tuples / Parentheses**:
            *   If not an operator section, parse `first_expr = parse_expr()`.
            *   If followed by `,`, parse subsequent expressions separated by `,` until `)` is reached, and return `Tuple([first_expr, ..., last_expr])`.
            *   If followed by `)`, consume it and return `first_expr` (simple grouping).
    *   `TOK_LBRACK`: Parses list constructs. Delegate to `parse_list_elements()`.

*   **`parse_list_elements`**:
    *   If next is `TOK_RBRACK`, return `Nil`.
    *   Else, parse `head = parse_expr()`.
    *   **ZF List Comprehension**: If followed by `|`, consume it. Parse a list of qualifiers separated by `;` until `]` is reached. A qualifier is a generator `pat <- expr` if there is a `<-` token before the next `;` or `]`, otherwise it is a filter expression `expr`. Return `ZF(head, qualifiers)`.
    *   **List Range**: If followed by `..`, consume it, parse `tail = parse_expr()`, expect `]`, and return `Range(head, tail)`.
    *   **List Literal**: If followed by `,`, consume it, and return `Cons(head, parse_list_elements())`. If followed by `]`, consume it and return `Cons(head, Nil)`.

### 3.3 Pattern Parsing

Patterns are parsed on the left-hand side of assignments or in generator expressions:
*   `TOK_INT`: Return `PatInt(val)`.
*   `TOK_CHAR`: Return `PatChar(val)`.
*   `TOK_VAR`: Return `PatVar(name)`.
*   `TOK_LBRACK`: Must be immediately followed by `TOK_RBRACK`. Returns `PatNil`. *(Note: only the empty list pattern is supported directly).*
*   `TOK_LPAREN`: Parses `parse_pattern_cons()`. If followed by `,`, parses multiple patterns separated by `,` until `)` is reached, returning `PatTuple([p1, ..., pN])`. Otherwise, expects `)` and returns the parenthesized pattern.
*   **Cons Pattern**: `parse_pattern_cons()` parses a pattern, and if followed by `:`, returns `PatCons(left, parse_pattern_cons())`.

### 3.4 Assignments vs. Evaluations
If a line of tokens contains the assignment token `=` outside of brackets/parentheses, parse it as a binding:
*   Expect `TOK_VAR name` at the beginning.
*   Parse zero or more patterns (parameters) until `=` is reached.
*   Parse the body expression.
*   Produce a binding representation: `ScriptBind(name, pattern_list, body)`.
If no `=` is present, parse the line as an expression evaluation: `REPLEval(body)`.

---

## 4. Pattern Matching Desugaring

Function equations are defined with multiple equations, each containing zero or more patterns:
```miranda
fib 0 = 0
fib 1 = 1
fib n = fib (n-1) + fib (n-2)
```

The desugaring phase compiles these equations into a single nested lambda expression containing conditional decision trees.

### 4.1 Desugaring Algorithm

Given a list of equations:
`eqs = [ { fname, pats: [pat_1, ..., pat_k], body }, ... ]`

1.  **Arity Validation**: Ensure all equations for `fname` have the same number of patterns $k$. Let this arity be $k$.
2.  **Special Cases**:
    *   If there is 1 equation and $k = 0$: Return `body`.
    *   If there is 1 equation and $k = 1$ with a variable pattern `PatVar x`: Return `Lam(x, body)`.
3.  **General Case (Decision Tree Compilation)**:
    *   Generate $k$ unique parameter names: `p0, p1, ..., p_k-1`.
    *   Define a recursive decision tree builder `build_decision_tree(eq_list)`:
        *   If `eq_list` is empty, return `MatchError`.
        *   Otherwise, select the first equation `{ pats: [pat_0, ..., pat_k-1], body }` and compile matches against the parameter names `p0, ..., p_k-1`:
            *   We process patterns from left to right using a helper: `check_pats(param_vars, pat_list, eq_body)`:
                *   If `param_vars` is empty: Return `eq_body`.
                *   Pop the first parameter variable `p` and pattern `pat`.
                *   Depending on the type of `pat`:
                    *   **`PatInt n`**:
                        ```
                        IfZero(Sub(Var(p), Int(n)), 
                               check_pats(rest_vars, rest_pats, eq_body), 
                               build_decision_tree(rest_equations))
                        ```
                    *   **`PatChar c`**:
                        ```
                        IfZero(Sub(Eq(Var(p), Char(c)), Int(1)), 
                               check_pats(rest_vars, rest_pats, eq_body), 
                               build_decision_tree(rest_equations))
                        ```
                    *   **`PatVar name`**:
                        If `name == p`, return `check_pats(rest_vars, rest_pats, eq_body)`.
                        Else, return `App(Lam(name, check_pats(rest_vars, rest_pats, eq_body)), Var(p))`.
                    *   **`PatNil`**:
                        ```
                        IfNil(Var(p), 
                              check_pats(rest_vars, rest_pats, eq_body), 
                              build_decision_tree(rest_equations))
                        ```
                    *   **`PatCons(hp, tp)`**:
                        Generate two fresh variables: `h_var` and `t_var`.
                        Let `failure_branch = build_decision_tree(rest_equations)`.
                        Let `success_branch = check_pats([h_var, t_var] + rest_vars, [hp, tp] + rest_pats, eq_body)`.
                        Return:
                        ```
                        IfNil(Var(p),
                              failure_branch,
                              App(Lam(h_var, 
                                      App(Lam(t_var, success_branch), 
                                          App(Var("tl"), Var(p)))),
                                  App(Var("hd"), Var(p))))
                        ```
                    *   **`PatTuple([sp1, ..., spM])`**:
                        Generate $M$ fresh variables: `t0, ..., t_M-1`.
                        Let `success_branch = check_pats([t0, ..., t_M-1] + rest_vars, [sp1, ..., spM] + rest_pats, eq_body)`.
                        Wrap the success branch with projection bindings:
                        ```
                        wrap_projs(vars, idx):
                            if vars is empty: return success_branch
                            return App(Lam(vars[0], wrap_projs(vars[1:], idx + 1)), Proj(idx, Var(p)))
                        
                        Return wrap_projs([t0, ..., t_M-1], 0)
                        ```
4.  **Wrap in Parameters**: The resulting decision tree is wrapped in outer lambda abstractions for the parameters:
    `Lam(p0, Lam(p1, ... Lam(p_k-1, decision_tree)...))`

---

## 5. Lazy Evaluation & Operational Semantics

Miracula uses Call-by-Need lazy evaluation. Expressions are not evaluated until their values are required. Evaluation resolves nodes to **Weak Head Normal Form (WHNF)**.

### 5.1 Weak Head Normal Form (WHNF)
An AST node is in WHNF if it is:
*   An integer (`Int`), character (`Char`), empty list (`Nil`), or MatchError.
*   A lambda abstraction (`Lam`) or closure (`Closure`).
*   A constructor node (`Cons` or `Tuple`) where the sub-expressions themselves are either already values or wrapped in thunks.

### 5.2 Lazy Constructor Wrapper (`needs_thunk`)
When constructing a `Cons(h, t)` or `Tuple(elms)` node, sub-expressions that are not already values/thunks must be lazily deferred.
*   **Do NOT wrap**: `Int`, `Char`, `Nil`, `Thunk`, `Closure`, `Lam`, `Cons`, `Tuple`, or `MatchError`.
*   **DO wrap**: Any other node type. Wrap it as: `Thunk(reference to Unevaluated(expr, current_env))`.

---

### 5.3 WHNF Evaluation Rules (`whnf(env, node)`)

To evaluate a node to WHNF in an environment `env`:

1.  **`Int n`**, **`Char c`**, **`Lam(x, body)`**, **`Closure(x, body, c_env)`**, **`Nil`**:
    *   Return unchanged.

2.  **`Cons(h, t)`**:
    *   Apply `needs_thunk` to `h` and `t` (wrapping them in thunks if required) and return `Cons(h', t')`.

3.  **`Tuple(elms)`**:
    *   Apply `needs_thunk` to each element in `elms` and return `Tuple(elms')`.

4.  **`Var x`**:
    *   If `x == "hd"` or `x == "tl"`, return `Var x` (treated as a primitive functional value).
    *   Otherwise, lookup `x` in `env`.
        *   If not found: Raise `RuntimeError: Unbound variable: x`.
        *   If found:
            *   If it is a `Thunk(ref)`:
                *   If state is `Evaluated(res)`: Return `res`.
                *   If state is `Evaluating`: Raise `Blackhole: Infinite loop on identifier: x`.
                *   If state is `Unevaluated(expr, saved_env)`:
                    1.  Set state to `Evaluating`.
                    2.  Compute `res = whnf(saved_env, expr)`.
                    3.  Set state to `Evaluated(res)`.
                    4.  Return `res`.
            *   If it is any other node `explicit_node`: Return `whnf(env, explicit_node)`.

5.  **`Thunk(ref)`**:
    *   Perform the exact same evaluation and state update logic as described for `Var` thunk lookups.

6.  **`App(e1, e2)`**:
    *   Evaluate `e1` to WHNF: `f = whnf(env, e1)`.
    *   **Case `f == Var "hd"`**:
        *   Evaluate `e2` to WHNF. If it is `Cons(h, _)`, return `whnf(env, h)`.
        *   If `Nil`: Raise `RuntimeError: hd applied to empty list`.
        *   Else: Raise `RuntimeError: hd expects a list`.
    *   **Case `f == Var "tl"`**:
        *   Evaluate `e2` to WHNF. If it is `Cons(_, t)`, return `whnf(env, t)`.
        *   If `Nil`: Raise `RuntimeError: tl applied to empty list`.
        *   Else: Raise `RuntimeError: tl expects a list`.
    *   **Case `f == Closure(x, body, closure_env)`**:
        *   Create a thunk for the argument: `t = Thunk(ref Unevaluated(e2, env))`.
        *   Extend `closure_env` with `{x -> t}`.
        *   Return `whnf(extended_env, body)`.
    *   **Case `f == Lam(x, body)`**:
        *   Create a thunk for the argument: `t = Thunk(ref Unevaluated(e2, env))`.
        *   Extend the current `env` with `{x -> t}`.
        *   Return `whnf(extended_env, body)`.
    *   **Otherwise**: Raise `RuntimeError: Non-functional application`.

7.  **`Add(e1, e2)`**, **`Sub(e1, e2)`**, **`Mul(e1, e2)`**, **`Mod(e1, e2)`**:
    *   Evaluate `e1` to WHNF and `e2` to WHNF.
    *   Both must resolve to `Int(n1)` and `Int(n2)`.
    *   Return `Int(n1 + n2)`, `Int(n1 - n2)`, `Int(n1 * n2)`, or `Int(n1 mod n2)` respectively.
    *   Else: Raise `RuntimeError`.

8.  **`Eq(e1, e2)`**, **`Ne(e1, e2)`**, **`Lt(e1, e2)`**, **`Gt(e1, e2)`**, **`Le(e1, e2)`**, **`Ge(e1, e2)`**:
    *   Evaluate `e1` to WHNF and `e2` to WHNF.
    *   If both are `Int(n1)` and `Int(n2)`, evaluate comparison and return `Int(1)` if true, else `Int(0)`.
    *   If both are `Char(c1)` and `Char(c2)` (supported only for `Eq`), return `Int(1)` if `c1 == c2` else `Int(0)`.
    *   Else: Raise `RuntimeError`.

9.  **`IfZero(cond, t_branch, f_branch)`**:
    *   Evaluate `cond` to WHNF. Must be `Int(val)`.
    *   If `val == 0`, return `whnf(env, t_branch)`.
    *   Else, return `whnf(env, f_branch)`.

10. **`If(cond, t_branch, f_branch)`**:
    *   Evaluate `cond` to WHNF. Must be `Int(val)`.
    *   If `val != 0` (true), return `whnf(env, t_branch)`.
    *   Else, return `whnf(env, f_branch)`.

11. **`IfNil(cond, t_branch, f_branch)`**:
    *   Evaluate `cond` to WHNF.
    *   If `Nil`, return `whnf(env, t_branch)`.
    *   If `Cons(_, _)`, return `whnf(env, f_branch)`.
    *   Else: Raise `RuntimeError: Condition must resolve to a list`.

12. **`Append(e1, e2)`**:
    *   Evaluate `e1` to WHNF.
    *   If `Nil`, return `whnf(env, e2)`.
    *   If `Cons(h, t)`:
        *   Create lazy append thunk for the tail: `t' = Thunk(ref Unevaluated(Append(t, e2), env))`.
        *   Return `Cons(h, t')`.
    *   Else: Raise `RuntimeError: Append expects lists`.

13. **`Range(e1, e2)`**:
    *   Evaluate `e1` to WHNF and `e2` to WHNF. Must resolve to `Int(n1)` and `Int(n2)`.
    *   If `n1 > n2`, return `Nil`.
    *   Else:
        *   Create lazy range generator thunk for the remaining range:
            `next_range = Thunk(ref Unevaluated(Range(Int(n1 + 1), e2), env))`.
        *   Return `Cons(Int(n1), next_range)`.

14. **`Proj(index, tuple_expr)`**:
    *   Evaluate `tuple_expr` to WHNF. Must be `Tuple(elms)`.
    *   Return `whnf(env, elms[index])`.

15. **`MatchError`**:
    *   Raise `RuntimeError: Pattern matching exhausted`.

---

### 5.4 List Comprehension Evaluation (ZF Expressions)

List comprehensions of the form `[body_expr | qualifiers]` compile into lazy generator chains.

#### Compilation and Evaluation Rules

1.  **Comprehension Entry**: `whnf(env, ZF(body, qualifiers))` delegates to `eval_zf(env, body, qualifiers)` and evaluates the resulting expression to WHNF.
2.  **`eval_zf(env, body, qualifiers)`**:
    *   **Base Case (`qualifiers` is empty `[]`)**:
        *   Wrap `body` in a thunk if `needs_thunk(body)` is true: `h = Thunk(ref Unevaluated(body, env))` else `body`.
        *   Return `Cons(h, Nil)`. (Wraps the yielded result in a single-element list).
    *   **Filter Case (`Filter(cond) :: rest`)**:
        *   Create cond thunk: `cond_thunk = Thunk(ref Unevaluated(cond, env))`.
        *   Return `If(cond_thunk, eval_zf(env, body, rest), Nil)`.
    *   **Generator Case (`Generator(pat, src_expr) :: rest`)**:
        *   Return `ZFGenerator(pat, rest, src_expr, body, env)`.

3.  **`ZFGenerator(pat, rest, current_list, body, zf_env)` Evaluation**:
    *   Evaluate `current_list` to WHNF in environment `zf_env`.
    *   **If `Nil`**: Return `Nil`.
    *   **If `Cons(h, t)`**:
        1.  Attempt pattern match: `match_res = match_pattern(zf_env, pat, h)`.
        2.  Create next generator step thunk: `next_gen = ZFGenerator(pat, rest, t, body, zf_env)`.
        3.  If match succeeds (`SOME(bindings)`):
            *   Extend `zf_env` with the bindings.
            *   Compute first list branch: `first_list = eval_zf(extended_env, body, rest)`.
            *   Return `whnf(current_env, Append(first_list, next_gen))`.
        4.  If match fails (`NONE`):
            *   Skip element and return `whnf(current_env, next_gen)`.
    *   **Otherwise**: Raise `RuntimeError: Generator source must be a list`.

#### Pattern Matching Logic (`match_pattern(env, pat, node)`)
To match pattern `pat` against `node` in environment `env`:
*   Evaluate `node` to WHNF first: `v = whnf(env, node)`.
*   **`(PatInt(n1), Int(n2))`**: If `n1 == n2` return success with empty bindings.
*   **`(PatChar(c1), Char(c2))`**: If `c1 == c2` return success with empty bindings.
*   **`(PatVar "_", _)`**: Wildcard pattern. Return success with empty bindings.
*   **`(PatVar x, v)`**: Bind identifier `x` to evaluated node `v`. Return success with binding `{x -> v}`.
*   **`(PatNil, Nil)`**: Return success with empty bindings.
*   **`(PatCons(p1, p2), Cons(h, t))`**:
    *   Recursively match `match_pattern(env, p1, h)` and `match_pattern(env, p2, t)`.
    *   If both succeed, return the union of their bindings. If duplicate variable bindings exist, the rightmost binding takes precedence.
*   **`(PatTuple(pats), Tuple(nodes))`**:
    *   If `length(pats) != length(nodes)`, return failure.
    *   Recursively match each pattern against its corresponding node. If all succeed, return the union of all bindings.
*   **Any other case**: Return failure.

---

## 6. Standard Library & Loading Rules

### 6.1 Program Setup & File Loading
Upon startup, the interpreter initializes an empty environment `env = {}`.
1.  **Standard Library**: Looks for `stdenv.m` in the current working directory. If found, reads it line-by-line. Empty lines and lines starting with `||` are skipped. All bindings are parsed, grouped by function name, desugared, and inserted into `env`.
2.  **Script File**: Looks for `script.m` in the current working directory. If found, reads and loads it in the same manner, extending the environment loaded from `stdenv.m`.

### 6.2 Standard Library Functions (`stdenv.m`)
The standard library `stdenv.m` defines basic combinators and list functions:
```miranda
|| string == [char]

foldl f z []     = z
foldl f z (x:xs) = foldl f (f z x) xs

converse f a b = f b a

reverse = foldl (converse(:)) []

sum = foldl (+) 0

map f x = [f a | a<-x]
```

---

## 7. Interactive REPL Specifications

The REPL loop displays a prompt `miranda> ` and reads inputs. It operates in two modes:

### 7.1 Input Modes
1.  **Interactive TTY Mode**: Automatically detected by running `test -t 0` (or checking if standard input is a terminal device).
    *   Puts the terminal in raw mode: `stty raw -echo` during input reading.
    *   Restores the terminal: `stty -raw echo` before executing evaluations or on interruption.
2.  **Piped/Script Mode**: Used when input is piped into the binary. Falls back to standard line reading.

### 7.2 Custom Line Editor Keybindings (TTY Mode Only)
The interactive line editor supports basic text navigation and editing:

*   **Left Arrow**: Moves the cursor left by 1 character.
*   **Right Arrow**: Moves the cursor right by 1 character.
*   **Backspace**: Deletes the character to the left of the cursor.
*   **Delete**: Deletes the character under the cursor.
*   **Ctrl-A** / **Home**: Moves the cursor to the beginning of the line.
*   **Ctrl-E** / **End**: Moves the cursor to the end of the line.
*   **Ctrl-K**: Kills all characters to the right of the cursor.
*   **Ctrl-L**: Clears the terminal screen (`\027[2J\027[H`) and redraws the current line.
*   **Ctrl-C**: Discards the current line and starts a new prompt.
*   **Ctrl-D**: If the line is empty, exits the REPL.
*   **Up Arrow**: Recalls the previous line in input history. Saves the current un-submitted text as a "draft line".
*   **Down Arrow**: Recalls the next line in input history. Restores the "draft line" when returning to the bottom.

### 7.3 REPL Commands
*   **/q** or **quit** or **exit**: Exits the REPL.
*   **/e**: 
    1.  Temporarily exits raw TTY mode.
    2.  Spawns `vi script.m` via system command.
    3.  On editor exit, re-initializes the environment from scratch, reloading `stdenv.m` and `script.m`, and restarts the REPL.
*   **Variable / Function Definitions**: If the input line contains an assignment `=`, desugars the equation(s) and adds the resulting binding to the global environment. Outputs: `Defined variable: <name>`.
*   **Expressions**: If the input is an expression:
    1.  Records start time.
    2.  Evaluates the expression to WHNF using `whnf()`.
    3.  Prints the result string.
    4.  Prints elapsed execution duration: `Evaluation time: <time> ms`.

### 7.4 Value Printing Semantics
To print an evaluated WHNF node:
*   **`Int n`**: Print string representation of `n`.
*   **`Char c`**: Print `'c'` (escaped).
*   **`Tuple elms`**: Evaluate all elements in `elms` to WHNF, print their representations separated by commas inside parentheses: `(x1, x2, ..., xN)`.
*   **`Nil`**: Print `[]`.
*   **`Cons(h, t)`**:
    *   Check if the list is a valid character list (string):
        *   Traverse the list. If it terminates in `Nil` and contains only `Char` nodes, print it as a double-quoted string with appropriate character escapes (e.g. `"hello\n"`).
        *   Otherwise, traverse the list, printing the WHNF representation of each element separated by commas inside square brackets: `[1,2,3]`. Handles improper lists (where the tail is not `Nil`) by printing the tail representation as the final element (e.g., `[1,2,rest]`).
*   **`Closure`** / **`Lam`**: Print `\x. <closure>`.
*   **Other nodes**: Print structural placeholders (e.g., `<conditional>`, `<append>`, `<zf-comprehension>`).

---

## 8. Step-by-Step Implementation Verification Checklist

1.  **Lexer**: Verify that `"hello"` is lexed as a single `TOK_STRING` containing `hello`, and that `[1..100]` is lexed as `[`, `1`, `..`, `100`, `]`.
2.  **Parser**: Verify that `1 + 2 * 3` parses as `Add(1, Mul(2, 3))`. Verify that sections like `( + 5 )` parse as `Lam("x", Add(Var("x"), 5))`.
3.  **Desugarer**: Verify that:
    ```
    f 0 = 10
    f n = 20
    ```
    compiles into:
    ```
    Lam("p0", IfZero(Sub(Var("p0"), Int(0)), Int(10), App(Lam("n", Int(20)), Var("p0"))))
    ```
4.  **Runtime**: Test `hd (tl [1, 2, 3])` to verify list indexing and lazy evaluation.
5.  **Comprehensions**: Test `[x + 1 | x <- [1..5]; x != 3]` to verify generators and filters.
6.  **Cycle Detection**: Test `x = x` to verify that evaluating `x` triggers a `Blackhole` error.
