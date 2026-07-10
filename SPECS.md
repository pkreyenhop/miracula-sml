# Miracula: Formal Language Specification

This document provides the formal specification of the Miracula language—a lazy, dynamically-typed functional programming language inspired by Miranda.

---

## 1. Concrete & Abstract Syntax (The Grammar)

### 1.1 Lexical Grammar

#### Identifiers & Keywords
- **Variables**: Identifiers starting with a lowercase letter or an underscore, followed by alphanumeric characters or underscores:
  `[a-z_][a-zA-Z0-9_]*`
- **Keywords**: `where`, `if`, `then`, `else`, `otherwise`, `mod`

#### Literals
- **Integers**: Sequence of digits: `[0-9]+`
- **Characters**: Single character enclosed in single quotes: `'c'`
- **Strings**: Sequence of characters and escape sequences enclosed in double quotes: `"..."`. Desugared at parse-time to a lazy list of `Char` nodes.

#### Whitespace & Layout Rules (Off-side Rule)
Miracula employs indentation-based blocking. The layout preprocessor (`apply_layout`) translates indentation into explicit block structure tokens:
- **Block Opening (`{`)**: Inserted when the indentation level of a new line increases relative to the current block stack.
- **Statement Separator (`;`)**: Inserted when a new line starts at the same indentation level.
- **Block Closing (`}`)**: Inserted when the indentation level decreases, popping layout columns from the layout stack until a matching indentation level is found.
- **Comments**: Any text from `||` to the end of the line is a comment and is ignored by the tokenizer. Blank lines and comment-only lines do not generate layout tokens or alter the layout stack.

---

### 1.2 Concrete Surface Syntax Grammar
```bnf
program    ::= segment*
segment    ::= binding

binding    ::= fname pattern* "=" expr [ "where" "{" binding_list "}" ]
binding_list ::= binding ( ";" binding )*

pattern    ::= pat_atom
             | pat_atom ":" pattern

pat_atom   ::= "_"
             | INT
             | CHAR
             | IDENT
             | "[" "]"
             | "(" pattern_list ")"

pattern_list ::= pattern ( "," pattern )*

expr       ::= expr_or
             | expr_or "where" "{" binding_list "}"

expr_or    ::= expr_and [ "\\/" expr_or ]
expr_and   ::= expr_cons [ "&" expr_and ]
expr_cons  ::= expr_pp [ ":" expr_cons ]
expr_pp    ::= expr_comp [ "++" expr_pp | "--" expr_pp ]
expr_comp  ::= expr_add [ "==" expr_add | "~=" expr_add | "<" expr_add | ">" expr_add | "<=" expr_add | ">=" expr_add ]
expr_add   ::= expr_mod [ ( "+" | "-" ) expr_add ]
expr_mod   ::= expr_compose [ "mod" expr_compose | "*" expr_compose | "/" expr_compose ]
expr_compose ::= expr_app [ "." expr_compose ]
expr_app   ::= expr_atom+
expr_atom  ::= "#" expr_atom
             | INT
             | CHAR
             | STRING
             | IDENT
             | "[" list_body "]"
             | "(" expr_list ")"

list_body  ::= empty
             | expr ( "," expr )*
             | expr ".." expr
             | expr "|" qualifier_list

qualifier_list ::= qualifier ( ";" qualifier )*
qualifier  ::= IDENT "<-" expr
             | expr

expr_list  ::= expr ( "," expr )*
```

---

### 1.3 Surface Syntax Desugaring
Miracula parses high-level surface syntax construct and desugars them into core primitives:
- **String Literals**: `"abc"` desugars to `Cons (Char 'a', Cons (Char 'b', Cons (Char 'c', Nil)))`.
- **Negation Prefix**: `-e` desugars to `Sub (Int 0, e)`.
- **List Length**: `#e` desugars to `App (Var "length", e)`.
- **Logical AND (`e1 & e2`)**: Desugars to `If (e1, e2, Int 0)`.
- **Logical OR (`e1 \/ e2`)**: Desugars to `If (e1, Int 1, e2)`.
- **Function Composition (`f . g`)**: Desugars to `Lam (cx, App (f, App (g, Var cx)))` with a fresh variable `cx`.
- **List Comprehensions (`[ e | q1; q2 ]`)**: Represented in the AST as `ZF (e, [q1, q2])` and evaluated dynamically via lazy generators.

---

### 1.4 Abstract Syntax Tree (AST)
The core abstract representation consists of the following algebraic definition:
```
node ::= Int of int
       | Char of char
       | Nil
       | Cons of node * node
       | Tuple of node list
       | Var of string
       | Lam of string * node
       | Closure of string * node * environment
       | Let of (string * node) list * node
       | Proj of int * node
       | MatchError
       | Thunk of thunk_state ref
       | IfZero of node * node * node
       | IfNil of node * node * node
       | If of node * node * node
       | Append of node * node
       | Diff of node * node
       | ZF of node * qualifier list
       | Range of node * node
       | Add of node * node
       | Sub of node * node
       | Mul of node * node
       | Div of node * node
       | Mod of node * node
       | Eq of node * node
       | Ne of node * node
       | Lt of node * node
       | Gt of node * node
       | Le of node * node
       | Ge of node * node
```

---

## 2. Static Semantics (The Type System)

Unlike standard Miranda, which features static Hindley-Milner type inference, **Miracula is a dynamically-typed language subset**. 

### 2.1 Types
Type assertions and annotations are omitted from the parser. The core language behaves as a uni-typed system where expressions evaluate to constructors, closures, or integers.

### 2.2 Semantic Restrictions
- **Algebraic Data Types (ADTs)**: User-defined algebraic data types (`::=`) are **not supported**. The only structured types are built-in **Lists** (`Nil`/`Cons`) and **Tuples** (`Tuple`).
- **Dynamic Type Enforcement**: Type constraints are checked dynamically during evaluation in `whnf`:
  - Modulo (`mod`), division (`/`), multiplication (`*`), addition (`+`), and subtraction (`-`) expect operands to evaluate to `Int`.
  - Inequality operations (`<`, `>`, `<=`, `>=`) expect operands to evaluate to `Int`.
  - Equality (`==`) and inequality (`~=`) recursively support comparing `Int`, `Char`, `Nil`/`Cons` (lists), and `Tuple` structures.
- **Monomorphic Scoping**: Local definitions in `where` clauses bind values in local scopes. Since typing is checked dynamically at runtime, there is no static let-polymorphism; values are evaluated on-demand under their bound environments.

---

## 3. Dynamic Semantics (The Evaluation Model)

Miracula uses a **lazy, call-by-need graph reduction model** implemented via a heap of mutable thunks.

### 3.1 Thunks & Sharing
To prevent re-evaluation (call-by-name), expressions bound to variables in environments or passed to closures are wrapped in a `Thunk` containing a mutable reference cell:
```sml
datatype thunk_state =
    Unevaluated of node * environment
  | Evaluating
  | Evaluated of node
```

### 3.2 Evaluation Rules (Weak Head Normal Form)
The evaluation function `whnf (env) (node)` reduces an expression until its outermost constructor is exposed (WHNF).

#### Variables (Var)
Looking up `Var x` in the environment `env`:
1. If `x` maps to a built-in function (e.g., `hd`, `tl`, `show`, `read`, `lines`, `numval`, `length`), return `Var x` directly.
2. If `x` maps to `Thunk r`:
   - If `!r` is `Evaluated n'`, return `n'`.
   - If `!r` is `Evaluating`, raise a `RuntimeError` (Blackhole: infinite recursion detected).
   - If `!r` is `Unevaluated (expr, saved_env)`:
     - Set `r := Evaluating`.
     - Evaluate `result = whnf (saved_env) (expr)`.
     - Set `r := Evaluated result`.
     - Return `result`.

#### Lambdas & Closures
- A `Lam (x, body)` evaluates under `whnf env` to a `Closure (x, body, env)`, capturing the lexical environment.
- Evaluating a `Closure` directly returns itself.

#### Application (App)
Evaluating `App (e1, e2)` under `whnf env`:
1. Evaluate `f = whnf env e1`.
2. If `f` is a `Closure (x, body, closure_env)`:
   - Create a thunk for the argument: `t = Thunk (ref (Unevaluated (e2, env)))`.
   - Insert the thunk into the captured closure environment: `extended_env = closure_env + [x -> t]`.
   - Evaluate `whnf extended_env body`.

#### Conditionals
- `If (cond, t, f)`: Evaluates `whnf env cond`. If it is an `Int n` (where `n <> 0`), evaluate `whnf env t`. Otherwise, evaluate `whnf env f`.
- `IfZero (cond, t, f)`: Evaluates `whnf env cond`. If it is `Int 0`, evaluate `whnf env t`. Otherwise, evaluate `whnf env f`.
- `IfNil (cond, t, f)`: Evaluates `whnf env cond`. If it is `Nil`, evaluate `whnf env t`. Otherwise, evaluate `whnf env f`.

#### Lists & Tuples
- `Nil` evaluates to `Nil`.
- `Cons (h, t)` evaluates to `Cons (h', t')` where `h'` and `t'` are conditionally wrapped in thunks under `env` if they require evaluation (i.e. they are not already values).
- `Tuple elms` evaluates to `Tuple elms'` where each element is wrapped in a `Thunk` if it is not already evaluated.

---

## 4. The Standard Prelude (Built-ins)

Foundational functions are implemented in SML as built-ins or loaded from `stdenv.m`.

### 4.1 Built-in Primitives
- **`hd list`**: Evaluates `list` to `Cons (h, t)` and returns `whnf env h`.
- **`tl list`**: Evaluates `list` to `Cons (h, t)` and returns `whnf env t`.
- **`length list`**: Recursively counts list elements: `len Nil = 0`, `len (Cons (_, t)) = 1 + len t`. Returns an `Int`.
- **`read filename`**: Reads raw text from `filename` and returns it as a character list (string).
- **`lines str`**: Splits a character list on newline characters (`\n`), returning a list of strings.
- **`numval str`**: Converts a character list (string) representing an integer into an `Int`.
- **`show expr`**: Renders `expr` in Weak Head Normal Form as a printable character list (string).

---

### 4.2 Standard Environment (`stdenv.m`)
The standard library environment defines common combinators and lazy stream processors:

```miranda
|| Standard folding operations
foldl f z []     = z
foldl f z (x:xs) = foldl f (f z x) xs

foldr f z []     = z
foldr f z (x:xs) = f x (foldr f z xs)

|| Helper combinator
converse f a b = f b a

|| Reverse list
reverse = foldl (converse(:)) []

|| Sum of list elements
sum = foldl (+) 0

|| Lazy list mapping and filtering
map f x = [f a | a<-x]
filter p xs = [x | x <- xs; p x]

|| Prefix take/drop operations
take 0 xs     = []
take n []     = []
take n (x:xs) = x : take (n-1) xs

drop 0 xs     = xs
drop n []     = []
drop n (x:xs) = drop (n-1) xs

|| Lazy conditional filter
takewhile p []     = []
takewhile p (x:xs) = if p x then x : takewhile p xs else []

|| Infinite list generators
iterate f x = x : iterate f (f x)
repeat x = x : repeat x

|| Tuple-based list zip
zip ([], []) = []
zip (x:xs, y:ys) = (x, y) : zip (xs, ys)
```
