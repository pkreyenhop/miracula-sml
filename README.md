# Miracula (Miranda Interpreter in SML)

Miracula is a lightweight interpreter and interactive REPL for a lazy functional programming language inspired by Miranda. It is written in Standard ML (SML) and features lazy evaluation, pattern-matching desugaring, list primitives, and an interactive environment.

## Features

- **Lazy Evaluation (Call-by-Need):** Expressions are evaluated only when required using memoized thunks to avoid redundant computation. Includes cycle/infinite loop detection (`Blackhole` exception).
- **Lexical Closures (Lexical Scoping):** First-class environment-capturing closures that support lexical scope for nested curried functions, ensuring outer variable bindings are resolved correctly in recursive/nested calls.
- **List Pattern Matching & Desugaring:** Allows defining functions through multiple equations with pattern matching on integers, variables, and list patterns (`[]` and `(x:xs)` cons patterns) compiled into conditional decision trees.
- **Lazy List Ranges:** Dynamic sequence generators using `[e1..e2]` syntax (e.g., `[1..100]`), lazily evaluated step-by-step so that sequences are generated only as they are accessed.
- **Interactive REPL:** Provides a prompt (`miranda> `) to define variables/functions and evaluate expressions interactively.
  - **Enhanced Line Editing**: Basic editing via Left/Right arrows, Backspace, Home (Ctrl-A), End (Ctrl-E), and line killing (Ctrl-K).
  - **Input History**: Navigate past inputs using Up/Down arrow keys, with draft line saving.
  - **Graceful Fallbacks**: Automatically detects interactive terminal (TTY) status, falling back cleanly for piped script input.
  - `/e` command: Open and edit `script.m` in the terminal using `vi`, reloading all definitions on exit.
  - `/q` command: Exit the REPL.

## Syntax & Examples

### Basic Expressions
```miranda
miranda> 3 + 4
Result: 7
Evaluation time: 0 ms
```

### Lambdas
Lambdas are defined using backslashes:
```miranda
miranda> (\x. x + 2) 5
Result: 7
Evaluation time: 0 ms
```

### Conditionals
Use `ifzero` to inspect numeric values:
```miranda
miranda> ifzero 0 then 42 else 0
Result: 42
Evaluation time: 0 ms
```

### Lists and Primitives
```miranda
miranda> hd [1, 2, 3]
Result: 1
Evaluation time: 0 ms

miranda> tl [1, 2, 3]
Result: [2, 3]
Evaluation time: 0 ms
```

### Defining Functions (script.m)
You can define variables and functions directly in the REPL or load them from `script.m`. 
For example, in `script.m`:
```miranda
add1 x = x+1

fib 0 = 0
fib 1 = 1
fib n = fib (n-1) + fib (n-2)

x = fib (3+1)
```

## How to Build and Run

### Prerequisites
Make sure you have [MLton](http://mlton.org/) installed on your system.

### Build
Compile the interpreter using MLton:
```bash
make
```
Or directly using the ML Basis configuration:
```bash
mlton miracula.mlb
```

### Run

Launch the REPL by running the compiled executable:
```bash
./miracula [script_file]
```
If no script file argument is provided, the interpreter defaults to loading `script.m` if present. For a demonstration of all language features, you can run:
```bash
./miracula features.m
```

### Test

You can run the automated verification test suite containing 26 test cases via:
```bash
make test
```
