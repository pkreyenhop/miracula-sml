(* CM.make "$smlnj-lib.cm"; *)

(* ========================================================================== *)
(* 1. TYPE & ENVIRONMENT DEFINITIONS USING STRUCTURES                        *)
(* ========================================================================== *)

structure StringKey = struct
    type ord_key = string
    val compare = String.compare
end

structure StringMap = BinaryMapFn(StringKey)

datatype thunk_state =
    Unevaluated of node * (node StringMap.map)
  | Evaluating
  | Evaluated of node

and node =
    Int of int
  | Var of string
  | Lam of string * node
  | App of node * node
  | Sub of node * node
  | Add of node * node
  | IfZero of node * node * node
  | Cons of node * node
  | Nil
  | Thunk of thunk_state ref

type env = node StringMap.map

exception Blackhole of string
exception RuntimeError of string

(* ========================================================================== *)
(* 2. LEXER IMPLEMENTATION                                                   *)
(* ========================================================================== *)

datatype token =
    TOK_LAMBDA | TOK_DOT | TOK_ARROW | TOK_ASSIGN
  | TOK_LPAREN | TOK_RPAREN | TOK_LBRACK | TOK_RBRACK | TOK_COMMA
  | TOK_SUB | TOK_ADD
  | TOK_IFZERO | TOK_THEN | TOK_ELSE
  | TOK_INT of int
  | TOK_VAR of string
  | TOK_EOF

local
    fun isDigit c = Char.isDigit c
    fun isAlphaNum c = Char.isAlphaNum c orelse c = #"_"
in
    fun tokenize str =
        let
            val size = String.size str
            fun loop i acc =
                if i >= size then List.rev (TOK_EOF :: acc)
                else
                    let val c = String.sub(str, i) in
                        if Char.isSpace c then loop (i + 1) acc
                        else if c = #"\\" then loop (i + 1) (TOK_LAMBDA :: acc)
                        else if c = #"."  then loop (i + 1) (TOK_DOT :: acc)
                        else if c = #"("  then loop (i + 1) (TOK_LPAREN :: acc)
                        else if c = #")"  then loop (i + 1) (TOK_RPAREN :: acc)
                        else if c = #"["  then loop (i + 1) (TOK_LBRACK :: acc)
                        else if c = #"]"  then loop (i + 1) (TOK_RBRACK :: acc)
                        else if c = #","  then loop (i + 1) (TOK_COMMA :: acc)
                        else if c = #"="  then loop (i + 1) (TOK_ASSIGN :: acc)
                        else if c = #"+"  then loop (i + 1) (TOK_ADD :: acc)
                        else if c = #"-"  then
                            if i + 1 < size andalso String.sub(str, i+1) = #">"
                            then loop (i + 2) (TOK_ARROW :: acc)
                            else loop (i + 1) (TOK_SUB :: acc)
                        else if isDigit c then
                            let
                                fun readNum j s =
                                    if j < size andalso isDigit (String.sub(str, j))
                                    then readNum (j + 1) (s ^ String.str (String.sub(str, j)))
                                    else (j, valOf (Int.fromString s))
                                val (nextJ, v) = readNum (i + 1) (String.str c)
                            in loop nextJ (TOK_INT v :: acc) end
                        else if Char.isAlpha c then
                            let
                                fun readVar j s =
                                    if j < size andalso isAlphaNum (String.sub(str, j))
                                    then readVar (j + 1) (s ^ String.str (String.sub(str, j)))
                                    else (j, s)
                                val (nextJ, s) = readVar (i + 1) (String.str c)
                                val tok = case s of
                                              "ifzero" => TOK_IFZERO
                                            | "then"   => TOK_THEN
                                            | "else"   => TOK_ELSE
                                            | _        => TOK_VAR s
                            in loop nextJ (tok :: acc) end
                        else (print ("Lex error: char " ^ String.str c ^ "\n"); loop (i+1) acc)
                    end
        in loop 0 [] end
end

(* ========================================================================== *)
(* 3. PARSER MECHANICS                                                       *)
(* ========================================================================== *)

datatype parsed_pattern = PatInt of int | PatVar of string
type raw_binding = { fname: string, pats: parsed_pattern list, body: node }
datatype stmt = ScriptBind of raw_binding | REPLEval of node

fun parse tokens =
    let
        val toks = ref tokens
        fun peek () = List.hd (!toks)
        fun consume () = toks := List.tl (!toks)

        fun parse_expr () =
            case peek () of
                TOK_LAMBDA =>
                (consume ();
                 case peek () of
                     TOK_VAR x =>
                     (consume ();
                      if peek () <> TOK_DOT then raise Fail "Expected '.' after lambda variable" else ();
                      consume ();
                      Lam (x, parse_expr ()))
                   | _ => raise Fail "Expected variable after lambda '\\'")
              | TOK_IFZERO =>
                (consume ();
                 let
                     val cond = parse_expr ()
                     val _ = if peek () <> TOK_THEN then raise Fail "Expected 'then'" else consume ()
                     val t_branch = parse_expr ()
                     val _ = if peek () <> TOK_ELSE then raise Fail "Expected 'else'" else consume ()
                     val f_branch = parse_expr ()
                 in IfZero (cond, t_branch, f_branch) end)
              | _ => parse_add_sub ()

        and parse_add_sub () =
            let fun loop left =
                case peek () of
                    TOK_ADD => (consume (); loop (Add (left, parse_app ())))
                  | TOK_SUB => (consume (); loop (Sub (left, parse_app ())))
                  | _ => left
            in loop (parse_app ()) end

        and parse_app () =
            let fun loop left =
                case peek () of
                    TOK_INT _ => loop (App (left, parse_atom ()))
                  | TOK_VAR _ => loop (App (left, parse_atom ()))
                  | TOK_LPAREN => loop (App (left, parse_atom ()))
                  | TOK_LBRACK => loop (App (left, parse_atom ()))
                  | _ => left
            in loop (parse_atom ()) end

        and parse_atom () =
            case peek () of
                TOK_INT n => (consume (); Int n)
              | TOK_VAR x => (consume (); Var x)
              | TOK_LPAREN =>
                (consume ();
                 let val e = parse_expr () in
                     if peek () <> TOK_RPAREN then raise Fail "Expected ')'" else ();
                     consume ();
                     e
                 end)
              | TOK_LBRACK => (consume (); parse_list_elements ())
              | _ => raise Fail "Unexpected token inside atom expression"

        and parse_list_elements () =
            if peek () = TOK_RBRACK then (consume (); Nil)
            else
                let val head = parse_expr () in
                    if peek () = TOK_COMMA then (consume (); Cons (head, parse_list_elements ()))
                    else if peek () = TOK_RBRACK then (consume (); Cons (head, Nil))
                    else raise Fail "Expected ',' or ']' in list literal"
                end

        fun is_assignment ts =
            let fun check [] = false
                  | check (TOK_ASSIGN :: _) = true
                  | check (_ :: rest) = check rest
            in check ts end
    in
        if is_assignment (!toks) then
            case peek () of
                TOK_VAR name =>
                (consume ();
                 let
                     fun collect_patterns acc =
                         case peek () of
                             TOK_INT n => (consume (); collect_patterns (PatInt n :: acc))
                           | TOK_VAR x => (consume (); collect_patterns (PatVar x :: acc))
                           | TOK_ASSIGN => (consume (); List.rev acc)
                           | _ => raise Fail "Malformed equation left hand side"
                     val pats = collect_patterns []
                     val expr_body = parse_expr ()
                 in ScriptBind { fname = name, pats = pats, body = expr_body } end)
              | _ => raise Fail "Left hand side of binding must start with an identifier"
        else
            let val e = parse_expr () in
                if peek () <> TOK_EOF then raise Fail "Trailing tokens left unparsed" else ();
                REPLEval e
            end
    end

(* ========================================================================== *)
(* 4. RUNTIME WORKSPACE                                                      *)
(* ========================================================================== *)

fun whnf (env : env) (n : node) : node =
    case n of
        Int n => Int n
      | Lam (x, body) => Lam (x, body)
      | Cons (h, t) => Cons (h, t)
      | Nil => Nil
      | Var x =>
        if x = "hd" orelse x = "tl" then Var x
        else
            (case StringMap.find (env, x) of
                 SOME (Thunk r) =>
                 (case !r of
                      Evaluated n' => n'
                    | Evaluating  => raise Blackhole ("Infinite loop on identifier: " ^ x)
                    | Unevaluated (expr, saved_env) =>
                      (r := Evaluating;
                       let val result = whnf saved_env expr in
                           r := Evaluated result;
                           result
                       end))
               | SOME explicit_node => whnf env explicit_node
               | NONE => raise RuntimeError ("Unbound variable: " ^ x))
      | App (e1, e2) =>
        (case whnf env e1 of
             Var "hd" =>
             (case whnf env e2 of
                  Cons (h, _) => whnf env h
                | Nil => raise RuntimeError "hd applied to empty list"
                | _ => raise RuntimeError "hd expects a list")
           | Var "tl" =>
             (case whnf env e2 of
                  Cons (_, t) => whnf env t
                | Nil => raise RuntimeError "tl applied to empty list"
                | _ => raise RuntimeError "tl expects a list")
           | Lam (x, body) =>
             let
                 val shared_thunk = Thunk (ref (Unevaluated (e2, env)))
                 val extended_env = StringMap.insert (env, x, shared_thunk)
             in whnf extended_env body end
           | _ => raise RuntimeError "Non-functional application")
      | Sub (e1, e2) =>
        (case (whnf env e1, whnf env e2) of
             (Int n1, Int n2) => Int (n1 - n2)
           | _ => raise RuntimeError "Subtraction expects integers")
      | Add (e1, e2) =>
        (case (whnf env e1, whnf env e2) of
             (Int n1, Int n2) => Int (n1 + n2)
           | _ => raise RuntimeError "Addition expects integers")
      | IfZero (cond, t_branch, f_branch) =>
        (case whnf env cond of
             Int 0 => whnf env t_branch
           | Int _ => whnf env f_branch
           | _ => raise RuntimeError "Condition must resolve to an integer")
      | Thunk r =>
        (case !r of
             Evaluated n' => n'
           | Evaluating  => raise Blackhole "Infinite loop inside generic thunk node"
           | Unevaluated (expr, saved_env) =>
             (r := Evaluating;
              let val result = whnf saved_env expr in
                  r := Evaluated result;
                  result
              end))

fun print_node env node =
    case node of
        Int n => Int.toString n
      | Lam (x, _) => "\\" ^ x ^ ". <closure>"
      | Var x => x
      | App (e1, e2) => "(" ^ print_node env e1 ^ " " ^ print_node env e2 ^ ")"
      | Sub (e1, e2) => "(" ^ print_node env e1 ^ " - " ^ print_node env e2 ^ ")"
      | Add (e1, e2) => "(" ^ print_node env e1 ^ " + " ^ print_node env e2 ^ ")"
      | IfZero _ => "<conditional>"
      | Thunk _ => "<thunk>"
      | Nil => "[]"
      | Cons _ =>
        let
            fun collect elements current =
                case whnf env current of
                    Cons (h, t) => collect (print_node env h :: elements) t
                  | Nil => List.rev elements
                  | rest => List.rev (print_node env rest :: elements)
        in
            "[" ^ String.concatWith "," (collect [] node) ^ "]"
        end

(* ========================================================================== *)
(* 5. DESUGARER LOGIC FOR STRINGS                                            *)
(* ========================================================================== *)

fun desugar_equations (eqs : raw_binding list) : node =
    case eqs of
        [] => raise Fail "Empty equation sequence"
      | [ { pats = [], body, ... } ] => body
      | [ { pats = [PatVar x], body, ... } ] => Lam (x, body)
      | _ =>
        let
            val first_eq = List.hd eqs
            val arity = List.length (#pats first_eq)
            val _ = if List.exists (fn e => List.length (#pats e) <> arity) eqs 
                    then raise Fail "Equations have mismatched parameter arities" else ()
            
            fun make_param_names 0 acc = acc
              | make_param_names n acc = make_param_names (n-1) (("p" ^ Int.toString (n-1)) :: acc)
            val param_names = make_param_names arity []

            fun build_decision_tree [] = raise Fail "Pattern matching exhausted without catch-all"
              | build_decision_tree (eq :: rest) =
                let
                    fun check_pats [] [] tree_body = tree_body
                      | check_pats (p::p_rest) (PatInt target_val :: pat_rest) tree_body =
                        IfZero (Sub (Var p, Int target_val), check_pats p_rest pat_rest tree_body, build_decision_tree rest)
                      | check_pats (p::p_rest) (PatVar binding_name :: pat_rest) tree_body =
                        let val substituted_body = 
                                if binding_name = p then tree_body
                                else App (Lam (binding_name, tree_body), Var p)
                        in check_pats p_rest pat_rest substituted_body end
                      | check_pats _ _ _ = raise Fail "Internal pattern arity violation"
                in check_pats param_names (#pats eq) (#body eq) end

            val decision_tree = build_decision_tree eqs
        in List.foldr (fn (p, acc) => Lam (p, acc)) decision_tree param_names end

fun load_script_file filename env =
    let
        fun file_exists name =
            (let val ins = TextIO.openIn name in TextIO.closeIn ins; true end) handle _ => false
    in
        if not (file_exists filename) then
            (print ("Script file '" ^ filename ^ "' not found. Starting with empty space.\n"); env)
        else
            let
                val ic = TextIO.openIn filename
                fun read_all lines =
                    case TextIO.inputLine ic of
                        NONE => (TextIO.closeIn ic; List.rev lines)
                      | SOME line =>
                        let 
                            val l = String.implode (List.filter (fn c => c <> #"\r" andalso c <> #"\n") (String.explode line))
                            fun is_empty s = String.size (String.translate (fn c => if Char.isSpace c then "" else String.str c) s) = 0
                        in
                            if is_empty l orelse (String.size l >= 2 andalso String.substring(l,0,2) = "||")
                            then read_all lines
                            else read_all (l :: lines)
                        end
                val raw_lines = read_all []
                
                fun process_line line =
                    case parse (tokenize line) of
                        ScriptBind b => b
                      | _ => raise Fail "Invalid expression structure in script file"
                val bindings = List.map process_line raw_lines

                fun update_group (b : raw_binding, m) =
                    let val current = case StringMap.find (m, #fname b) of SOME l => l | NONE => []
                    in StringMap.insert (m, #fname b, current @ [b]) end
                val grouped = List.foldl update_group StringMap.empty bindings
            in
                StringMap.foldli (fn (fname, eq_list, acc_env) =>
                    StringMap.insert (acc_env, fname, desugar_equations eq_list)
                ) env grouped
            end
    end

(* ========================================================================== *)
(* 6. REPL ENGINE                                                            *)
(* ========================================================================== *)

fun repl (env : env) =
    let
        val _ = print "miranda> "
        val _ = TextIO.flushOut TextIO.stdOut
    in
        case TextIO.inputLine TextIO.stdIn of
            NONE => print "\nGoodbye.\n"
          | SOME line =>
            let 
                val line_trimmed = String.implode (List.filter (fn c => c <> #"\n" andalso c <> #"\r") (String.explode line))
                fun is_empty s = String.size (String.translate (fn c => if Char.isSpace c then "" else String.str c) s) = 0
            in
                if line_trimmed = "/q" orelse line_trimmed = "exit" orelse line_trimmed = "quit" then
                    print "Goodbye.\n"
                else if line_trimmed = "/e" then
                    let
                        val _ = print "Opening vi script.m ...\n"
                        val _ = OS.Process.system "vi script.m"
                        val _ = print "Reloading environment profiles from script.m...\n"
                        val reloaded_env = load_script_file "script.m" StringMap.empty
                    in repl reloaded_env end
                else if is_empty line_trimmed then
                    repl env
                else
                    let
                        val tokens = tokenize line_trimmed
                    in
                        (case parse tokens of
                             ScriptBind b =>
                             let
                                 val final_lambda = desugar_equations [b]
                                 val updated_env = StringMap.insert (env, #fname b, final_lambda)
                             in
                                 print ("Defined variable: " ^ #fname b ^ "\n");
                                 repl updated_env
                             end
                           | REPLEval expr =>
                             let
                                 val start = Time.now ()
                                 val result = whnf env expr
                                 val result_str = print_node env result
                                 val duration = Time.toMilliseconds (Time.- (Time.now (), start))
                             in
                                 print ("Result: " ^ result_str ^ "\n");
                                 print ("Evaluation time: " ^ LargeInt.toString duration ^ " ms\n");
                                 repl env
                             end)
                        handle
                            Fail msg => (print ("Lex/Parse Error: " ^ msg ^ "\n"); repl env)
                          | Blackhole msg => (print ("Runtime Error: " ^ msg ^ "\n"); repl env)
                          | RuntimeError msg => (print ("Runtime Error: " ^ msg ^ "\n"); repl env)
                          | exn => (print ("Error: " ^ General.exnMessage exn ^ "\n"); repl env)
                    end
            end
    end

fun main () =
    let
        val _ = print "==================================================\n"
        val _ = print " Environment-Sharing SML REPL                     \n"
        val _ = print " Use '/e' to edit script.m, '/q' to exit          \n"
        val _ = print "==================================================\n"
        (* val _ = CM.make "$smlnj-lib.cm" (* Force dynamic instantiation *) *)
        val initial_env = load_script_file "script.m" StringMap.empty
    in
        repl initial_env
    end

val _ = main ()
