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
  | Range of node * node
  | IfNil of node * node * node
  | MatchError
  | Closure of string * node * (node StringMap.map)
  | Thunk of thunk_state ref

type env = node StringMap.map

exception Blackhole of string
exception RuntimeError of string

(* ========================================================================== *)
(* 2. LEXER IMPLEMENTATION                                                   *)
(* ========================================================================== *)

datatype token =
    TOK_LAMBDA | TOK_DOT | TOK_DOTDOT | TOK_ARROW | TOK_ASSIGN
  | TOK_LPAREN | TOK_RPAREN | TOK_LBRACK | TOK_RBRACK | TOK_COMMA | TOK_COLON
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
                        else if c = #"."  then
                            if i + 1 < size andalso String.sub(str, i+1) = #"."
                            then loop (i + 2) (TOK_DOTDOT :: acc)
                            else loop (i + 1) (TOK_DOT :: acc)
                        else if c = #"("  then loop (i + 1) (TOK_LPAREN :: acc)
                        else if c = #")"  then loop (i + 1) (TOK_RPAREN :: acc)
                        else if c = #"["  then loop (i + 1) (TOK_LBRACK :: acc)
                        else if c = #"]"  then loop (i + 1) (TOK_RBRACK :: acc)
                        else if c = #","  then loop (i + 1) (TOK_COMMA :: acc)
                        else if c = #"="  then loop (i + 1) (TOK_ASSIGN :: acc)
                        else if c = #":"  then loop (i + 1) (TOK_COLON :: acc)
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

datatype parsed_pattern =
    PatInt of int
  | PatVar of string
  | PatNil
  | PatCons of parsed_pattern * parsed_pattern

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
              | _ => parse_cons ()

        and parse_cons () =
            let val left = parse_add_sub () in
                case peek () of
                    TOK_COLON => (consume (); Cons (left, parse_cons ()))
                  | _ => left
            end

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
                    if peek () = TOK_DOTDOT then
                        (consume ();
                         let val tail_expr = parse_expr () in
                             if peek () <> TOK_RBRACK then raise Fail "Expected ']' after range expression" else ();
                             consume ();
                             Range (head, tail_expr)
                         end)
                    else if peek () = TOK_COMMA then (consume (); Cons (head, parse_list_elements ()))
                    else if peek () = TOK_RBRACK then (consume (); Cons (head, Nil))
                    else raise Fail "Expected '..', ',', or ']' in list expression"
                end

        fun is_assignment ts =
            let fun check [] = false
                  | check (TOK_ASSIGN :: _) = true
                  | check (_ :: rest) = check rest
            in check ts end

        fun parse_pattern () =
            case peek () of
                TOK_INT n => (consume (); PatInt n)
              | TOK_VAR x => (consume (); PatVar x)
              | TOK_LBRACK =>
                (consume ();
                 if peek () = TOK_RBRACK then (consume (); PatNil)
                 else raise Fail "Only empty list pattern '[]' is supported directly")
              | TOK_LPAREN =>
                (consume ();
                 let val p = parse_pattern_cons () in
                     if peek () <> TOK_RPAREN then raise Fail "Expected ')' in pattern" else ();
                     consume ();
                     p
                 end)
              | _ => raise Fail "Malformed pattern in equation left hand side"

        and parse_pattern_cons () =
            let val left = parse_pattern () in
                case peek () of
                    TOK_COLON => (consume (); PatCons (left, parse_pattern_cons ()))
                  | _ => left
            end
    in
        if is_assignment (!toks) then
            case peek () of
                TOK_VAR name =>
                (consume ();
                 let
                     fun collect_patterns acc =
                         if peek () = TOK_ASSIGN then (consume (); List.rev acc)
                         else collect_patterns (parse_pattern () :: acc)
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
      | Lam (x, body) => Closure (x, body, env)
      | Closure (x, body, closure_env) => Closure (x, body, closure_env)
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
           | Closure (x, body, closure_env) =>
              let
                  val shared_thunk = Thunk (ref (Unevaluated (e2, env)))
                  val extended_env = StringMap.insert (closure_env, x, shared_thunk)
              in whnf extended_env body end
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
      | IfNil (cond, t_branch, f_branch) =>
        (case whnf env cond of
             Nil => whnf env t_branch
           | Cons _ => whnf env f_branch
           | _ => raise RuntimeError "Condition must resolve to a list")
      | Range (e1, e2) =>
        (case (whnf env e1, whnf env e2) of
             (Int n1, Int n2) =>
             if n1 > n2 then Nil
             else Cons (Int n1, Thunk (ref (Unevaluated (Range (Int (n1 + 1), e2), env))))
           | _ => raise RuntimeError "Range bounds must evaluate to integers")
      | MatchError => raise RuntimeError "Pattern matching exhausted"
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
      | Closure (x, _, _) => "\\" ^ x ^ ". <closure>"
      | Var x => x
      | App (e1, e2) => "(" ^ print_node env e1 ^ " " ^ print_node env e2 ^ ")"
      | Sub (e1, e2) => "(" ^ print_node env e1 ^ " - " ^ print_node env e2 ^ ")"
      | Add (e1, e2) => "(" ^ print_node env e1 ^ " + " ^ print_node env e2 ^ ")"
      | IfZero _ => "<conditional>"
      | IfNil _ => "<conditional-nil>"
      | MatchError => "<match-error>"
      | Thunk _ => "<thunk>"
      | Range (e1, e2) => "[" ^ print_node env e1 ^ ".." ^ print_node env e2 ^ "]"
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

val var_counter = ref 0
fun new_var_name prefix =
    let
        val c = !var_counter
        val _ = var_counter := c + 1
    in
        prefix ^ "_" ^ Int.toString c
    end

fun desugar_equations (eqs : raw_binding list) : node =
    case eqs of
        [] => raise Fail "Empty equation sequence"
      | [ ({ pats = [], body, ... } : raw_binding) ] => body
      | [ ({ pats = [PatVar x], body, ... } : raw_binding) ] => Lam (x, body)
      | _ =>
        let
            val { pats = first_pats, ... } = List.hd eqs
            val arity = List.length first_pats
            val _ = if List.exists (fn ({pats, ...} : raw_binding) => List.length pats <> arity) eqs 
                    then raise Fail "Equations have mismatched parameter arities" else ()
            
            fun make_param_names 0 acc = acc
              | make_param_names n acc = make_param_names (n-1) (("p" ^ Int.toString (n-1)) :: acc)
            val param_names = make_param_names arity []

            fun build_decision_tree [] = MatchError
              | build_decision_tree (({pats, body, ...} : raw_binding) :: rest) =
                let
                    fun check_pats [] [] tree_body = tree_body
                      | check_pats (p::p_rest) (pat::pat_rest) tree_body =
                        (case pat of
                             PatInt target_val =>
                             IfZero (Sub (Var p, Int target_val), check_pats p_rest pat_rest tree_body, build_decision_tree rest)
                           | PatVar binding_name =>
                             let val substituted_body = 
                                     if binding_name = p then tree_body
                                     else App (Lam (binding_name, tree_body), Var p)
                             in check_pats p_rest pat_rest substituted_body end
                           | PatNil =>
                             IfNil (Var p, check_pats p_rest pat_rest tree_body, build_decision_tree rest)
                           | PatCons (head_pat, tail_pat) =>
                             let
                                 val h_var = new_var_name "h"
                                 val t_var = new_var_name "t"
                                 val failure_branch = build_decision_tree rest
                                 val inner_body = check_pats (h_var :: t_var :: p_rest) (head_pat :: tail_pat :: pat_rest) tree_body
                             in
                                 IfNil (Var p,
                                        failure_branch,
                                        App (Lam (h_var,
                                                  App (Lam (t_var, inner_body),
                                                       App (Var "tl", Var p))),
                                             App (Var "hd", Var p)))
                             end)
                      | check_pats _ _ _ = raise Fail "Internal pattern arity violation"
                in check_pats param_names pats body end

            val decision_tree = build_decision_tree eqs
        in List.foldr (fn (p, acc) => Lam (p, acc)) decision_tree param_names end

fun print_ast node =
    case node of
        Int n => "Int " ^ Int.toString n
      | Var x => "Var " ^ x
      | Lam (x, body) => "Lam (" ^ x ^ ", " ^ print_ast body ^ ")"
      | Closure (x, body, _) => "Closure (" ^ x ^ ", " ^ print_ast body ^ ")"
      | App (e1, e2) => "App (" ^ print_ast e1 ^ ", " ^ print_ast e2 ^ ")"
      | Sub (e1, e2) => "Sub (" ^ print_ast e1 ^ ", " ^ print_ast e2 ^ ")"
      | Add (e1, e2) => "Add (" ^ print_ast e1 ^ ", " ^ print_ast e2 ^ ")"
      | IfZero (c, t, f) => "IfZero (" ^ print_ast c ^ ", " ^ print_ast t ^ ", " ^ print_ast f ^ ")"
      | IfNil (c, t, f) => "IfNil (" ^ print_ast c ^ ", " ^ print_ast t ^ ", " ^ print_ast f ^ ")"
      | MatchError => "MatchError"
      | Nil => "Nil"
      | Cons (h, t) => "Cons (" ^ print_ast h ^ ", " ^ print_ast t ^ ")"
      | Range (e1, e2) => "Range (" ^ print_ast e1 ^ ", " ^ print_ast e2 ^ ")"
      | Thunk _ => "Thunk"

fun load_script_file filename env =
    let
        fun file_exists name =
            let val ins = TextIO.openIn name in TextIO.closeIn ins; true end handle _ => false
    in
        if not (file_exists filename) then
            if filename = "stdenv.m" then
                (print ("Standard environment file 'stdenv.m' not found. Skipping.\n"); env)
            else
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

                fun update_group (b as {fname, ...} : raw_binding, m) =
                    let val current = case StringMap.find (m, fname) of SOME l => l | NONE => []
                    in StringMap.insert (m, fname, current @ [b]) end
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

datatype key =
    KeyChar of char
  | KeyEnter
  | KeyBackspace
  | KeyDelete
  | KeyUp
  | KeyDown
  | KeyLeft
  | KeyRight
  | KeyHome
  | KeyEnd
  | KeyCtrlC
  | KeyCtrlD
  | KeyCtrlL
  | KeyCtrlK
  | KeyUnknown of string

fun readKey () =
    case TextIO.input1 TextIO.stdIn of
        NONE => NONE
      | SOME #"\027" =>
        (case TextIO.input1 TextIO.stdIn of
             SOME #"[" =>
             (case TextIO.input1 TextIO.stdIn of
                  SOME #"A" => SOME KeyUp
                | SOME #"B" => SOME KeyDown
                | SOME #"C" => SOME KeyRight
                | SOME #"D" => SOME KeyLeft
                | SOME #"H" => SOME KeyHome
                | SOME #"F" => SOME KeyEnd
                | SOME #"1" =>
                  (case TextIO.input1 TextIO.stdIn of
                       SOME #"~" => SOME KeyHome
                     | SOME _ => SOME (KeyUnknown "esc[1...")
                     | NONE => NONE)
                | SOME #"3" =>
                  (case TextIO.input1 TextIO.stdIn of
                       SOME #"~" => SOME KeyDelete
                     | SOME _ => SOME (KeyUnknown "esc[3...")
                     | NONE => NONE)
                | SOME #"4" => SOME KeyEnd
                | SOME #"7" => SOME KeyHome
                | SOME #"8" => SOME KeyEnd
                | SOME c => SOME (KeyUnknown ("esc[" ^ String.str c))
                | NONE => NONE)
           | SOME #"O" =>
             (case TextIO.input1 TextIO.stdIn of
                  SOME #"H" => SOME KeyHome
                | SOME #"F" => SOME KeyEnd
                | SOME c => SOME (KeyUnknown ("escO" ^ String.str c))
                | NONE => NONE)
           | SOME c => SOME (KeyUnknown ("esc" ^ String.str c))
           | NONE => NONE)
      | SOME #"\n" => SOME KeyEnter
      | SOME #"\r" => SOME KeyEnter
      | SOME #"\003" => SOME KeyCtrlC
      | SOME #"\004" => SOME KeyCtrlD
      | SOME #"\012" => SOME KeyCtrlL
      | SOME #"\011" => SOME KeyCtrlK
      | SOME #"\127" => SOME KeyBackspace
      | SOME #"\008" => SOME KeyBackspace
      | SOME #"\001" => SOME KeyHome
      | SOME #"\005" => SOME KeyEnd
      | SOME c => SOME (KeyChar c)

fun redraw prompt left right =
    let
        val full_line = (List.rev left) @ right
        val left_str = String.implode (List.rev left)
        val _ = print ("\r\027[K" ^ prompt ^ String.implode full_line)
        val _ = print ("\r" ^ prompt ^ left_str)
        val _ = TextIO.flushOut TextIO.stdOut
    in
        ()
    end

fun readLineLoop prompt history =
    let
        fun loop (left, right, hist_idx, draft) =
            case readKey () of
                NONE => NONE
              | SOME KeyEnter =>
                let
                    val line = String.implode ((List.rev left) @ right)
                    val _ = print "\n"
                    val _ = TextIO.flushOut TextIO.stdOut
                in
                    SOME line
                end
              | SOME KeyCtrlC =>
                let
                    val _ = print "^C\n"
                    val _ = TextIO.flushOut TextIO.stdOut
                in
                    SOME ""
                end
              | SOME KeyCtrlD =>
                if List.null left andalso List.null right then
                    let
                        val _ = print "\n"
                        val _ = TextIO.flushOut TextIO.stdOut
                    in
                        NONE
                    end
                else
                    let
                        val new_right = if List.null right then [] else List.tl right
                        val _ = redraw prompt left new_right
                    in
                        loop (left, new_right, hist_idx, draft)
                    end
              | SOME KeyCtrlL =>
                let
                    val _ = print "\027[2J\027[H"
                    val _ = redraw prompt left right
                in
                    loop (left, right, hist_idx, draft)
                end
              | SOME KeyCtrlK =>
                let
                    val new_right = []
                    val _ = redraw prompt left new_right
                in
                    loop (left, new_right, hist_idx, draft)
                end
              | SOME KeyBackspace =>
                if List.null left then
                    loop (left, right, hist_idx, draft)
                else
                    let
                        val new_left = List.tl left
                        val _ = redraw prompt new_left right
                    in
                        loop (new_left, right, hist_idx, draft)
                    end
              | SOME KeyDelete =>
                if List.null right then
                    loop (left, right, hist_idx, draft)
                else
                    let
                        val new_right = List.tl right
                        val _ = redraw prompt left new_right
                    in
                        loop (left, new_right, hist_idx, draft)
                    end
              | SOME KeyLeft =>
                if List.null left then
                    loop (left, right, hist_idx, draft)
                else
                    let
                        val c = List.hd left
                        val new_left = List.tl left
                        val new_right = c :: right
                        val _ = redraw prompt new_left new_right
                    in
                        loop (new_left, new_right, hist_idx, draft)
                    end
              | SOME KeyRight =>
                if List.null right then
                    loop (left, right, hist_idx, draft)
                else
                    let
                        val c = List.hd right
                        val new_right = List.tl right
                        val new_left = c :: left
                        val _ = redraw prompt new_left new_right
                    in
                        loop (new_left, new_right, hist_idx, draft)
                    end
              | SOME KeyHome =>
                let
                    val new_right = (List.rev left) @ right
                    val new_left = []
                    val _ = redraw prompt new_left new_right
                in
                    loop (new_left, new_right, hist_idx, draft)
                end
              | SOME KeyEnd =>
                let
                    val new_left = (List.rev right) @ left
                    val new_right = []
                    val _ = redraw prompt new_left new_right
                in
                    loop (new_left, new_right, hist_idx, draft)
                end
              | SOME KeyUp =>
                let
                    val current_str = String.implode ((List.rev left) @ right)
                    val new_draft = if hist_idx = ~1 then current_str else draft
                    val next_idx = hist_idx + 1
                in
                    if next_idx < List.length history then
                        let
                            val hist_item = List.nth (history, next_idx)
                            val new_left = List.rev (String.explode hist_item)
                            val new_right = []
                            val _ = redraw prompt new_left new_right
                        in
                            loop (new_left, new_right, next_idx, new_draft)
                        end
                    else
                        loop (left, right, hist_idx, draft)
                end
              | SOME KeyDown =>
                if hist_idx = ~1 then
                    loop (left, right, hist_idx, draft)
                else if hist_idx = 0 then
                    let
                        val new_left = List.rev (String.explode draft)
                        val new_right = []
                        val _ = redraw prompt new_left new_right
                    in
                        loop (new_left, new_right, ~1, "")
                    end
                else
                    let
                        val next_idx = hist_idx - 1
                        val hist_item = List.nth (history, next_idx)
                        val new_left = List.rev (String.explode hist_item)
                        val new_right = []
                        val _ = redraw prompt new_left new_right
                    in
                        loop (new_left, new_right, next_idx, draft)
                    end
              | SOME (KeyChar c) =>
                let
                    val new_left = c :: left
                    val _ = redraw prompt new_left right
                in
                    loop (new_left, right, hist_idx, draft)
                end
              | SOME (KeyUnknown _) =>
                loop (left, right, hist_idx, draft)
    in
        loop ([], [], ~1, "")
    end

fun getIsTTY () =
    OS.Process.isSuccess (OS.Process.system "test -t 0 2>/dev/null")

fun readLine prompt history =
    let
        val isTTY = getIsTTY ()
    in
        if not isTTY then
            let
                val _ = print prompt
                val _ = TextIO.flushOut TextIO.stdOut
            in
                case TextIO.inputLine TextIO.stdIn of
                    NONE => NONE
                  | SOME line => SOME (String.implode (List.filter (fn c => c <> #"\n" andalso c <> #"\r") (String.explode line)))
            end
        else
            let
                val _ = print prompt
                val _ = TextIO.flushOut TextIO.stdOut
                val _ = OS.Process.system "stty raw -echo"
                val res = (readLineLoop prompt history) handle exn => (OS.Process.system "stty -raw echo"; raise exn)
                val _ = OS.Process.system "stty -raw echo"
            in
                res
            end
    end

fun addHistory (line, history) =
    if line = "" then
        history
    else
        case history of
            [] => [line]
          | h :: _ => if h = line then history else line :: history

fun repl (env : env, history : string list) =
    case readLine "miranda> " history of
        NONE => print "Goodbye.\n"
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
                    val env_with_std = load_script_file "stdenv.m" StringMap.empty
                    val reloaded_env = load_script_file "script.m" env_with_std
                in repl (reloaded_env, history) end
            else if is_empty line_trimmed then
                repl (env, history)
            else
                let
                    val updated_history = addHistory (line_trimmed, history)
                    val tokens = tokenize line_trimmed
                in
                    (case parse tokens of
                         ScriptBind (b as {fname, ...} : raw_binding) =>
                         let
                             val final_lambda = desugar_equations [b]
                             val updated_env = StringMap.insert (env, fname, final_lambda)
                         in
                             print ("Defined variable: " ^ fname ^ "\n");
                             repl (updated_env, updated_history)
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
                             repl (env, updated_history)
                         end)
                    handle
                        Fail msg => (print ("Lex/Parse Error: " ^ msg ^ "\n"); repl (env, updated_history))
                      | Blackhole msg => (print ("Runtime Error: " ^ msg ^ "\n"); repl (env, updated_history))
                      | RuntimeError msg => (print ("Runtime Error: " ^ msg ^ "\n"); repl (env, updated_history))
                      | exn => (print ("Error: " ^ General.exnMessage exn ^ "\n"); repl (env, updated_history))
                end
        end

fun main () =
    let
        val _ = print "==================================================\n"
        val _ = print " Environment-Sharing SML REPL                     \n"
        val _ = print " Use '/e' to edit script.m, '/q' to exit          \n"
        val _ = print "==================================================\n"
        (* val _ = CM.make "$smlnj-lib.cm" (* Force dynamic instantiation *) *)
        val env_with_std = load_script_file "stdenv.m" StringMap.empty
        val initial_env = load_script_file "script.m" env_with_std
    in
        repl (initial_env, [])
    end

val _ = main ()
