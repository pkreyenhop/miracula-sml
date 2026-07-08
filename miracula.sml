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
  | Mul of node * node
  | IfZero of node * node * node
  | Cons of node * node
  | Nil
  | Range of node * node
  | IfNil of node * node * node
  | MatchError
  | Closure of string * node * (node StringMap.map)
  | Thunk of thunk_state ref
  | Eq of node * node
  | Ne of node * node
  | Lt of node * node
  | Gt of node * node
  | Le of node * node
  | Ge of node * node
  | Mod of node * node
  | Tuple of node list
  | If of node * node * node
  | Append of node * node
  | ZFGenerator of parsed_pattern * qualifier list * node * node * (node StringMap.map)
  | ZF of node * qualifier list
  | Proj of int * node
  | Char of char

and parsed_pattern =
    PatInt of int
  | PatVar of string
  | PatNil
  | PatCons of parsed_pattern * parsed_pattern
  | PatTuple of parsed_pattern list
  | PatChar of char

and qualifier =
    Generator of parsed_pattern * node
  | Filter of node

type env = node StringMap.map

exception Blackhole of string
exception RuntimeError of string

(* ========================================================================== *)
(* 2. LEXER IMPLEMENTATION                                                   *)
(* ========================================================================== *)

datatype token =
    TOK_LAMBDA | TOK_DOT | TOK_DOTDOT | TOK_ARROW | TOK_ASSIGN
  | TOK_LPAREN | TOK_RPAREN | TOK_LBRACK | TOK_RBRACK | TOK_COMMA | TOK_COLON
  | TOK_SUB | TOK_ADD | TOK_MUL
  | TOK_IFZERO | TOK_THEN | TOK_ELSE
  | TOK_INT of int
  | TOK_VAR of string
  | TOK_EOF
  | TOK_PIPE | TOK_LARROW | TOK_SEMICOLON
  | TOK_EQ | TOK_NE | TOK_LT | TOK_GT | TOK_LE | TOK_GE
  | TOK_MOD | TOK_IF
  | TOK_CHAR of char | TOK_STRING of string | TOK_PP

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
                        else if c = #";"  then loop (i + 1) (TOK_SEMICOLON :: acc)
                        else if c = #"|"  then loop (i + 1) (TOK_PIPE :: acc)
                        else if c = #"<"  then
                            if i + 1 < size andalso String.sub(str, i+1) = #"-"
                            then loop (i + 2) (TOK_LARROW :: acc)
                            else if i + 1 < size andalso String.sub(str, i+1) = #"="
                            then loop (i + 2) (TOK_LE :: acc)
                            else loop (i + 1) (TOK_LT :: acc)
                        else if c = #">"  then
                            if i + 1 < size andalso String.sub(str, i+1) = #"="
                            then loop (i + 2) (TOK_GE :: acc)
                            else loop (i + 1) (TOK_GT :: acc)
                        else if c = #"="  then
                            if i + 1 < size andalso String.sub(str, i+1) = #"="
                            then loop (i + 2) (TOK_EQ :: acc)
                            else loop (i + 1) (TOK_ASSIGN :: acc)
                        else if c = #"!"  then
                            if i + 1 < size andalso String.sub(str, i+1) = #"="
                            then loop (i + 2) (TOK_NE :: acc)
                            else (print ("Lex error: char " ^ String.str c ^ "\n"); loop (i+1) acc)
                        else if c = #"*"  then loop (i + 1) (TOK_MUL :: acc)
                        else if c = #":"  then loop (i + 1) (TOK_COLON :: acc)
                        else if c = #"+"  then
                            if i + 1 < size andalso String.sub(str, i+1) = #"+"
                            then loop (i + 2) (TOK_PP :: acc)
                            else loop (i + 1) (TOK_ADD :: acc)
                        else if c = #"-"  then
                            if i + 1 < size andalso String.sub(str, i+1) = #">"
                            then loop (i + 2) (TOK_ARROW :: acc)
                            else loop (i + 1) (TOK_SUB :: acc)
                        else if c = #"'" then
                            if i + 2 < size andalso String.sub(str, i+1) <> #"\\" andalso String.sub(str, i+2) = #"'" then
                                loop (i + 3) (TOK_CHAR (String.sub(str, i+1)) :: acc)
                            else if i + 3 < size andalso String.sub(str, i+1) = #"\\" andalso String.sub(str, i+3) = #"'" then
                                let
                                    val esc = String.sub(str, i+2)
                                    val ch = case esc of
                                                 #"n" => #"\n"
                                               | #"t" => #"\t"
                                               | #"'" => #"'"
                                               | #"\\" => #"\\"
                                               | _ => esc
                                in
                                    loop (i + 4) (TOK_CHAR ch :: acc)
                                end
                            else (print "Lex error: invalid char literal\n"; loop (i+1) acc)
                        else if c = #"\"" then
                            let
                                fun readStr j s =
                                    if j >= size then (j, s)
                                    else
                                        let val c' = String.sub(str, j) in
                                            if c' = #"\"" then (j + 1, s)
                                            else if c' = #"\\" andalso j + 1 < size then
                                                let
                                                    val esc = String.sub(str, j+1)
                                                    val ch = case esc of
                                                                 #"n" => #"\n"
                                                               | #"t" => #"\t"
                                                               | #"\"" => #"\""
                                                               | #"\\" => #"\\"
                                                               | _ => esc
                                                in
                                                    readStr (j + 2) (s ^ String.str ch)
                                                end
                                            else
                                                readStr (j + 1) (s ^ String.str c')
                                        end
                                val (nextJ, s) = readStr (i + 1) ""
                            in
                                loop nextJ (TOK_STRING s :: acc)
                            end
                        else if isDigit c then
                            let
                                fun readNum j s =
                                    if j < size andalso isDigit (String.sub(str, j))
                                    then readNum (j + 1) (s ^ String.str (String.sub(str, j)))
                                    else (j, valOf (Int.fromString s))
                                val (nextJ, v) = readNum (i + 1) (String.str c)
                            in loop nextJ (TOK_INT v :: acc) end
                        else if Char.isAlpha c orelse c = #"_" then
                            let
                                fun readVar j s =
                                    if j < size andalso isAlphaNum (String.sub(str, j))
                                    then readVar (j + 1) (s ^ String.str (String.sub(str, j)))
                                    else (j, s)
                                val (nextJ, s) = readVar (i + 1) (String.str c)
                                val tok = case s of
                                              "ifzero" => TOK_IFZERO
                                            | "if"     => TOK_IF
                                            | "then"   => TOK_THEN
                                            | "else"   => TOK_ELSE
                                            | "mod"    => TOK_MOD
                                            | _        => TOK_VAR s
                            in loop nextJ (tok :: acc) end
                        else (print ("Lex error: char " ^ String.str c ^ "\n"); loop (i+1) acc)
                    end
        in loop 0 [] end
end

(* ========================================================================== *)
(* 3. PARSER MECHANICS                                                       *)
(* ========================================================================== *)

(* parsed_pattern is now defined with node *)

type raw_binding = { fname: string, pats: parsed_pattern list, body: node }
datatype stmt = ScriptBind of raw_binding | REPLEval of node

fun parse tokens =
    let
        val toks = ref tokens
        fun peek () = List.hd (!toks)
        fun consume () = toks := List.tl (!toks)
        fun peek2 () =
            case !toks of
                _ :: t :: _ => SOME t
              | _ => NONE
        fun peek3 () =
            case !toks of
                _ :: _ :: t :: _ => SOME t
              | _ => NONE

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
              | TOK_IF =>
                (consume ();
                 let
                     val cond = parse_expr ()
                     val _ = if peek () <> TOK_THEN then raise Fail "Expected 'then'" else consume ()
                     val t_branch = parse_expr ()
                     val _ = if peek () <> TOK_ELSE then raise Fail "Expected 'else'" else consume ()
                     val f_branch = parse_expr ()
                 in If (cond, t_branch, f_branch) end)
              | _ => parse_cons ()

        and parse_cons () =
            let val left = parse_pp () in
                case peek () of
                    TOK_COLON => (consume (); Cons (left, parse_cons ()))
                  | _ => left
            end

        and parse_pp () =
            let val left = parse_comp () in
                case peek () of
                    TOK_PP => (consume (); Append (left, parse_pp ()))
                  | _ => left
            end

        and parse_comp () =
            let val left = parse_add_sub () in
                case peek () of
                    TOK_EQ => (consume (); Eq (left, parse_add_sub ()))
                  | TOK_NE => (consume (); Ne (left, parse_add_sub ()))
                  | TOK_LT => (consume (); Lt (left, parse_add_sub ()))
                  | TOK_GT => (consume (); Gt (left, parse_add_sub ()))
                  | TOK_LE => (consume (); Le (left, parse_add_sub ()))
                  | TOK_GE => (consume (); Ge (left, parse_add_sub ()))
                  | _ => left
            end

        and parse_add_sub () =
            let fun loop left =
                case peek () of
                    TOK_ADD => (consume (); loop (Add (left, parse_mod ())))
                  | TOK_SUB => (consume (); loop (Sub (left, parse_mod ())))
                  | _ => left
            in loop (parse_mod ()) end

        and parse_mod () =
            let val left = parse_app () in
                case peek () of
                    TOK_MOD => (consume (); Mod (left, parse_app ()))
                  | TOK_MUL => (consume (); Mul (left, parse_app ()))
                  | _ => left
            end

        and parse_app () =
            let fun loop left =
                case peek () of
                    TOK_INT _ => loop (App (left, parse_atom ()))
                  | TOK_CHAR _ => loop (App (left, parse_atom ()))
                  | TOK_STRING _ => loop (App (left, parse_atom ()))
                  | TOK_VAR _ => loop (App (left, parse_atom ()))
                  | TOK_LPAREN => loop (App (left, parse_atom ()))
                  | TOK_LBRACK => loop (App (left, parse_atom ()))
                  | _ => left
            in loop (parse_atom ()) end

        and parse_atom () =
            case peek () of
                TOK_INT n => (consume (); Int n)
              | TOK_CHAR c => (consume (); Char c)
              | TOK_STRING s =>
                let
                    fun make_list [] = Nil
                      | make_list (c :: cs) = Cons (Char c, make_list cs)
                in
                    consume ();
                    make_list (String.explode s)
                end
              | TOK_VAR x => (consume (); Var x)
              | TOK_LPAREN =>
                if peek2 () = SOME TOK_COLON then
                    if peek3 () = SOME TOK_RPAREN then
                        (consume (); consume (); consume ();
                         Lam ("x", Lam ("y", Cons (Var "x", Var "y"))))
                    else
                        (consume (); consume ();
                         let val e = parse_expr () in
                             if peek () <> TOK_RPAREN then raise Fail "Expected ')'" else ();
                             consume ();
                             Lam ("x", Cons (Var "x", e))
                         end)
                else if peek2 () = SOME TOK_ADD then
                    if peek3 () = SOME TOK_RPAREN then
                        (consume (); consume (); consume ();
                         Lam ("x", Lam ("y", Add (Var "x", Var "y"))))
                    else
                        (consume (); consume ();
                         let val e = parse_expr () in
                             if peek () <> TOK_RPAREN then raise Fail "Expected ')'" else ();
                             consume ();
                             Lam ("x", Add (Var "x", e))
                         end)
                else if peek2 () = SOME TOK_SUB then
                    if peek3 () = SOME TOK_RPAREN then
                        (consume (); consume (); consume ();
                         Lam ("x", Lam ("y", Sub (Var "x", Var "y"))))
                    else
                        (consume (); consume ();
                         let val e = parse_expr () in
                             if peek () <> TOK_RPAREN then raise Fail "Expected ')'" else ();
                             consume ();
                             Lam ("x", Sub (Var "x", e))
                         end)
                else
                    (consume ();
                     let
                         fun parse_tuple_elms acc =
                             let val e = parse_expr () in
                                 case peek () of
                                     TOK_COMMA => (consume (); parse_tuple_elms (e :: acc))
                                   | TOK_RPAREN => (consume (); List.rev (e :: acc))
                                   | _ => raise Fail "Expected ',' or ')' inside tuple"
                             end
                         val first = parse_expr ()
                     in
                         if peek () = TOK_COMMA then
                             (consume ();
                              Tuple (parse_tuple_elms [first]))
                         else
                             (if peek () <> TOK_RPAREN then raise Fail "Expected ')'" else ();
                              consume ();
                              first)
                     end)
              | TOK_LBRACK => (consume (); parse_list_elements ())
              | _ => raise Fail "Unexpected token inside atom expression"

        and parse_list_elements () =
            if peek () = TOK_RBRACK then (consume (); Nil)
            else
                let val head = parse_expr () in
                    if peek () = TOK_PIPE then
                        (consume ();
                         let
                             fun has_larrow () =
                                 let
                                     fun check [] = false
                                       | check (TOK_SEMICOLON :: _) = false
                                       | check (TOK_RBRACK :: _) = false
                                       | check (TOK_LARROW :: _) = true
                                       | check (_ :: rest) = check rest
                                 in
                                     check (!toks)
                                 end
                             fun parse_qualifiers () =
                                 let
                                     val q = if has_larrow () then
                                                 let
                                                     val pat = parse_pattern ()
                                                     val _ = if peek () <> TOK_LARROW then raise Fail "Expected '<-'" else consume ()
                                                     val src = parse_expr ()
                                                 in
                                                     Generator (pat, src)
                                                 end
                                             else
                                                 Filter (parse_expr ())
                                 in
                                     case peek () of
                                         TOK_SEMICOLON => (consume (); q :: parse_qualifiers ())
                                       | TOK_RBRACK => (consume (); [q])
                                       | _ => raise Fail "Expected ';' or ']' in qualifiers"
                                 end
                             val quals = parse_qualifiers ()
                         in
                             ZF (head, quals)
                         end)
                    else if peek () = TOK_DOTDOT then
                        (consume ();
                         let val tail_expr = parse_expr () in
                             if peek () <> TOK_RBRACK then raise Fail "Expected ']' after range expression" else ();
                             consume ();
                             Range (head, tail_expr)
                         end)
                    else if peek () = TOK_COMMA then (consume (); Cons (head, parse_list_elements ()))
                    else if peek () = TOK_RBRACK then (consume (); Cons (head, Nil))
                    else raise Fail "Expected '|', '..', ',', or ']' in list expression"
                end

        and is_assignment ts =
            let fun check [] = false
                  | check (TOK_ASSIGN :: _) = true
                  | check (_ :: rest) = check rest
            in check ts end

        and parse_pattern () =
            case peek () of
                TOK_INT n => (consume (); PatInt n)
              | TOK_CHAR c => (consume (); PatChar c)
              | TOK_VAR x => (consume (); PatVar x)
              | TOK_LBRACK =>
                (consume ();
                 if peek () = TOK_RBRACK then (consume (); PatNil)
                 else raise Fail "Only empty list pattern '[]' is supported directly")
              | TOK_LPAREN =>
                (consume ();
                 let
                     fun parse_tuple_pats acc =
                         let val p = parse_pattern_cons () in
                             case peek () of
                                 TOK_COMMA => (consume (); parse_tuple_pats (p :: acc))
                               | TOK_RPAREN => (consume (); List.rev (p :: acc))
                               | _ => raise Fail "Expected ',' or ')' inside tuple pattern"
                         end
                     val first = parse_pattern_cons ()
                 in
                     if peek () = TOK_COMMA then
                         (consume ();
                          PatTuple (parse_tuple_pats [first]))
                     else
                         (if peek () <> TOK_RPAREN then raise Fail "Expected ')' in pattern" else ();
                          consume ();
                          first)
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

fun match_pattern env pat node =
    case (pat, whnf env node) of
        (PatInt n1, Int n2) => if n1 = n2 then SOME StringMap.empty else NONE
      | (PatChar c1, Char c2) => if c1 = c2 then SOME StringMap.empty else NONE
      | (PatVar "_", _) => SOME StringMap.empty
      | (PatVar x, v) => SOME (StringMap.singleton (x, v))
      | (PatNil, Nil) => SOME StringMap.empty
      | (PatCons (p1, p2), Cons (h, t)) =>
        (case (match_pattern env p1 h, match_pattern env p2 t) of
             (SOME m1, SOME m2) => SOME (StringMap.unionWith (fn (v1, v2) => v2) (m1, m2))
           | _ => NONE)
      | (PatTuple pats, Tuple nodes) =>
        if List.length pats = List.length nodes then
            let
                fun match_list [] [] acc = SOME acc
                  | match_list (p::ps) (n::ns) acc =
                    (case match_pattern env p n of
                         SOME m => match_list ps ns (StringMap.unionWith (fn (v1, v2) => v2) (acc, m))
                       | NONE => NONE)
                  | match_list _ _ _ = NONE
            in
                match_list pats nodes StringMap.empty
            end
        else NONE
      | _ => NONE

and eval_zf env body_expr qualifiers =
    case qualifiers of
        [] =>
        let
            fun needs_thunk (Int _) = false
              | needs_thunk (Char _) = false
              | needs_thunk Nil = false
              | needs_thunk (Thunk _) = false
              | needs_thunk (Closure _) = false
              | needs_thunk (Lam _) = false
              | needs_thunk MatchError = false
              | needs_thunk _ = true
            val h = if needs_thunk body_expr then Thunk (ref (Unevaluated (body_expr, env))) else body_expr
        in
            Cons (h, Nil)
        end
      | Filter cond :: rest =>
        let
            val cond' = Thunk (ref (Unevaluated (cond, env)))
        in
            If (cond', eval_zf env body_expr rest, Nil)
        end
      | Generator (pat, src) :: rest =>
        ZFGenerator (pat, rest, src, body_expr, env)

and whnf (env : env) (n : node) : node =
    case n of
        Int n => Int n
      | Char c => Char c
      | Lam (x, body) => Closure (x, body, env)
      | Closure (x, body, closure_env) => Closure (x, body, closure_env)
      | Cons (h, t) =>
        let
            fun needs_thunk (Int _) = false
              | needs_thunk (Char _) = false
              | needs_thunk Nil = false
              | needs_thunk (Thunk _) = false
              | needs_thunk (Closure _) = false
              | needs_thunk (Lam _) = false
              | needs_thunk (Cons _) = false
              | needs_thunk (Tuple _) = false
              | needs_thunk MatchError = false
              | needs_thunk _ = true
            val h' = if needs_thunk h then Thunk (ref (Unevaluated (h, env))) else h
            val t' = if needs_thunk t then Thunk (ref (Unevaluated (t, env))) else t
        in
            Cons (h', t')
        end
      | Nil => Nil
      | Eq (e1, e2) =>
        (case (whnf env e1, whnf env e2) of
             (Int n1, Int n2) => if n1 = n2 then Int 1 else Int 0
           | (Char c1, Char c2) => if c1 = c2 then Int 1 else Int 0
           | _ => raise RuntimeError "Equality expects integers or characters")
      | Ne (e1, e2) =>
        (case (whnf env e1, whnf env e2) of
             (Int n1, Int n2) => if n1 <> n2 then Int 1 else Int 0
           | _ => raise RuntimeError "Inequality expects integers")
      | Lt (e1, e2) =>
        (case (whnf env e1, whnf env e2) of
             (Int n1, Int n2) => if n1 < n2 then Int 1 else Int 0
           | _ => raise RuntimeError "Less-than expects integers")
      | Gt (e1, e2) =>
        (case (whnf env e1, whnf env e2) of
             (Int n1, Int n2) => if n1 > n2 then Int 1 else Int 0
           | _ => raise RuntimeError "Greater-than expects integers")
      | Le (e1, e2) =>
        (case (whnf env e1, whnf env e2) of
             (Int n1, Int n2) => if n1 <= n2 then Int 1 else Int 0
           | _ => raise RuntimeError "Less-than-or-equal expects integers")
      | Ge (e1, e2) =>
        (case (whnf env e1, whnf env e2) of
             (Int n1, Int n2) => if n1 >= n2 then Int 1 else Int 0
           | _ => raise RuntimeError "Greater-than-or-equal expects integers")
      | Mod (e1, e2) =>
        (case (whnf env e1, whnf env e2) of
             (Int n1, Int n2) => Int (n1 mod n2)
           | _ => raise RuntimeError "Modulo expects integers")
      | Tuple elms =>
        let
            fun needs_thunk (Int _) = false
              | needs_thunk (Char _) = false
              | needs_thunk Nil = false
              | needs_thunk (Thunk _) = false
              | needs_thunk (Closure _) = false
              | needs_thunk (Lam _) = false
              | needs_thunk (Cons _) = false
              | needs_thunk (Tuple _) = false
              | needs_thunk MatchError = false
              | needs_thunk _ = true
            val elms' = List.map (fn e => if needs_thunk e then Thunk (ref (Unevaluated (e, env))) else e) elms
        in
            Tuple elms'
        end
      | If (cond, t_branch, f_branch) =>
        (case whnf env cond of
             Int 0 => whnf env f_branch
           | Int _ => whnf env t_branch
           | _ => raise RuntimeError "If condition must be an integer")
      | Append (e1, e2) =>
        (case whnf env e1 of
             Nil => whnf env e2
           | Cons (h, t) =>
             let
                 val t' = Thunk (ref (Unevaluated (Append (t, e2), env)))
             in
                 Cons (h, t')
             end
           | _ => raise RuntimeError "Append expects lists")
      | ZF (body_expr, qualifiers) =>
        whnf env (eval_zf env body_expr qualifiers)
      | ZFGenerator (pat, rest, current_list, body_expr, zf_env) =>
        (case whnf zf_env current_list of
             Nil => Nil
           | Cons (h, t) =>
             let
                 val match_res = match_pattern zf_env pat h
                 val next_gen = ZFGenerator (pat, rest, t, body_expr, zf_env)
             in
                 case match_res of
                     SOME bindings =>
                     let
                          val extended_env = StringMap.foldli (fn (k, v, acc) => StringMap.insert (acc, k, v)) zf_env bindings
                          val first_list = eval_zf extended_env body_expr rest
                     in
                         whnf env (Append (first_list, next_gen))
                     end
                   | NONE => whnf env next_gen
             end
             | _ => raise RuntimeError "Generator source must be a list")
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
      | Mul (e1, e2) =>
        (case (whnf env e1, whnf env e2) of
             (Int n1, Int n2) => Int (n1 * n2)
           | _ => raise RuntimeError "Multiplication expects integers")
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
      | Proj (i, tpl) =>
        (case whnf env tpl of
             Tuple elms => whnf env (List.nth (elms, i))
           | _ => raise RuntimeError "Proj expects a tuple")
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
      | Mul (e1, e2) => "(" ^ print_node env e1 ^ " * " ^ print_node env e2 ^ ")"
      | Eq (e1, e2) => "(" ^ print_node env e1 ^ " == " ^ print_node env e2 ^ ")"
      | Ne (e1, e2) => "(" ^ print_node env e1 ^ " != " ^ print_node env e2 ^ ")"
      | Lt (e1, e2) => "(" ^ print_node env e1 ^ " < " ^ print_node env e2 ^ ")"
      | Gt (e1, e2) => "(" ^ print_node env e1 ^ " > " ^ print_node env e2 ^ ")"
      | Le (e1, e2) => "(" ^ print_node env e1 ^ " <= " ^ print_node env e2 ^ ")"
      | Ge (e1, e2) => "(" ^ print_node env e1 ^ " >= " ^ print_node env e2 ^ ")"
      | Mod (e1, e2) => "(" ^ print_node env e1 ^ " mod " ^ print_node env e2 ^ ")"
      | Tuple elms => "(" ^ String.concatWith "," (List.map (fn e => print_node env (whnf env e)) elms) ^ ")"
      | IfZero _ => "<conditional>"
      | If _ => "<conditional>"
      | IfNil _ => "<conditional-nil>"
      | Append _ => "<append>"
      | ZF _ => "<zf-comprehension>"
      | ZFGenerator _ => "<zf-generator>"
      | MatchError => "<match-error>"
      | Thunk _ => "<thunk>"
      | Range (e1, e2) => "[" ^ print_node env e1 ^ ".." ^ print_node env e2 ^ "]"
      | Char c =>
        let
            fun escape ch =
                if ch = #"\n" then "\\n"
                else if ch = #"\t" then "\\t"
                else if ch = #"'" then "\\'"
                else if ch = #"\\" then "\\\\"
                else String.str ch
        in
            "'" ^ escape c ^ "'"
        end
      | Nil => "[]"
      | Cons _ =>
        let
            fun check_string current acc =
                case whnf env current of
                    Nil => SOME (String.implode (List.rev acc))
                  | Cons (h, t) =>
                    (case whnf env h of
                         Char c => check_string t (c :: acc)
                       | _ => NONE)
                  | _ => NONE
        in
            case check_string node [] of
                SOME "" => "[]"
              | SOME s =>
                let
                    fun escape ch =
                        if ch = #"\n" then "\\n"
                        else if ch = #"\t" then "\\t"
                        else if ch = #"\"" then "\\\""
                        else if ch = #"\\" then "\\\\"
                        else String.str ch
                in
                    "\"" ^ String.translate escape s ^ "\""
                end
              | NONE =>
                let
                    fun collect elements current =
                        case whnf env current of
                            Cons (h, t) => collect (print_node env (whnf env h) :: elements) t
                          | Nil => List.rev elements
                          | rest => List.rev (print_node env (whnf env rest) :: elements)
                in
                    "[" ^ String.concatWith "," (collect [] node) ^ "]"
                end
        end
      | Proj (i, _) => "<projection-" ^ Int.toString i ^ ">"

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
                           | PatChar target_val =>
                             IfZero (Sub (Eq (Var p, Char target_val), Int 1), check_pats p_rest pat_rest tree_body, build_decision_tree rest)
                           | PatVar binding_name =>
                             let val substituted_body = 
                                     if binding_name = p then tree_body
                                     else App (Lam (binding_name, tree_body), Var p)
                             in check_pats p_rest pat_rest substituted_body end
                           | PatTuple tuple_pats =>
                             let
                                 val elms_vars = List.tabulate (List.length tuple_pats, fn i => new_var_name ("t" ^ Int.toString i))
                                 val inner_body = check_pats (elms_vars @ p_rest) (tuple_pats @ pat_rest) tree_body
                                 fun wrap_projs [] _ body = body
                                   | wrap_projs (var :: rest_vars) i body =
                                     App (Lam (var, wrap_projs rest_vars (i+1) body), Proj (i, Var p))
                             in
                                 wrap_projs elms_vars 0 inner_body
                             end
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
      | Char c => "Char '" ^ String.str c ^ "'"
      | Var x => "Var " ^ x
      | Lam (x, body) => "Lam (" ^ x ^ ", " ^ print_ast body ^ ")"
      | Closure (x, body, _) => "Closure (" ^ x ^ ", " ^ print_ast body ^ ")"
      | App (e1, e2) => "App (" ^ print_ast e1 ^ ", " ^ print_ast e2 ^ ")"
      | Sub (e1, e2) => "Sub (" ^ print_ast e1 ^ ", " ^ print_ast e2 ^ ")"
      | Add (e1, e2) => "Add (" ^ print_ast e1 ^ ", " ^ print_ast e2 ^ ")"
      | Mul (e1, e2) => "Mul (" ^ print_ast e1 ^ ", " ^ print_ast e2 ^ ")"
      | IfZero (c, t, f) => "IfZero (" ^ print_ast c ^ ", " ^ print_ast t ^ ", " ^ print_ast f ^ ")"
      | IfNil (c, t, f) => "IfNil (" ^ print_ast c ^ ", " ^ print_ast t ^ ", " ^ print_ast f ^ ")"
      | MatchError => "MatchError"
      | Nil => "Nil"
      | Cons (h, t) => "Cons (" ^ print_ast h ^ ", " ^ print_ast t ^ ")"
      | Range (e1, e2) => "Range (" ^ print_ast e1 ^ ", " ^ print_ast e2 ^ ")"
      | Thunk _ => "Thunk"
      | Eq (e1, e2) => "Eq (" ^ print_ast e1 ^ ", " ^ print_ast e2 ^ ")"
      | Ne (e1, e2) => "Ne (" ^ print_ast e1 ^ ", " ^ print_ast e2 ^ ")"
      | Lt (e1, e2) => "Lt (" ^ print_ast e1 ^ ", " ^ print_ast e2 ^ ")"
      | Gt (e1, e2) => "Gt (" ^ print_ast e1 ^ ", " ^ print_ast e2 ^ ")"
      | Le (e1, e2) => "Le (" ^ print_ast e1 ^ ", " ^ print_ast e2 ^ ")"
      | Ge (e1, e2) => "Ge (" ^ print_ast e1 ^ ", " ^ print_ast e2 ^ ")"
      | Mod (e1, e2) => "Mod (" ^ print_ast e1 ^ ", " ^ print_ast e2 ^ ")"
      | Tuple elms => "Tuple [" ^ String.concatWith "," (List.map print_ast elms) ^ "]"
      | If (c, t, f) => "If (" ^ print_ast c ^ ", " ^ print_ast t ^ ", " ^ print_ast f ^ ")"
      | Append (e1, e2) => "Append (" ^ print_ast e1 ^ ", " ^ print_ast e2 ^ ")"
      | ZF (body, quals) => "ZF (" ^ print_ast body ^ ")"
      | ZFGenerator _ => "ZFGenerator"
      | Proj (i, e) => "Proj (" ^ Int.toString i ^ ", " ^ print_ast e ^ ")"

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
