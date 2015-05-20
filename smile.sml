(* SMiLe Interpreter extensions
   CS 251 Final Project - Haskell is Not Not Not ML
   Su Lin Blodgett, Sara Burns, and Sravanti Tekumalla

   Note: This implmentation of SMiLe extends the assignment in 251
   by adding the promise datatype as well as the delay and force 
   functions to return a promise and to force evaluation, respectively.
   In addition, we added a typecheck function which takes a SMiLe
   expression and SMiLe type and checks to see whether the expression
   has its corresponding type. To do this, we also added a Typ datatype.
*)
(* An interpreter for a dynamically typed language that otherwise
   looks much like a subset of SML. 

   Design decisions:

     * values (the results of evaluation) are represented by a
       separate type from unevaluated expressions, even when those
       expressions are literals like true or "hello".  This leans on
       the type system to help ensure we do not forget to evaluate
       anything.

 *)

(* Variable symbols are represented by strings. *)
type sym = string

(* Expressions: this is the abstract syntax of our language.
   You can write programs in our language by constructing ML values
   of type expr.  These values encode Abstract Syntax Trees.  *)
datatype expr = Unit
              | Bool of bool
              | Int of int
              | String of string
              | Plus of expr * expr
              | Minus of expr * expr
              | Times of expr * expr
              | Div of expr * expr
              | Mod of expr * expr
              | Concat of expr * expr
              | Lt of expr * expr
              | Gt of expr * expr
              | Le of expr * expr
              | Ge of expr * expr
              | Eq of expr * expr
              | Ne of expr * expr
              | Neg of expr
              | Not of expr
              | IfThenElse of expr * expr * expr
              | AndAlso of expr * expr
              | OrElse of expr * expr
              | Tuple of expr list
              | Constructor of sym * expr
              | Fn of sym * expr
              | Apply of expr * expr
              | Var of sym
              | Let of binding list * expr
              | Case of expr * (pattern * expr) list

(* For type checking *)
    and typ = UnitT
               | BoolT of bool
               | IntT of int
               | StringT of string
               | TupleT of typ list
               (*| TagT of sym * value *)
               (*| ClosureT of (sym * value) list ref * sym * expr *)

(* patterns appear in Case exprs *)
     and pattern = UnitP
                 | Wildcard
                 | VarP of sym
                 | BoolP of bool
                 | IntP of int 
                 | StringP of string
                 | TupleP of pattern list
                 | TagP of sym * pattern

(* Fun and Val bindings appear in Let exprs *)
     and binding = Fun of sym * sym * expr
                 | Val of sym * expr

(* Values: these are not part of program syntax.  They are the results
of evaluating an expression. *)
datatype value = UnitV
               | BoolV of bool
               | IntV of int
               | StringV of string
               | TupleV of value list
               | TagV of sym * value
               | ClosureV of (sym * value) list ref * sym * expr


(******************** IMPLEMENTATION *************************)

(* We will build an environment-based interpreter.  Environments are
represented by association lists mapping symbols to values. *)
(* type environment = (sym * value) list *)

(* for lazy evaluation, borrowed from 251 notes *)
type 'a promise = 'a option ref * (unit -> 'a)

fun delay thunk = (ref NONE, thunk)

fun force (value, thunk) =
    case !value of
        NONE => let val v = thunk ()
                    val _ = value := SOME v
                in v end
      | SOME v => v

type environment = (sym * (value  promise)) list
(* Look up a variable in an environment.
   Raise Unbound if the variable is not bound in the environment. 

   sym -> environment -> value
*)
exception Unbound of sym
fun lookup x [] = raise (Unbound x)
  | lookup x ((k,v)::rest) = if k=x then v else lookup x rest

(* Raise Unimplemented where you haven't finished the interpreter
   or the given type of expression is not expected to appear at
   run time. *)
exception Unimplemented

(* Raise MoMatch when there is no match in a Case expression *)
exception NoMatch

(* Raise TypeError when an operation is applied to incompatible values *)
exception TypeError

(* Evaluate the given expression in the given environment.
   This is a recursive function.  Most expressions just continue
   to use the same environment, but some expressions evaluate their
   subexpressions in larger or different environments.

   environment -> expr -> value
*)



fun eval env Unit = delay(fn () => UnitV)
  | eval env (Bool b) = delay(fn() => BoolV b)
  | eval env (Int i) = delay(fn() => IntV i)
  | eval env (String s) = delay(fn() => StringV s)
  | eval env (Neg e) = delay(fn() => (case force(eval env e) of
                            IntV i => IntV (~i)
                          | _ => raise TypeError))
  | eval env (Not e) = delay(fn() => (case force(eval env e) of
                            BoolV b => BoolV (not b)
                          | _ => raise TypeError))
  | eval env (Plus (e1,e2)) = delay(fn() => (case (force(eval env e1), force(eval env e2)) of
                                 (IntV i, IntV j) => IntV (i + j)
                               | _ => raise TypeError))
  | eval env (Minus (e1,e2)) = delay(fn() => (case (force(eval env e1), force(eval env e2)) of
                                  (IntV i, IntV j) => IntV (i - j)
                                | _ => raise TypeError))
  | eval env (Times (e1,e2)) = delay(fn() => (case (force(eval env e1), force(eval env e2)) of
                                  (IntV i, IntV j) => IntV (i * j)
                                | _ => raise TypeError))
  | eval env (Div (e1,e2)) = delay(fn() => (case (force(eval env e1), force(eval env e2)) of
                                (IntV i, IntV j) => IntV (i div j)
                              | _ => raise TypeError))
  | eval env (Mod (e1,e2)) = delay(fn() => (case (force(eval env e1), force(eval env e2)) of
                                (IntV i, IntV j) => IntV (i mod j)
                              | _ => raise TypeError))
  | eval env (Lt (e1,e2)) = delay(fn() => (case (force(eval env e1), force(eval env e2)) of
                               (IntV i, IntV j) => BoolV (i < j)
                             | _ => raise TypeError))
  | eval env (Gt (e1,e2)) = delay(fn() => (case (force(eval env e1), force(eval env e2)) of
                               (IntV i, IntV j) => BoolV (i > j)
                             | _ => raise TypeError))
  | eval env (Le (e1,e2)) = delay(fn() => (case (force(eval env e1), force(eval env e2)) of
                               (IntV i, IntV j) => BoolV (i <= j)
                             | _ => raise TypeError))
  | eval env (Ge (e1,e2)) = delay(fn() => (case (force(eval env e1), force(eval env e2)) of
                               (IntV i, IntV j) => BoolV (i >= j)
                             | _ => raise TypeError))
  | eval env (Concat (e1,e2)) = 
    delay(fn() => (case (force(eval env e1), force(eval env e2)) of
         (StringV i, StringV j) => StringV (i ^ j)
       | _ => raise TypeError))
  | eval env (Eq (e1,e2)) = delay(fn() => BoolV ((force(eval env e1)) = (force(eval env e2))))
  | eval env (Ne (e1,e2)) = delay(fn() => BoolV ((force(eval env e1))<>(force(eval env e2))))


  (* Now the interesting parts (sample solution uses 50-60 more lines
     for the rest of eval) *)

  (* Evaluate the "if" expression, i, to value vi.
     If vi is the true value,
        the result is the evaluation of the "then" expression, t,
     else if vi is the false value,
        the result is the evaluation of the "else" expression, e,
     else if vi is any other value,
        there is a type error.

     Note that, with our current dynamically typed language,
     we do not check that the "then" and "else" expression 
     have the same result type.  Why not?
   *)
  | eval env (IfThenElse (i,t,e)) =
         delay(fn() => force(eval env (case force(eval env i) of
                  BoolV true => t
                | BoolV false => e
                | _ => raise TypeError)))

   (*Evaluate expression e1 to value v1.
     If v1 is the false value,
        the result is false,
     else if v1 is the true value,
        Evaluate e2 to v2.
        If v2 is the false value,
           the result is false,
        else if v2 is the true value,
           the result is true,
        else if v2 is any other value,
           there is a type error.
     else if v1 is any other value,
        there is a type error.
   *)
  | eval env (AndAlso (e1,e2)) =
    delay(fn() => (case force(eval env (IfThenElse (e1,e2,Bool false))) of
         BoolV v => BoolV v
       | _ => raise TypeError))


  | eval env (OrElse (e1,e2))  = delay(fn() => (case force(eval env (IfThenElse (e1,Bool true,e2))) of
                                      BoolV v => BoolV v
                                    | _ => raise TypeError))
  (* Given Tuple [e1,...,en],
     Evaluate each subexpression ei to value vi, in order.
     The result is TupleV [v1,...,vn]
     
     Feels like a familiar higher order function...
     Also note the use of a partially applied eval!
  *)
  | eval env (Tuple es) = delay(fn() => TupleV (map force (map (eval env) es)))
  (* Evaluate the subexpression to a value and produce
     a tagged version of that value. *)
  | eval env (Constructor (n,e)) = delay(fn() => TagV (n, force(eval env e)))

  (* Now for the real fun... *)
  (* Anonymous functions: fn x => e
	The evaluation of an anonymous function results in a 
	function closure. The closure includes the environment 
	in which the function was defined in, because the language
	is lexically scoped. The argument x is the argument that
	then needs to be bound to e, which is the function in the 
	expression body. ClosureV essentially conses the (x,e) tuple
	to the current enviornment to evaluate the function. 
	The environment is a reference, so that when it is used in 
	a Let expression, it can be mutated in order to support recursion. 
*)

  | eval env (Fn (x,e)) = delay(fn() => ClosureV (ref env, x, e))

  (* Function application: e1 e2
	In order to apply e1 as a function to e2, both need to be evaluated 
	to values before we can begin Apply. First, evaluate e1 to a value, 
	which creates a function closure. Then we need to evaluate e2 to a value
	which will be our argument for our function application. Now, we pattern 
	match on the first evaluated expression to ensure that e1 is a function 
	closure which can be applied to the evaluated e2, the arg value. 
	Once we verify that e1 is a function, we then evaluate the body of the 
	function in the environment which includes the binding where x is 
	bound to the result of the value of e2. 
*)
  | eval env (Apply (e1,e2)) =
    delay(fn() => 
    let
        (* Evaluate e1 to a value *)
        val closure = force(eval env e1)
        (* Evaluate e2 to a value *)
        val arg_value = force(eval env e2)
    in
        (* Must have a closure, else there is a type error. *)
        case closure of
            ClosureV (closure_env, x, e) =>
            (* After checking that e1 is a function,
		Apply e1 to e2 in closure environment
		plus binding of x to result of evaluating e2 *)
            force(eval ((x,arg_value)::(!closure_env)) e)
          | _ => raise TypeError
    end)

  (* x
     Lookup a variable in the current environment. *)
  | eval env (Var x) = delay(fn() => lookup x env)

  (* let <bindings> in e end
     Evaluate bindings in order, building the environment
     in which to evaluate e. *)     
 | eval env (Let (bindings,e)) =
    delay(fn() => 
    let fun bindhelp [] env' = env'
	   | bindhelp (Val (x, e')::rest) env' = 
	     bindhelp rest ((x, force(eval env' e'))::env')
           | bindhelp (Fun (f, x, e')::rest) env' = 
	      let
		  val closure_env_ref = ref []
		  val closure = ClosureV(closure_env_ref, x, e')
		  val new_closure_env = (f, closure)::env'
		  val _ = (closure_env_ref := new_closure_env)
	      in
		  bindhelp rest new_closure_env
	      end 
    in
        force(eval (bindhelp bindings env) e)
    end)

  (* COMPLETE THE IMPLEMENTATION OF CASE EXPRESSIONS

     case e of
         <pattern> => <expr> 
       | <pattern> => <expr>
       |  ...

     Evaluate e, then match against each pattern in order
     until a matching pattern is found, and evaluate the
     corresponding expression in the current environment,
     extended with bindings introduced in the pattern.

     This one is the most involved. *)

  | eval env (Case (e,cases)) = 
    delay(fn () => 
    let
    fun match (v,p) =
            case (v,p) of
                (_, Wildcard) => SOME []
                |(v, VarP s) => SOME [(s,v)]
                | (UnitV, UnitP) => SOME []
                | (BoolV v, BoolP p) => if v = p then SOME [] else NONE
                | (IntV i, IntP j) => if i=j then SOME [] else NONE
                | (StringV s, StringP t) => if s=t then SOME [] else NONE
                | (TupleV vs, TupleP ps) => let fun tuplematch (vs, ps)  =
                                                (case (vs, ps) of
                                                        (v::vs', p::ps') => (case match (v, p) of
                                                                                SOME listbind => (case tuplematch (vs', ps') of
                                                                                                    SOME lb =>  SOME (listbind@lb)
                                                                                                   | NONE => NONE)
                                                                                | NONE => NONE)
                                                        | ([], []) => SOME []
                                                        | _ => NONE)
                                           in tuplematch (vs, ps)
                                           end
                |(TagV (s1,v), TagP (s2, p)) => (case match (v,p) of
                                                  SOME listbind => if s1=s2 then SOME listbind else NONE
                                                 | NONE => NONE)

                | _ => NONE 
		    
	
	  fun evalcase (item, caselist) =
	     (case (item, caselist) of
		(item, []) => raise NoMatch
		| (item, (p, e):: cases') => (case match (item, p) of
							SOME bindlist => force(eval (bindlist@env) e)
							| NONE => evalcase (item, cases')))
		    
	val evaluated = force(eval env e)
	in 
	    evalcase (evaluated, cases)
	end)
 
(*typecheck helper function for tuples *)
fun tupletypecheck (vs, ts) = 
    case (vs, ts) of 
	([], []) => true
	| (v::vs', t::ts') => (case (v, t) of
			      (UnitV, UnitT) => tupletypecheck(vs', ts')
			      | (IntV v, IntT t) => tupletypecheck(vs', ts')
		              | (BoolV v, BoolT t) => tupletypecheck(vs', ts')
			      | (StringV v, StringT t) => tupletypecheck(vs', ts')
			      | (TupleV vss, TupleT tss) => tupletypecheck(vss, tss) andalso tupletypecheck(vs', ts')
			      | _ => false) 
			     
(* typecheck function *)
fun typecheck (e, t) = 
   delay(fn() => 
   case (force(eval [] e), t) of 
	(UnitV, UnitT) => true
      | (IntV v, IntT t) => true
      | (BoolV v, BoolT t) => true
      | (StringV v, StringT t) => true
      | (TupleV vs, TupleT ts) => tupletypecheck (vs, ts) 
      | _ => raise TypeError)

(**** Examples ****)
val _ = Control.Print.printDepth := 100


val factml =
    let 
        fun fact x =
            if x <= 1
            then 1
            else x * (fact (x-1))
    in
        fact 6
    end

val factlang =
    Let ([Fun ("fact", "x",
               IfThenElse (Le (Var "x", Int 1),
                           Int 1,
                           Times (Var "x", 
                                  Apply (Var "fact",
                                         Minus (Var "x", Int 1)))))
         ],
         Apply (Var "fact", Int 6))

val factlang_result = eval [] factlang

val thing =  Case (Bool true, [(IntP 0, String "not boolean"), (StringP "string", String "still not a boolean"), (TupleP [IntP 3, IntP 5], String "tuple not a boolean"), (BoolP true, String "boolean")])
val thing_result =   eval [] thing
 val thing2 =  Case (Tuple [Int 3, Int 5], [(IntP 0, String "not boolean"), (StringP "string", String "still not a boolean"), (TupleP [IntP 3, IntP 5], String "tuple not a boolean"), (BoolP true, String "boolean")])
val thing2_result = eval [] thing2
val shadowing = eval [("x", IntV 2)] (Case (Int 5, [(VarP "x", Times (Var "x", Var "x"))]))
val mult_bindings = eval [("x", IntV 2)] (Case (Tuple [Int 5, Int 4, Int 3], [(TupleP [VarP "a", VarP "b", VarP "c"], Minus(Times (Var "a", Var "b"), Var "c")),  (VarP "x", Times (Var "x", Var "x"))]))
