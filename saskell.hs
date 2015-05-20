{- CS 251 - Haskell is Not Not Not ML
   Su Lin Blodgett, Sara Burns, Sravanti Tekumalla

   Note: this interpreter is not the final version of our Haskell
   interpreter. This version implements error checking, but not
   through the use of Monads. Please see raskell.hs for the most
   up-to-date implementation. 
-}
{- An interpreter for a dynamically typed language that otherwise
   looks much like a subset of SML. 

   Design decisions:

     * values (the results of evaluation) are represented by a
       separate type from unevaluated Expressions, even when those
       Expressions are literals like True or "hello".  This leans on
       the type system to help ensure we do not forget to evaluate
       anything.

 -}

{- Variable symbols are represented by strings. -}
type Sym = String

{- Expressions: this is the abstract syntax of our language.
   These values encode Abstract Syntax Trees.  -}
data Expr = UnitE
              | BoolE Bool
              | IntE Int
              | StringE String
              | PlusE Expr Expr
              | MinusE Expr Expr
              | TimesE Expr Expr
              | DivE Expr Expr
              | ModE Expr Expr
              | ConcatE Expr Expr
              | LtE Expr Expr
              | GtE Expr Expr
              | LeE Expr Expr
              | GeE Expr Expr
              | EqE Expr Expr
              | NeE Expr Expr
              | NegE Expr
              | NotE Expr
              | IfThenElseE Expr Expr Expr
              | AndAlsoE Expr Expr
              | OrElseE Expr Expr
              | TupleE [Expr] 
              | ConstructorE Sym Expr
              | FnE Sym Expr
              | ApplyE Expr Expr
              | VarE Sym
              | LetE [Binding] Expr
              | CaseE Expr [(Pattern, Expr)] 
              deriving (Show, Read, Eq) 

{- For type checking -}
data Typ = UnitT
               | BoolT Typ
               | IntT Typ 
               | StringT Typ
               | TupleT [Typ]
               | TagT Sym Value 
               | ClosureT Environment (Maybe Sym) Sym Expr


{- patterns appear in Case Exprs -}
data Pattern = UnitP
                 | Wildcard
                 | VarP Sym
                 | BoolP Bool
                 | IntP Int
                 | StringP String
                 | TupleP [Pattern] 
                 | TagP Sym Pattern
                 deriving(Show, Read, Eq)



{- Fun and Val bindings appear in Let Exprs -}
data Binding = Fun Sym Sym Expr
               | Val Sym Expr
               deriving(Show, Read, Eq)

{- Values: these are not part of program syntax.  They are the results
of evaluating an Expression. -}
data Value = UnitV
               | BoolV Bool
               | IntV Int
               | StringV String
               | TupleV [Value] 
               | TagV Sym Value
               | ClosureV Environment (Maybe Sym) Sym Expr
               deriving (Show, Read, Eq) 


{-******************* IMPLEMENTATION ************************-}

{- We will build an environment-based interpreter.  Environments are
represented by association lists mapping symbols to values. -}
{- type environment = (sym * value) list -}

{- for lazy evaluation in ML, borrowed from 251 notes -}
{-}
type 'a promise = 'a option ref * (unit -> 'a)

fun delay thunk = (ref Nothing, thunk)

fun force (value, thunk) =
    case !value of
        Nothing  -> let val v = thunk ()
                    val _ = value := Just v
                in v end
      | Just v  -> v
      

type environment = (sym * (value  promise)) list
-}

type Environment = [(Sym, Value)]


{- Look up a variable in an environment.
   Raise Unbound if the variable is not bound in the environment. 

   sym -> environment -> value
-}

lookitup x [] = error "Unbound x"
lookitup x ((k, v):rest) = if k==x then v else lookitup x rest 


eval env UnitE = UnitV
eval env (BoolE b) =  BoolV b
eval env (IntE i) = IntV i
eval env (StringE s) = StringV s
eval env (NegE e) = (case (eval env e) of
                            IntV i -> IntV (-i)
                            _  -> error "TypeError")
eval env (NotE e) = (case (eval env e) of
                            BoolV b  -> BoolV (not b)
                            _  -> error "TypeError")
eval env (PlusE e1 e2) = (case ((eval env e1), (eval env e2))  of
                                 ((IntV i), (IntV j)) -> IntV (i + j)
                                 _  -> error "TypeError")
eval env (MinusE e1 e2) = (case ((eval env e1), (eval env e2)) of
                                 ((IntV i), (IntV j))  -> IntV (i - j)
                                 _  -> error "TypeError")
eval env (TimesE e1 e2) = (case ((eval env e1), (eval env e2)) of
                                 ((IntV i), (IntV j))  -> IntV (i * j)
                                 _  -> error "TypeError")
eval env (DivE e1 e2) = (case ((eval env e1), (eval env e2)) of
                                ((IntV i), (IntV j)) -> IntV (div i j)
                                _  -> error "TypeError")
eval env (ModE e1 e2) = (case ((eval env e1), (eval env e2)) of
                                ((IntV i), (IntV j)) -> IntV (mod i j)
                                _  -> error "TypeError")
eval env (LtE e1 e2) = (case ((eval env e1), (eval env e2)) of
                                ((IntV i), (IntV j)) -> BoolV (i < j)
                                _  -> error "TypeError")
eval env (GtE e1 e2) = (case ((eval env e1), (eval env e2)) of
                                ((IntV i), (IntV j)) -> BoolV (i > j)
                                _  -> error "TypeError")
eval env (LeE e1 e2) = (case ((eval env e1), (eval env e2)) of
                                ((IntV i), (IntV j)) -> BoolV (i <= j)
                                _  -> error "TypeError")
eval env (GeE e1 e2) = (case ((eval env e1), (eval env e2)) of
                                ((IntV i), (IntV j)) -> BoolV (i >= j)
                                _  -> error "TypeError")
eval env (ConcatE e1 e2) = (case ((eval env e1), (eval env e2)) of
                                ((StringV i), (StringV j))  -> StringV (i ++ j)
                                _  -> error "TypeError")
eval env (EqE e1 e2) = (BoolV ((eval env e1) == (eval env e2)))
eval env (NeE e1 e2) = (BoolV ((eval env e1) /= (eval env e2)))

eval env (IfThenElseE i t e) = (if (case (eval env i) of
                                BoolV v  -> v
                                _  -> error "TypeError")
                                then (eval env t) else (eval env e))

eval env (AndAlsoE e1 e2) = (case (eval env (IfThenElseE e1 e2 (BoolE False))) of
                                BoolV v  -> BoolV v
                                _  -> error "TypeError")

eval env (OrElseE e1 e2)  =  (case (eval env (IfThenElseE e1 (BoolE True) e2)) of
                                 BoolV v  -> BoolV v
                                 _  -> error "TypeError")

eval env (TupleE es) =  TupleV  (map (eval env) es)
eval env (ConstructorE n e) =  TagV n (eval env e)
eval env (FnE x e) =  ClosureV env Nothing x e
eval env (ApplyE e1 e2) = 
    let
        {- Evaluate e1 to a value -}
        closure = eval env e1
        {- Evaluate e2 to a value -}
        arg_value = eval env e2
    in
        {- Must have a closure, else there is a type error. -}
        (case closure of
            ClosureV closure_env (Just a) x e -> eval ((x, arg_value):((a, closure):closure_env)) e
            ClosureV closure_env Nothing x e -> eval ((x, arg_value):closure_env) e
            _  -> error "TypeError")
eval env (VarE x) =  lookitup x env


  {- let <bindings> in e end
     Evaluate bindings in order, building the environment
     in which to evaluate e. -}
         
eval env (LetE bindings e) =
    let bindhelp a b = (case (a, b) of
                        ([], env') -> env'
                        (((Val x e'):rest), env') -> bindhelp rest ((x, (eval env' e')):env') 
                        (((Fun f x e'):rest), env') -> 
                          (let 
                            closure = ClosureV env' (Just f) x e'
                           in 
                            bindhelp rest ((f, closure):env')))
    in
        eval (bindhelp bindings env) e
        

{- 

     case e of
         <pattern>  -> <Expr> 
       | <pattern>  -> <Expr>
       |  ...

     Evaluate e, then match against each pattern in order
     until a matching pattern is found, and evaluate the
     corresponding Expression in the current environment,
     extended with bindings introduced in the pattern.
 -}

	
eval env (CaseE e cases) = 
    let 
      match v p = (case (v,p) of
                    (_, Wildcard)  -> Just []
                    (v, VarP s)  -> Just [(s,v)]
                    (UnitV, UnitP)  -> Just []
                    (BoolV v, BoolP p)  -> if (v == p) then Just [] else Nothing
                    (IntV i, IntP j)  -> if (i==j) then Just [] else Nothing
                    (StringV s, StringP t)  -> if (s==t) then Just[] else Nothing
                    (TupleV vs, TupleP ps)  -> let 
                                                tuplematch (vs, ps) = (case (vs, ps) of
                                                                        (v:vs', p:ps')  -> (case match v p of
                                                                                              Just listbind  -> (case tuplematch (vs', ps') of
                                                                                                                  Just lb  ->  Just (listbind++lb)
                                                                                                                  Nothing  -> Nothing)
                                                                                              Nothing  -> Nothing)
                                                                        ([], [])  -> Just []
                                                                        _  -> Nothing)
                                              in tuplematch (vs, ps)
                    ((TagV s1 v), (TagP s2 p))  -> (case match v p of
                                                      Just listbind  -> if (s1==s2) then Just listbind else Nothing
                                                      Nothing  -> Nothing)

                    _ -> Nothing)  
      evalcase item caselist = (case (item, caselist) of
		      (item, [])  -> error "NoMatch"
		      (item, (p, e): cases')  -> (case match item p of
							Just bindlist  -> eval (bindlist++env) e
							Nothing  -> evalcase item cases'))
		    
      evaluated = eval env e
	in 
	    evalcase evaluated cases

{-typecheck helper function for tuples -}
tupletypecheck vs ts = case (vs, ts) of 
  ([], [])  -> True
  (v:vs', t:ts') -> (case (v, t) of
                      (UnitV, UnitT)  -> tupletypecheck vs' ts'
                      (IntV v, IntT t)  -> tupletypecheck vs' ts'
                      (BoolV v, BoolT t)  -> tupletypecheck vs' ts'
                      (StringV v, StringT t)  -> tupletypecheck vs' ts'
                      (TupleV vss,TupleT tss)  -> (tupletypecheck vss tss) && (tupletypecheck vs' ts')
                      _  -> False) 
			     

          
{- typecheck function -}
typecheck e t = (case ((eval [] e), t) of 
                (UnitV, UnitT)  -> True
                (IntV v, IntT t)  -> True
                (BoolV v, BoolT t)  -> True
                (StringV v, StringT t)  -> True
                (TupleV vs, TupleT ts)  -> tupletypecheck vs ts 
                _  -> error "TypeError")




{-*** Testing ***-}

factlang =
    LetE ([Fun "fact" "x"
              (IfThenElseE (LeE (VarE "x") (IntE 1))
                           (IntE 1)
                           (TimesE (VarE "x") 
                                  (ApplyE (VarE "fact")
                                         (MinusE (VarE "x") (IntE 1)))))
         ])
         (ApplyE (VarE "fact") (IntE 6))

factlang_result = eval [] factlang

{-*** Testing code from SMiLE ***-}
{-}
val thing =  Case (Bool True, [(IntP 0, String "not boolean"), (StringP "string", String "still not a boolean"), (TupleP [IntP 3, IntP 5], String "tuple not a boolean"), (BoolP True, String "boolean")])
val thing_result =   eval [] thing
 val thing2 =  Case (Tuple [Int 3, Int 5], [(IntP 0, String "not boolean"), (StringP "string", String "still not a boolean"), (TupleP [IntP 3, IntP 5], String "tuple not a boolean"), (BoolP True, String "boolean")])
val thing2_result = eval [] thing2
val shadowing = eval [("x", IntV 2)] (Case (Int 5, [(VarP "x", Times (Var "x", Var "x"))]))
val mult_bindings = eval [("x", IntV 2)] (Case (Tuple [Int 5, Int 4, Int 3], [(TupleP [VarP "a", VarP "b", VarP "c"], Minus(Times (Var "a", Var "b"), Var "c")),  (VarP "x", Times (Var "x", Var "x"))]))
-}
