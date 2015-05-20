{- Haskell is Not Not Not ML
   CS 251 Final Project
   Su Lin Blodgett, Sara Burns, and Sravanti Tekumalla

   Note: This is the most recent and up-to-date version of
   our Haskell interpreter, and includes use of the Maybe monad
   as well as tests for laziness. 

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
               | TupleV [(Maybe Value)]
               | TagV Sym (Maybe Value)
               | ClosureV Environment (Maybe Sym) Sym Expr
               deriving (Show, Read, Eq) 


{-******************* IMPLEMENTATION ************************-}

{- We will build an environment-based interpreter.  Environments are
represented by association lists mapping symbols to values. -}
{- type environment = [(Sym, Value)] -}

type Environment = [(Sym, Value)]


{- Helper function:
   Look up a variable in an environment.
   Raise Unbound if the variable is not bound in the environment. 

   sym -> environment -> value
-}

lookitup x [] = error "Unbound x"
lookitup x ((k, v):rest) = if k==x then v else lookitup x rest 

eval env UnitE  = Just UnitV

eval env (BoolE b) = Just (BoolV b)

eval env (IntE i) = Just (IntV i)

eval env (StringE s) = Just (StringV s)

eval env (NegE e) = (case (eval env e) of
                            Just (IntV i) -> Just (IntV (-i))
                            _  -> Nothing)

eval env (NotE e) = (case (eval env e) of
                            Just (BoolV b)  -> Just (BoolV (not b))
                            _  -> Nothing)

eval env (PlusE e1 e2) = (case ((eval env e1), (eval env e2))  of
                                 ((Just (IntV i)), (Just (IntV j))) -> Just (IntV (i + j))
                                 _  -> Nothing)

eval env (MinusE e1 e2) = (case ((eval env e1), (eval env e2)) of
                                 ((Just (IntV i)), (Just (IntV j))) -> Just (IntV (i - j))
                                 _  -> Nothing)

eval env (TimesE e1 e2) = (case ((eval env e1), (eval env e2)) of
                                 ((Just (IntV  i)), (Just (IntV j)))  -> Just (IntV (i * j))
                                 _  -> Nothing)

eval env (DivE e1 e2) = (case ((eval env e1), (eval env e2)) of
                                ((Just (IntV  i)), (Just (IntV j))) -> Just (IntV (div i j))
                                _  -> Nothing)

eval env (ModE e1 e2) = (case ((eval env e1), (eval env e2)) of
                                ((Just (IntV i)), (Just (IntV j))) -> Just (IntV (mod i j))
                                _  -> Nothing)

eval env (LtE e1 e2) = (case ((eval env e1), (eval env e2)) of
                                ((Just (IntV i)), (Just (IntV j))) -> Just (BoolV (i < j))
                                _  -> Nothing)

eval env (GtE e1 e2) = (case ((eval env e1), (eval env e2)) of
                                ((Just (IntV i)), (Just (IntV j))) -> Just (BoolV (i > j))
                                _  -> Nothing)

eval env (LeE e1 e2) = (case ((eval env e1), (eval env e2)) of
                                ((Just (IntV i)), (Just (IntV j))) -> Just (BoolV (i <= j))
                                _  -> Nothing)

eval env (GeE e1 e2) = (case ((eval env e1), (eval env e2)) of
                                ((Just (IntV i)), (Just (IntV j))) -> Just (BoolV (i >= j))
                                _  -> Nothing)

eval env (ConcatE e1 e2) = (case ((eval env e1), (eval env e2)) of
                                ((Just (StringV i)), (Just (StringV j))) -> Just (StringV (i ++ j))
                                _  -> Nothing)

eval env (EqE e1 e2) = Just (BoolV ((eval env e1) == (eval env e2)))

eval env (NeE e1 e2) = Just (BoolV ((eval env e1) /= (eval env e2)))

eval env (IfThenElseE i t e) = (case (eval env i) of 
                                Just (BoolV v)  -> if v then (eval env t) else (eval env e)
                                _ -> Nothing)                              

eval env (AndAlsoE e1 e2) = (case (eval env (IfThenElseE e1 e2 (BoolE False))) of
                                Just (BoolV v)  ->  Just (BoolV v)
                                _  -> Nothing)

eval env (OrElseE e1 e2)  =  (case (eval env (IfThenElseE e1 (BoolE True) e2)) of
                                 Just (BoolV v)  -> Just (BoolV v)
                                 _  -> Nothing)

eval env (TupleE es) = Just (TupleV  (map (eval env) es))

eval env (ConstructorE n e) = Just (TagV n (eval env e))

eval env (FnE x e) = Just (ClosureV env Nothing x e)

eval env (ApplyE e1 e2) = 
    let
        {- Evaluate e1 to a value -}
        closure =  eval env e1
    in
        {- Must have a closure, else there is a type error. -}
        (case closure of --potentially would check here if the expression contains the argument before evaluating it(we force evaluation by pattern matching)
            Just (ClosureV closure_env (Just a) x e) -> (case (eval env e2) of 
                                                          (Just arg) -> eval ((x, arg):((a, (ClosureV closure_env (Just a) x e)): closure_env)) e
                                                          _ -> Nothing)
            Just (ClosureV closure_env Nothing x e) -> (case (eval env e2) of 
                                                          (Just arg) -> eval ((x, arg): closure_env) e
                                                          _ -> Nothing)
            _  -> Nothing)
eval env (VarE x) =  Just (lookitup x env)


{- let <bindings> in e end
   Evaluate bindings in order, building the environment
   in which to evaluate e. -}
         
eval env (LetE bindings e) =
    let bindhelp a b = (case (a, b) of
                        ([], env') -> env'
                        (((Val x e'):rest), env') -> (case (eval env e') of 
                                                      (Just a) -> bindhelp rest ((x, a):env')
                                                      _ -> bindhelp rest env')
                        (((Fun f x e'):rest), env') -> 
                          (let 
                            closure = ClosureV env' (Just f) x e'
                          in
                            bindhelp rest ((f, (ClosureV env' (Just f) x e')):env')))
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
                                                                        ((Just v):vs', p:ps')  -> (case match v p of
                                                                                              Just listbind  -> (case tuplematch (vs', ps') of
                                                                                                                  Just lb  ->  Just (listbind++lb)
                                                                                                                  Nothing  -> Nothing)
                                                                                              Nothing  -> Nothing)
                                                                        ([], [])  -> Just []
                                                                        _  -> Nothing)
                                              in tuplematch (vs, ps)
                    ((TagV s1 v), (TagP s2 p))  -> (case v of
                                                      Just v -> (case match v p of
                                                                  Just listbind  -> if (s1==s2) then Just listbind else Nothing
                                                                  Nothing  -> Nothing)
                                                      _ -> Nothing)

                    _ -> Nothing)  
      evalcase item caselist = (case (item, caselist) of
		      (item, [])  -> error "NoMatch"
		      (item, (p, e): cases')  -> (case match item p of
							Just bindlist  -> eval (bindlist++env) e
							Nothing  -> evalcase item cases'))
		    
      evaluated = eval env e
	in
    case evaluated of
      Just ev ->  evalcase ev cases
      _ -> Nothing

{-typecheck helper function for tuples -}
tupletypecheck vs ts = case (vs, ts) of 
  ([], [])  -> True
  ((Just v):vs', t:ts') -> (case (v, t) of
                      (UnitV, UnitT)  -> tupletypecheck vs' ts'
                      (IntV v, IntT t)  -> tupletypecheck vs' ts'
                      (BoolV v, BoolT t)  -> tupletypecheck vs' ts'
                      (StringV v, StringT t)  -> tupletypecheck vs' ts'
                      (TupleV vss,TupleT tss)  -> (tupletypecheck vss tss) && (tupletypecheck vs' ts')
                      _  -> False) 
  _ -> False
			     

          
{- typecheck function -}
typecheck e t = (case ((eval [] e), t) of 
                ((Just UnitV), UnitT)  -> Just True
                ((Just (IntV v)), IntT t)  -> Just True
                ((Just (BoolV v)), BoolT t)  -> Just True
                ((Just (StringV v)), StringT t)  -> Just True
                ((Just (TupleV vs)), TupleT ts)  -> Just (tupletypecheck vs ts)
                _  -> Nothing)

{-*** Testing ***-}

factlang =
    LetE ([Fun "fact" "x"
              --(IfThenElseE (LeE (VarE "x") (IntE 1))
              --             (IntE 1)
                           (TimesE (VarE "x") 
                                  (ApplyE (VarE "fact")
                                         (MinusE (VarE "x") (IntE 1)))), (Fun "lazy" "x" (IntE 7))
         ])
         (ApplyE (VarE "lazy") (ApplyE (VarE "fact") (IntE 7))) -- it's not lazy :(

factlang_result = eval [] factlang
{-testing laziness-}
--f = LetE ([Fun "lazy" "x" (IntE 7)]) (ApplyE (VarE "lazy") (ApplyE (FnE "x" ((TimesE (VarE "x") (MinusE (VarE "x") (IntE 1))))) (IntE 5)))
--f_result = eval [] f

