module DeriveFunctor where

open import Level using (Level)
open import Relation.Nullary
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Maybe hiding (_>>=_)
open import Data.String as String hiding (_++_)
open import Data.List as List
open import Data.Product
open import Agda.Builtin.Sigma
open import Relation.Binary.PropositionalEquality as Eq hiding ([_])
open import Function.Base
open import Agda.Builtin.Reflection
open import Reflection hiding (_>>=_; _>>_)
open import Reflection.AST.AlphaEquality using (_=α=_)
open import Reflection.AST.DeBruijn using (weaken; _∈FV_)
open import Class.Functor
open import Class.Monad

-- Print a message from the TC monad.
-- Error parts are concatenated and a newline is automatically added at the end.
printTC : List ErrorPart -> TC ⊤
printTC parts = debugPrint "" 10 parts

-- A small record to hold the de Bruijn indices of the inputs of [fmap].
record Inputs : Set where
  field 
    a b A B f : ℕ

-- [lift-inputs n inp] adds [n] to all de Bruijn indices in the inputs [inp].
lift-inputs : ℕ -> Inputs -> Inputs
lift-inputs n inp = 
  record { a = n + Inputs.a inp 
         ; b = n + Inputs.b inp 
         ; A = n + Inputs.A inp 
         ; B = n + Inputs.B inp 
         ; f = n + Inputs.f inp }

-- [pi-telescope t] peels off all the outer products of term [t],
-- and returns the telescope of domains along with the final codomain
-- (which is guaranteed to not be itself a product).
pi-telescope : Term -> Telescope × Term
pi-telescope (pi a (abs na b)) = 
  let (tele , t) = pi-telescope b in
  ((na , a) ∷ tele , t)
pi-telescope t = ([] , t)

-- Map [f] over an argument with index [i] and type [arg-ty].
build-arg : Inputs -> Name -> ℕ -> Arg Type -> TC (Arg Term)
build-arg inp ind i (arg info arg-ty) =
  if arg-ty =α= var (Inputs.A inp) [] then
    -- Simply apply [f].
    (printTC [ strErr "- apply f" ] >> 
    return (arg info $ var (Inputs.f inp) [ vArg $ var i [] ]))
  else
    -- Return the argument unchanged.
    (printTC (strErr "arg-ty :" ∷ termErr arg-ty ∷ []) >>
    printTC [ strErr "- don't apply f" ] >> 
    return (arg info $ var i []))
  
  
  --else 
  --  -- We don't support other cases yet.
  --  typeError [ strErr "build-arg: unsupported argument type" ]

build-clause : Name -> Name -> TC Clause
build-clause ind ctor = do
  printTC (strErr "build-clause for " ∷ nameErr ctor ∷ [])
  -- Bind the input arguments.
  let inp = record { a = 4 ; b = 3 ; A = 2 ; B = 1 ; f = 0 }
      inp-tele = 
        ("a" , hArg (quoteTerm Level)) ∷
        ("b" , hArg (quoteTerm Level)) ∷
        ("A" , hArg (agda-sort $ Sort.set $ var 1 [])) ∷
        ("B" , hArg (agda-sort $ Sort.set $ var 1 [])) ∷
        ("f" , vArg (pi (vArg $ var 1 []) $ abs "_" $ var 1 [])) ∷
        []
  inContext (List.reverse inp-tele) $ do
    -- Fetch the type of the constructor at parameter [A].
    ctor-ty <- inferType (con ctor (hArg (var (Inputs.a inp) []) ∷ hArg (var (Inputs.A inp) []) ∷ []))
    -- Get the types of the arguments of the constructor.
    let (args-tele , _) = pi-telescope ctor-ty
        n-args = List.length args-tele
    inContext (List.reverse $ inp-tele ++ args-tele) $ do
      let inp = lift-inputs n-args inp
      -- Transform each argument as needed.
      mapped-args <- 
        mapM (\(i , (_ , ty)) -> build-arg inp ind i $ fmap (weaken (i + 1)) ty)  
          (List.zip (downFrom n-args) args-tele)
      -- Build the clause.
      let args-patt = 
            List.zipWith 
              (\{ (_ , arg info _) i -> arg info (Pattern.var i) }) 
              args-tele 
              (downFrom n-args)
          patt = 
            hArg (Pattern.var $ Inputs.a inp) ∷
            hArg (Pattern.var $ Inputs.b inp) ∷
            hArg (Pattern.var $ Inputs.A inp) ∷
            hArg (Pattern.var $ Inputs.B inp) ∷
            vArg (Pattern.var $ Inputs.f inp) ∷
            vArg (Pattern.con ctor args-patt) ∷
            []
      let body = con ctor (hArg (var (Inputs.b inp) []) ∷ hArg (var (Inputs.B inp) []) ∷ mapped-args)
          clause = Clause.clause (inp-tele ++ args-tele) patt body
      return clause
  
build-fmap : Name -> TC (List Clause)
build-fmap ind = do
  ind-def <- getDefinition ind
  ctors <- 
    case ind-def of \
    { (data-type npars ctors) -> return ctors
    ; _ -> typeError $ strErr "The constant" ∷ nameErr ind ∷ strErr "is not a data-type." ∷ []   
    }
  mapM (build-clause ind) ctors
  
build-fmap-ty : Name -> Type
build-fmap-ty ind =
  pi (hArg $ quoteTerm Level) $ abs "a" $ 
  pi (hArg $ quoteTerm Level) $ abs "b" $ 
  pi (hArg $ agda-sort $ Sort.set $ var 1 []) $ abs "A" $ 
  pi (hArg $ agda-sort $ Sort.set $ var 1 []) $ abs "B" $ 
  pi (vArg $ pi (vArg $ var 1 []) (abs "_" $ var 1 [])) $ abs "f" $
  pi (vArg $ def ind [ vArg $ var 2 [] ]) $ abs "_" $
  def ind [ vArg $ var 2 [] ]
             
derive-functor : Name -> Name -> TC ⊤
derive-functor fmap ind = do
  declareDef (vArg fmap) (build-fmap-ty ind)
  clauses <- build-fmap ind
  defineFun fmap clauses

unquoteDecl maybe-fmap = derive-functor maybe-fmap (quote Maybe)
   