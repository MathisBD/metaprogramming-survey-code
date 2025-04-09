import Lake
open Lake DSL

package «lean_derive_functor» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩
  ]

@[default_target]
lean_lib «DeriveFunctor» where
  -- add any library configuration options here
