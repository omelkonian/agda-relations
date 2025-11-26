module Class.HasInitial where

open import Class.Prelude

record HasInitial (A : Type ℓ) : Type (lsuc ℓ) where
  field Initial : A → Type
open HasInitial ⦃...⦄ public
