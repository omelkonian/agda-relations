module Relation.Prelude where

open import Class.Prelude public

variable z : A

open import Relation.Unary public
  using ()
  renaming (_⊆_ to _⊆¹_; _∩_ to _∩¹_; _∪_ to _∪¹_)
open import Relation.Binary public
  using (Transitive)

module Eq where
  open import Relation.Binary.PropositionalEquality public

module EqReasoning where
  open Eq.≡-Reasoning public
    renaming (begin_ to ≡begin_; _∎ to _≡∎)

module LeqReasoning where
  open Nat.≤-Reasoning public
    renaming (begin_ to ≤begin_; _∎ to _≤∎; begin-strict_ to <begin_)

module LP where
  open import Data.List.Properties public
