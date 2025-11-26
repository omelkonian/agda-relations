module Relation.Prelude where

open import Class.Prelude public

variable {- x y -} z x′ y′ z′ : A

module Product where
  open import Data.Product public

open import Relation.Nullary public
  using (True; toWitness)
open import Relation.Unary public
  using ()
  renaming (_⇒_ to _⇒¹_; _⊆_ to _⊆¹_; _∩_ to _∩¹_; _∪_ to _∪¹_)
open import Relation.Binary public
  using (Transitive; Trans)
  -- ( REL; Rel; Reflexive; Irreflexive; Symmetric; Antisymmetric
  -- ; Trans; Transitive; Total; DecidableEquality; IsEquivalence; Setoid
  -- ; _⟶_Respects_; _Respects_; _Respectsʳ_; _Respectsˡ_; _Respects₂_
  -- )
  renaming (_⇒_ to _⇒²_; _⇔_ to _⇔²_)

Rel₀ : Type ℓ → Type _
Rel₀ A = Rel A 0ℓ

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

-- iff
_↔_ : Type ℓ → Type ℓ′ → Type (ℓ ⊔ ℓ′)
A ↔ B = (A → B) × (B → A)
