{-# OPTIONS --with-K #-}
open import Relation.Prelude
open import Relation.InferenceRules
open import Class.HasInitial

module Relation.Closure.ReflTrans.WithK
  {A : Type ℓ} ⦃ _ : HasInitial A ⦄ (_—→_ : Rel A ℓ)
  where

open import Relation.Closure.ReflTrans _—→_

Reachable-inj : ∀ {s s₀} {init init′ : Initial s₀} {tr tr′ : s ↞— s₀} →
  (Reachable s ∋ s₀ , init , tr) ≡ (s₀ , init′ , tr′)
  ───────────────────────────────────────────────────
  tr ≡ tr′
Reachable-inj refl = refl
