module Relation.Closure.Core where

open import Relation.Prelude

-- ****************************
-- [RECOMMENDED] infix -1 _—→_
-- ****************************

-- labelled relations
LRel : Type ℓ × Type → (ℓ′ : Level) → Type (ℓ ⊔ lsuc ℓ′)
LRel (A , L) ℓ = A → L → A → Type ℓ

LRel₀ : Type ℓ × Type → Type _
LRel₀ (A , L) = LRel (A , L) 0ℓ

private variable L : Type

unlabel : LRel (A , L) ℓ′ → Rel A ℓ′
unlabel _—→[_]_ x y = ∃ λ α → x —→[ α ] y

infix 0 emitting_∶_ emit∶_

emitting_∶_ : ∀ {B : Pred A ℓ′} → (x : A) → B x → Σ A B
emitting_∶_ = _,_
emit∶_ = -,_

-- transitive operations
TransitiveOp : Rel A ℓ → Type _
TransitiveOp _~_ = ∀ x {y z} → x ~ y → y ~ z → x ~ z

mkTransitiveOp : ∀ {_~_ : Rel A ℓ} → Transitive _~_ → TransitiveOp _~_
mkTransitiveOp trans _ = trans
