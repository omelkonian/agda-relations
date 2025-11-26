module Test.Relation.Closure where

open import Relation.Prelude
open import Relation.Closure.Core

module _ where

  infix -1 _—→_
  data _—→_ : Rel₀ ℕ where
    [inc] : n —→ suc n
    [dec] : suc n —→ n

  open import Relation.Closure.ReflTrans _—→_

  _ : 10 —↠ 10
  _ = begin 10 ∎

  _ : 10 —↠⁺ 12
  _ = begin
    10 —→⟨ [inc] ⟩
    11 —→⟨ [dec] ⟩
    10 —→⟨ [inc] ⟩
    11 —→⟨ [inc] ⟩
    12 ∎

  _ : 12 ⁺↞— 10
  _ = begin
    12 ⟨ [inc] ⟩←—
    11 ⟨ [inc] ⟩←—
    10 ⟨ [dec] ⟩←—
    11 ⟨ [inc] ⟩←—
    10 ∎

infix -1 _—[_]→_
data _—[_]→_ : LRel₀ (ℕ , String) where
  [inc] : n —[ "inc" ]→ suc n
  [dec] : suc n —[ "dec" ]→ n

module _ where
  open import Relation.Closure.LReflTrans _—[_]→_

  _ : 10 —[ [] ]↠ 10
  _ = begin 10 ∎

  _ : 10 —↠ 10
  _ = emit∶ begin 10 ∎

  _ : 10 —↠ 10
  _ = emitting [] ∶ begin 10 ∎

  _ : 10 —↠⁺ 12
  _ = emitting ("inc" ∷ "dec" ∷ "inc" ∷ "inc" ∷ []) ∶
      begin 10 —→⟨ [inc] ⟩
            11 —→⟨ [dec] ⟩
            10 —→⟨ [inc] ⟩
            11 —→⟨ [inc] ⟩
            12 ∎

  _ : 12 ⁺↞— 10
  _ = emitting ("inc" ∷ "dec" ∷ "inc" ∷ "inc" ∷ []) ∶
      begin 12 ⟨ [inc] ⟩←—
            11 ⟨ [inc] ⟩←—
            10 ⟨ [dec] ⟩←—
            11 ⟨ [inc] ⟩←—
            10 ∎

module _ where

  open import Class.Setoid

  instance
    Setoidℕ : ISetoid ℕ
    Setoidℕ = λ where
      .relℓ → _
      ._≈_  → _≡_

  open import Relation.Closure.UpTo.LReflTrans _—[_]→_

  _ : 10 —[ [] ]↠ 10
  _ = begin 10 ∎

  _ : 10 —↠ 10
  _ = emit∶ begin 10 ∎

  _ : 10 —↠ 10
  _ = emitting [] ∶ begin 10 ∎

  open import Class.DecEq
  open import Class.Decidable

  _ : 10 —↠⁺ 12
  _ = emitting ("inc" ∷ "dec" ∷ "inc" ∷ "inc" ∷ []) ∶
      begin 10 —→⟨ [inc]      ⟩ it , it ⊢
            11 —→⟨ [dec] {10} ⟩
            10 —→⟨ [inc] {10} ⟩
            11 —→⟨ [inc] {11} ⟩
            12 ∎
            -- [BUG] cannot replace with begin 10 —→⟨ [inc] ⟩ 11 ⋯
            -- i.e. unnecessary implicits + first two equivalence proofs

  _ : 12 ⁺↞— 10
  _ = emitting ("inc" ∷ "dec" ∷ "inc" ∷ "inc" ∷ []) ∶
      begin 12 ⟨ [inc]      ⟩←— it , it ⊢
            11 ⟨ [inc] {10} ⟩←—
            10 ⟨ [dec] {10} ⟩←—
            11 ⟨ [inc] {10} ⟩←—
            10 ∎
