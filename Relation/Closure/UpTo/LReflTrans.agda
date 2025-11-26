open import Relation.Prelude
open import Class.Setoid
open import Relation.InferenceRules
open import Relation.Closure.Core

module Relation.Closure.UpTo.LReflTrans
  {A : Type ℓ} {L : Type} (_—[_]→_ : LRel (A , L) ℓ) ⦃ sa : ISetoid A ⦄
  where

open import Relation.Closure.LReflTrans _—[_]→_ public
  using (_—→_; _←[_]—_; _←—_)

private
  ℓ⊔ℓ′ = ℓ ⊔ relℓ ⦃ sa ⦄
  variable
    α α′ : L
    αs αs′ : List L

-- left-biased
infix  3 _∎
infixr 2 _—→⟨_⟩_⊢_
infix  1 begin_; pattern begin_ x = x
infix -1 _—↠_ _—[_]↠_ _—↠⁺_ _—[_]↠⁺_
data _—[_]↠_ : LRel (A , List L) ℓ⊔ℓ′ where
  _∎ : ∀ x → x —[ [] ]↠ x
  _—→⟨_⟩_⊢_ : ∀ x {x′ y y′ z}
    → x′ —[ α ]→ y′
    → x ≈ x′ × y ≈ y′
    → y —[ αs ]↠ z
      --———————————————
    → x —[ α ∷ αs ]↠ z
data _—[_]↠⁺_ : LRel (A , List L) ℓ⊔ℓ′ where
  _—→⟨_⟩_⊢_ : ∀ x {x′ y y′ z}
    → x′ —[ α ]→ y′
    → x ≈ x′ × y ≈ y′
    → y —[ αs ]↠ z
      --———————————————
    → x —[ α ∷ αs ]↠⁺ z
_—↠_  = unlabel _—[_]↠_
_—↠⁺_ = unlabel _—[_]↠⁺_

-- right-biased view
-- infix  3 _∎
infixr 2 _⟨_⟩←—_⊢_
infix -1 _↞[_]—_ _↞—_ _⁺↞[_]—_ _⁺↞—_
data _↞[_]—_ : LRel (A , List L) ℓ⊔ℓ′ where
  _∎ : ∀ x → x ↞[ [] ]— x
  _⟨_⟩←—_⊢_ : ∀ z {z′ y y′ x}
    → (z′ ←[ α ]— y′)
    → z ≈ z′ × y ≈ y′
    → (y ↞[ αs ]— x)
      --————————————————————
    → z ↞[ αs L.∷ʳ α ]— x
data _⁺↞[_]—_ : LRel (A , List L) ℓ⊔ℓ′ where
  _⟨_⟩←—_⊢_ : ∀ z {z′ y y′ x}
    → (z′ ←[ α ]— y′)
    → z ≈ z′ × y ≈ y′
    → (y ↞[ αs ]— x)
      --————————————————————
    → z ⁺↞[ αs L.∷ʳ α ]— x
_↞—_  = unlabel _↞[_]—_
_⁺↞—_ = unlabel _⁺↞[_]—_

-- automatic-proof version
module _ ⦃ _ : DecSetoid A ⦄ where

  infixr 2 _—→⟨_⟩_ _⟨_⟩←—_

  _—→⟨_⟩_ : ∀ (x : A)
    → x′ —[ α ]→ y′
    → y —[ αs ]↠ z
    → {True $ x ≈? x′}
    → {True $ y ≈? y′}
      --————————————————
    → x —[ α ∷ αs ]↠ z
  (x —→⟨ x′→y′ ⟩ y↠z) {p₁} {p₂} = x —→⟨ x′→y′ ⟩ toWitness p₁ , toWitness p₂ ⊢ y↠z

  _⟨_⟩←—_ : ∀ z
    → z′ ←[ α ]— y′
    → y ↞[ αs ]— x
    → {True $ z ≈? z′}
    → {True $ y ≈? y′}
      --——————————————————
    → z ↞[ αs L.∷ʳ α ]— x
  (z ⟨ z′←y′ ⟩←— y↞x) {p₁} {p₂} = z ⟨ z′←y′ ⟩←— toWitness p₁ , toWitness p₂ ⊢ y↞x

-- view correspondence
infixr 2 _`—→⟨_⟩_⊢_
_`—→⟨_⟩_⊢_ : ∀ (x : A) {x′ y y′ x}
  → y′ ←[ α ]— x′
  → x ≈ x′ × y ≈ y′
  → z ↞[ αs ]— y
  → z ↞[ α ∷ αs ]— x
_ `—→⟨ st ⟩ eq ⊢ _ ∎                  = _ ⟨ st ⟩←— Product.swap eq ⊢ _ ∎
x `—→⟨ st ⟩ eq ⊢ _ ⟨ st′ ⟩←— eq′ ⊢ tr = _ ⟨ st′ ⟩←— eq′ ⊢ (x `—→⟨ st ⟩ eq ⊢ tr)

viewLeft : x —[ αs ]↠ y → y ↞[ αs ]— x
viewLeft (_ ∎)          = _ ∎
viewLeft (c —→⟨ st ⟩ eq ⊢ p) = c `—→⟨ st ⟩ eq ⊢ viewLeft p

infixr 2 _`⟨_⟩←—_⊢_
_`⟨_⟩←—_⊢_ : ∀ z {z′ y y′ x}
  → y′ —[ α ]→ z′
  → z ≈ z′ × y ≈ y′
  → x —[ αs ]↠ y
  → x —[ αs L.∷ʳ α ]↠ z
_ `⟨ st ⟩←— eq ⊢ (_ ∎)                 = _ —→⟨ st ⟩ Product.swap eq ⊢ _ ∎
_ `⟨ st ⟩←— eq ⊢ (_ —→⟨ st′ ⟩ eq′ ⊢ p) = _ —→⟨ st′ ⟩ eq′ ⊢ (_ `⟨ st ⟩←— eq ⊢ p)

viewRight : y ↞[ αs ]— x → x —[ αs ]↠ y
viewRight (_ ∎)          = _ ∎
viewRight (_ ⟨ st ⟩←— eq ⊢ p) = _ `⟨ st ⟩←— eq ⊢ viewRight p

view↔ : (x —[ αs ]↠ y) ↔ (y ↞[ αs ]— x)
view↔ = viewLeft , viewRight
