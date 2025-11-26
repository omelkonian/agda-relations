open import Relation.Prelude
open import Class.Setoid
open import Relation.InferenceRules
open import Relation.Closure.Core

module Relation.Closure.UpTo.ReflTrans
  {A : Type ℓ} (_—→_ : Rel A ℓ) ⦃ sa : ISetoid A ⦄
  where

open import Relation.Closure.ReflTrans _—→_ public
  using (_←—_)

private
  ℓ⊔ℓ′ = ℓ ⊔ relℓ ⦃ sa ⦄

-- left-biased
infix  3 _∎
infixr 2 _—→⟨_⟩_⊢_
infix  1 begin_; pattern begin_ x = x
infix -1 _—↠_ _—↠⁺_
data _—↠_ : Rel A ℓ⊔ℓ′ where
  _∎ : ∀ x → x —↠ x
  _—→⟨_⟩_⊢_ : ∀ x {x′ y y′ z}
    → x′ —→ y′
    → x ≈ x′ × y ≈ y′
    → y —↠ z
      --———————————————
    → x —↠ z
data _—↠⁺_ : Rel A ℓ⊔ℓ′ where
  _—→⟨_⟩_⊢_ : ∀ x {x′ y y′ z}
    → x′ —→ y′
    → x ≈ x′ × y ≈ y′
    → y —↠ z
      --———————————————
    → x —↠⁺ z

-- transitivity of _—↠⁽⁺⁾_
—↠-trans : Transitive _—↠_
—↠-trans (x ∎) xz = xz
—↠-trans (_ —→⟨ r ⟩ p ⊢ xy) yz = _ —→⟨ r ⟩ p ⊢ —↠-trans xy yz

↠⁺⇒↠ : _—↠⁺_ ⇒² _—↠_
↠⁺⇒↠ (_ —→⟨ r ⟩ p ⊢ xy) = _ —→⟨ r ⟩ p ⊢ xy

—↠⁺-transˡ : Trans _—↠⁺_ _—↠_ _—↠⁺_
—↠⁺-transˡ (_ —→⟨ r ⟩ p ⊢ xy) yz = _ —→⟨ r ⟩ p ⊢ —↠-trans xy yz

—↠⁺-transʳ : Trans _—↠_ _—↠⁺_ _—↠⁺_
—↠⁺-transʳ (_ ∎) yz⁺ = yz⁺
—↠⁺-transʳ (_ —→⟨ r ⟩ p ⊢ xy) yz⁺ = _ —→⟨ r ⟩ p ⊢ —↠-trans xy (↠⁺⇒↠ yz⁺)

—↠⁺-trans : Transitive _—↠⁺_
—↠⁺-trans = —↠⁺-transʳ ∘ ↠⁺⇒↠

_—↠⟨_⟩_  = TransitiveOp _—↠_  ∋ mkTransitiveOp —↠-trans
_—↠⁺⟨_⟩_ = TransitiveOp _—↠⁺_ ∋ mkTransitiveOp —↠⁺-trans

-- right-biased view
-- infix  3 _∎
infixr 2 _⟨_⟩←—_⊢_
infix -1 _↞—_ _⁺↞—_
data _↞—_ : Rel A ℓ⊔ℓ′ where
  _∎ : ∀ x → x ↞— x
  _⟨_⟩←—_⊢_ : ∀ z {z′ y y′ x}
    → (z′ ←— y′)
    → z ≈ z′ × y ≈ y′
    → (y ↞— x)
      --————————————————————
    → z ↞— x
data _⁺↞—_ : Rel A ℓ⊔ℓ′ where
  _⟨_⟩←—_⊢_ : ∀ z {z′ y y′ x}
    → (z′ ←— y′)
    → z ≈ z′ × y ≈ y′
    → (y ↞— x)
      --————————————————————
    → z ⁺↞— x

-- transitivity of _⁽⁺⁾↞—_
↞—-trans : Transitive _↞—_
↞—-trans (x ∎) xz = xz
↞—-trans (_ ⟨ r ⟩←— p ⊢ xy) yz = _ ⟨ r ⟩←— p ⊢ ↞—-trans xy yz

↞⁺⇒↞ : _⁺↞—_ ⇒² _↞—_
↞⁺⇒↞ (_ ⟨ r ⟩←— p ⊢ xy) = _ ⟨ r ⟩←— p ⊢ xy

⁺↞—-transˡ : Trans _⁺↞—_ _↞—_ _⁺↞—_
⁺↞—-transˡ (_ ⟨ r ⟩←— p ⊢ xy) yz = _ ⟨ r ⟩←— p ⊢ ↞—-trans xy yz

⁺↞—-transʳ : Trans _↞—_ _⁺↞—_ _⁺↞—_
⁺↞—-transʳ (_ ∎) yz⁺ = yz⁺
⁺↞—-transʳ (_ ⟨ r ⟩←— p ⊢ xy) yz⁺ = _ ⟨ r ⟩←— p ⊢ ↞—-trans xy (↞⁺⇒↞ yz⁺)

⁺↞—-trans : Transitive _⁺↞—_
⁺↞—-trans = ⁺↞—-transʳ ∘ ↞⁺⇒↞

_↞—⟨_⟩_  = TransitiveOp _↞—_  ∋ mkTransitiveOp ↞—-trans
_⁺↞—⟨_⟩_ = TransitiveOp _⁺↞—_ ∋ mkTransitiveOp ⁺↞—-trans

-- automatic-proof version
module _ ⦃ ds : DecSetoid A ⦄ where

  infixr 2 _—→⟨_⟩_ _⟨_⟩←—_

  _—→⟨_⟩_ : ∀ x
    → x′ —→ y′
    → y —↠ z
    → {True $ x ≈? x′}
    → {True $ y ≈? y′}
      --————————————————
    → x —↠ z
  (x —→⟨ x′→y′ ⟩ y↠z) {p₁} {p₂} = x —→⟨ x′→y′ ⟩ toWitness p₁ , toWitness p₂ ⊢ y↠z

  _⟨_⟩←—_ : ∀ z
    → z′ ←— y′
    → y ↞— x
    → {True $ z ≈? z′}
    → {True $ y ≈? y′}
      --——————————————————
    → z ↞— x
  (z ⟨ z′←y′ ⟩←— y↞x) {p₁} {p₂} = z ⟨ z′←y′ ⟩←— toWitness p₁ , toWitness p₂ ⊢ y↞x

-- view correspondence
infixr 2 _`—→⟨_⟩_⊢_
_`—→⟨_⟩_⊢_ : ∀ (x : A) {x′ y y′ x}
  → y′ ←— x′
  → x ≈ x′ × y ≈ y′
  → z ↞— y
  → z ↞— x
_ `—→⟨ st ⟩ eq ⊢ _ ∎                  = _ ⟨ st ⟩←— Product.swap eq ⊢ _ ∎
x `—→⟨ st ⟩ eq ⊢ _ ⟨ st′ ⟩←— eq′ ⊢ tr = _ ⟨ st′ ⟩←— eq′ ⊢ (x `—→⟨ st ⟩ eq ⊢ tr)

viewLeft : x —↠ y → y ↞— x
viewLeft (_ ∎)          = _ ∎
viewLeft (c —→⟨ st ⟩ eq ⊢ p) = c `—→⟨ st ⟩ eq ⊢ viewLeft p

infixr 2 _`⟨_⟩←—_⊢_
_`⟨_⟩←—_⊢_ : ∀ z {z′ y y′ x}
  → y′ —→ z′
  → z ≈ z′ × y ≈ y′
  → x —↠ y
  → x —↠ z
_ `⟨ st ⟩←— eq ⊢ (_ ∎)                 = _ —→⟨ st ⟩ Product.swap eq ⊢ _ ∎
_ `⟨ st ⟩←— eq ⊢ (_ —→⟨ st′ ⟩ eq′ ⊢ p) = _ —→⟨ st′ ⟩ eq′ ⊢ (_ `⟨ st ⟩←— eq ⊢ p)

viewRight : y ↞— x → x —↠ y
viewRight (_ ∎)          = _ ∎
viewRight (_ ⟨ st ⟩←— eq ⊢ p) = _ `⟨ st ⟩←— eq ⊢ viewRight p

view↔ : (x —↠ y) ↔ (y ↞— x)
view↔ = viewLeft , viewRight
