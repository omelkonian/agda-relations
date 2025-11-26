open import Relation.Prelude
open import Class.Bifunctor
open import Relation.InferenceRules
open import Relation.Closure.Core

module Relation.Closure.LReflTrans
  {A : Type ℓ} {L : Type} (_—[_]→_ : LRel (A , L) ℓ)
  where

private variable
  α α′ : L
  αs αs′ : List L

-- left-biased
infix  3 _∎
infixr 2 _—→⟨_⟩_
infix  1 begin_; pattern begin_ x = x
infix -1 _—→_ _—[_]↠_ _—↠_ _—[_]↠⁺_ _—↠⁺_
data _—[_]↠_ : LRel (A , List L) ℓ where
  _∎ : ∀ x → x —[ [] ]↠ x
  _—→⟨_⟩_ : ∀ x → x —[ α ]→ y → y —[ αs ]↠ z → x —[ α ∷ αs ]↠ z
data _—[_]↠⁺_ : LRel (A , List L) ℓ where
  _—→⟨_⟩_ : ∀ x → x —[ α ]→ y → y —[ αs ]↠ z → x —[ α ∷ αs ]↠⁺ z

_—→_  = unlabel _—[_]→_
_—↠_  = unlabel _—[_]↠_
_—↠⁺_ = unlabel _—[_]↠⁺_

-- transitivity of _—↠⁽⁺⁾_
—↠-trans : Transitive _—↠_
—↠-trans ([]     , (x ∎))     xz = xz
—↠-trans (_ ∷ αs , (_ —→⟨ r ⟩ xy)) yz = -, (_ —→⟨ r ⟩ —↠-trans (αs , xy) yz .proj₂)

↠⁺⇒↠ : _—↠⁺_ ⇒² _—↠_
↠⁺⇒↠ (_ , (_ —→⟨ r ⟩ xy)) = -, (_ —→⟨ r ⟩ xy)

—↠⁺-transˡ : Trans _—↠⁺_ _—↠_ _—↠⁺_
—↠⁺-transˡ (_ , (_ —→⟨ r ⟩ xy)) yz = -, (_ —→⟨ r ⟩ —↠-trans (-, xy) yz .proj₂)

—↠⁺-transʳ : Trans _—↠_ _—↠⁺_ _—↠⁺_
—↠⁺-transʳ (_ , (_ ∎)) yz⁺ = yz⁺
—↠⁺-transʳ (_ , (_ —→⟨ r ⟩ xy)) yz⁺ = -, (_ —→⟨ r ⟩ —↠-trans (-, xy) (↠⁺⇒↠ yz⁺) .proj₂)

—↠⁺-trans : Transitive _—↠⁺_
—↠⁺-trans = —↠⁺-transʳ ∘ ↠⁺⇒↠

_—↠⟨_⟩_  = TransitiveOp _—↠_  ∋ mkTransitiveOp —↠-trans
_—↠⁺⟨_⟩_ = TransitiveOp _—↠⁺_ ∋ mkTransitiveOp —↠⁺-trans

-- right-biased view
_←[_]—_ : LRel (A , L) ℓ
y ←[ α ]— x = x —[ α ]→ y

-- infix  3 _∎
infixr 2 _⟨_⟩←—_
infix -1 _←—_ _↞[_]—_ _↞—_ _⁺↞[_]—_ _⁺↞—_
data _↞[_]—_ : LRel (A , List L) ℓ where
  _∎ : ∀ x → x ↞[ [] ]— x
  _⟨_⟩←—_ : ∀ z → (z ←[ α ]— y) → (y ↞[ αs ]— x) → z ↞[ αs L.∷ʳ α ]— x
data _⁺↞[_]—_ : LRel (A , List L) ℓ where
  _⟨_⟩←—_ : ∀ z → (z ←[ α ]— y) → (y ↞[ αs ]— x) → z ⁺↞[ αs L.∷ʳ α ]— x

_←—_  = unlabel _←[_]—_
_↞—_  = unlabel _↞[_]—_
_⁺↞—_ = unlabel _⁺↞[_]—_

-- view correspondence
infixr 2 _`—→⟨_⟩_
_`—→⟨_⟩_ : ∀ x → y ←[ α ]— x → z ↞[ αs ]— y → z ↞[ α ∷ αs ]— x
_ `—→⟨ st ⟩ _ ∎           = _ ⟨ st ⟩←— _ ∎
_ `—→⟨ st ⟩ _ ⟨ st′ ⟩←— p = _ ⟨ st′ ⟩←— _ `—→⟨ st ⟩ p

viewLeft : x —[ αs ]↠ y → y ↞[ αs ]— x
viewLeft (_ ∎)          = _ ∎
viewLeft (_ —→⟨ st ⟩ p) = _ `—→⟨ st ⟩ viewLeft p

viewLeft∃ : x —↠ y → y ↞— x
viewLeft∃ (_ , xy) = -, viewLeft xy

infixr 2 _`⟨_⟩←—_
_`⟨_⟩←—_ : ∀ z → y —[ α ]→ z → x —[ αs ]↠ y → x —[ αs L.∷ʳ α ]↠ z
_ `⟨ st ⟩←— (_ ∎)           = _ —→⟨ st ⟩ _ ∎
_ `⟨ st ⟩←— (_ —→⟨ st′ ⟩ p) = _ —→⟨ st′ ⟩ (_ `⟨ st ⟩←— p)

viewRight : y ↞[ αs ]— x → x —[ αs ]↠ y
viewRight (_ ∎)          = _ ∎
viewRight (_ ⟨ st ⟩←— p) = _ `⟨ st ⟩←— viewRight p

view↔ : (x —[ αs ]↠ y) ↔ (y ↞[ αs ]— x)
view↔ = viewLeft , viewRight

-- view correspondence between _—↠⁺_ and _⁺↞—_
infixr 2 _`—→⁺⟨_⟩_
_`—→⁺⟨_⟩_ : ∀ x → y ←[ α ]— x → z ↞[ αs ]— y → z ⁺↞[ α ∷ αs ]— x
_ `—→⁺⟨ st ⟩ _ ∎           = _ ⟨ st ⟩←— _ ∎
_ `—→⁺⟨ st ⟩ _ ⟨ st′ ⟩←— p = _ ⟨ st′ ⟩←— _ `—→⟨ st ⟩ p

viewLeft⁺ : x —[ αs ]↠⁺ y → y ⁺↞[ αs ]— x
viewLeft⁺ (_ —→⟨ st ⟩ p) = _ `—→⁺⟨ st ⟩ viewLeft p

infixr 2 _`⟨_⟩⁺←—_
_`⟨_⟩⁺←—_ : ∀ z → y —[ α ]→ z → x —[ αs ]↠ y → x —[ αs L.∷ʳ α ]↠⁺ z
_ `⟨ st ⟩⁺←— (_ ∎)           = _ —→⟨ st ⟩ _ ∎
_ `⟨ st ⟩⁺←— (_ —→⟨ st′ ⟩ p) = _ —→⟨ st′ ⟩ (_ `⟨ st ⟩←— p)

viewRight⁺ : y ⁺↞[ αs ]— x → x —[ αs ]↠⁺ y
viewRight⁺ (_ ⟨ st ⟩←— p) = _ `⟨ st ⟩⁺←— viewRight p

view↔⁺ : (x —[ αs ]↠⁺ y) ↔ (y ⁺↞[ αs ]— x)
view↔⁺ = viewLeft⁺ , viewRight⁺

-- transitivity of _↞—⁽⁺⁾_
↞—-trans : Transitive _↞—_
↞—-trans zy yx = viewLeft <$>₂′ —↠-trans (viewRight <$>₂′ yx) (viewRight <$>₂′ zy)

↞⁺⇒↞ : _⁺↞—_ ⇒² _↞—_
↞⁺⇒↞ = map₂′ viewLeft ∘ ↠⁺⇒↠ ∘ map₂′ viewRight⁺

⁺↞—-transˡ : Trans _⁺↞—_ _↞—_ _⁺↞—_
⁺↞—-transˡ zy⁺ yx = viewLeft⁺ <$>₂′ —↠⁺-transʳ (viewRight <$>₂′ yx) (viewRight⁺ <$>₂′ zy⁺)

⁺↞—-transʳ : Trans _↞—_ _⁺↞—_ _⁺↞—_
⁺↞—-transʳ zy yx⁺ = viewLeft⁺ <$>₂′ —↠⁺-transˡ (viewRight⁺ <$>₂′ yx⁺) (viewRight <$>₂′ zy)

⁺↞—-trans : Transitive _⁺↞—_
⁺↞—-trans = ⁺↞—-transʳ ∘ ↞⁺⇒↞

_↞—⟨_⟩_  = TransitiveOp _↞—_  ∋ mkTransitiveOp ↞—-trans
_⁺↞—⟨_⟩_ = TransitiveOp _⁺↞—_ ∋ mkTransitiveOp ⁺↞—-trans
