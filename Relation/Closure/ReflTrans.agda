open import Relation.Prelude
open import Relation.InferenceRules
open import Relation.Closure.Core

module Relation.Closure.ReflTrans {A : Type ℓ} (_—→_ : Rel A ℓ) where

-- left-biased
infix  3 _∎
infixr 2 _—→⟨_⟩_ _—↠⟨_⟩_
infix  1 begin_; pattern begin_ x = x
infix -1 _—↠_ _—↠⁺_
data _—↠_ : Rel A ℓ where
  _∎ : ∀ x → x —↠ x
  _—→⟨_⟩_ : ∀ x → x —→ y → y —↠ z → x —↠ z
data _—↠⁺_ : Rel A ℓ where
  _—→⟨_⟩_ : ∀ x → x —→ y → y —↠ z → x —↠⁺ z

pattern _—→⟨_∣_⟩_ x x→y y y→z = _—→⟨_⟩_ {y = y} x x→y y→z

—↠-trans : Transitive _—↠_
—↠-trans (x ∎) xz = xz
—↠-trans (_ —→⟨ r ⟩ xy) yz = _ —→⟨ r ⟩ —↠-trans xy yz

_—↠⟨_⟩_ : ∀ x → x —↠ y → y —↠ z → x —↠ z
_—↠⟨_⟩_ _ = —↠-trans

-- right-biased view
_←—_ = flip _—→_

-- infix  3 _∎
infixr 2 _⟨_⟩←—_
infix -1 _←—_ _↞—_ _⁺↞—_
data _↞—_ : Rel A ℓ where
  _∎ : ∀ x → x ↞— x
  _⟨_⟩←—_ : ∀ z → z ←— y → y ↞— x → z ↞— x
data _⁺↞—_ : Rel A ℓ where
  _⟨_⟩←—_ : ∀ z → z ←— y → y ↞— x → z ⁺↞— x

pattern _⟨_∣_⟩←—_ z z←y y y↞x = _⟨_⟩←—_ {y = y} z z←y y↞x

↞—-trans : Transitive _↞—_
↞—-trans (x ∎) xz = xz
↞—-trans (_ ⟨ r ⟩←— zy) yx = _ ⟨ r ⟩←— ↞—-trans zy yx

_⟨_⟩↞—_ : ∀ z → z ↞— y → y ↞— x → z ↞— x
_⟨_⟩↞—_ _ = ↞—-trans

↞—-trans-assoc : ∀ {x y z w} (x→ : y ↞— x) (y→ : z ↞— y) (z→ : w ↞— z) →
  ↞—-trans (↞—-trans z→ y→) x→ ≡ ↞—-trans z→ (↞—-trans y→ x→)
↞—-trans-assoc x→ y→ = λ where
  (_ ∎) → refl
  (_ ⟨ _ ⟩←— z→) → cong (_ ⟨ _ ⟩←—_) $ ↞—-trans-assoc x→ y→ z→

↞—-trans-identityʳ : ∀ {x y} (x→ : y ↞— x) → ↞—-trans x→ (_ ∎) ≡ x→
↞—-trans-identityʳ = λ where
  (_ ∎) → refl
  (_ ⟨ _ ⟩←— tr) → cong (_ ⟨ _ ⟩←—_) (↞—-trans-identityʳ tr)

-- view correspondence
infixr 2 _`—→⟨_⟩_
_`—→⟨_⟩_ : ∀ x → y ←— x → z ↞— y → z ↞— x
_ `—→⟨ st ⟩ _ ∎           = _ ⟨ st ⟩←— _ ∎
_ `—→⟨ st ⟩ _ ⟨ st′ ⟩←— p = _ ⟨ st′ ⟩←— _ `—→⟨ st ⟩ p

viewLeft : x —↠ y → y ↞— x
viewLeft (_ ∎)          = _ ∎
viewLeft (_ —→⟨ st ⟩ p) = _ `—→⟨ st ⟩ viewLeft p

infixr 2 _`⟨_⟩←—_
_`⟨_⟩←—_ : ∀ z → y —→ z → x —↠ y → x —↠ z
_ `⟨ st ⟩←— (_ ∎)           = _ —→⟨ st ⟩ _ ∎
_ `⟨ st ⟩←— (_ —→⟨ st′ ⟩ p) = _ —→⟨ st′ ⟩ (_ `⟨ st ⟩←— p)

viewRight : y ↞— x → x —↠ y
viewRight (_ ∎)          = _ ∎
viewRight (_ ⟨ st ⟩←— p) = _ `⟨ st ⟩←— viewRight p

view↔ : (x —↠ y) ↔ (y ↞— x)
view↔ = viewLeft , viewRight

private variable s s′ s″ s↓ s↓′ : A

open EqReasoning

viewLeft∘←— : ∀ {tr : s —↠ s′} {st : s′ —→ s″} →
  viewLeft (_ `⟨ st ⟩←— tr) ≡ (_ ⟨ st ⟩←— viewLeft tr)
viewLeft∘←— {tr = _ ∎} = refl
viewLeft∘←— {tr = _ —→⟨ x ⟩ tr} {st = st} =
  ≡begin
    viewLeft (_ `⟨ st ⟩←— (_ —→⟨ x ⟩ tr))
  ≡⟨⟩
    viewLeft (_ —→⟨ x ⟩ (_ `⟨ st ⟩←— tr))
  ≡⟨⟩
    (_ `—→⟨ x ⟩ viewLeft ((_ `⟨ st ⟩←— tr)))
  ≡⟨ cong (_ `—→⟨ _ ⟩_) $ viewLeft∘←— {tr = tr} ⟩
    (_ `—→⟨ x ⟩ ((_ ⟨ st ⟩←— viewLeft tr)))
  ≡⟨⟩
    (_ ⟨ st ⟩←— viewLeft (_ —→⟨ x ⟩ tr))
  ≡∎

viewLeft∘viewRight : ∀ {tr : s′ ↞— s} →
  viewLeft (viewRight tr) ≡ tr
viewLeft∘viewRight {tr = _ ∎} = refl
viewLeft∘viewRight {tr = _ ⟨ st ⟩←— tr} =
  ≡begin
    viewLeft (viewRight $ _ ⟨ st ⟩←— tr)
  ≡⟨⟩
    viewLeft (_ `⟨ st ⟩←— viewRight tr)
  ≡⟨ viewLeft∘←— {tr = viewRight tr}{st} ⟩
    (_ ⟨ st ⟩←— viewLeft (viewRight tr))
  ≡⟨ cong (_ ⟨ _ ⟩←—_) $ viewLeft∘viewRight {tr = tr} ⟩
    (_ ⟨ st ⟩←— tr)
  ≡∎

↞—-trans∘`—→ :  (st : s —→ s↓) (tr : s↓′ ↞— s↓) (tr′ : s′ ↞— s↓′)
  → ↞—-trans tr′ (_ `—→⟨ st ⟩ tr)
  ≡ (_ `—→⟨ st ⟩ ↞—-trans tr′ tr)
↞—-trans∘`—→ _  _ (_ ∎) = refl
↞—-trans∘`—→ st tr (_ ⟨ st′ ⟩←— tr′) =
  ≡begin
    ↞—-trans (_ ⟨ st′ ⟩←— tr′) (_ `—→⟨ st ⟩ tr)
  ≡⟨⟩
    (_ ⟨ st′ ⟩←— ↞—-trans tr′ (_ `—→⟨ st ⟩ tr))
  ≡⟨ cong (_ ⟨ st′ ⟩←—_) (↞—-trans∘`—→ st tr tr′) ⟩
    (_ ⟨ st′ ⟩←— _ `—→⟨ st ⟩ ↞—-trans tr′ tr)
  ≡⟨⟩
    (_ `—→⟨ st ⟩ _ ⟨ st′ ⟩←— ↞—-trans tr′ tr)
  ≡⟨⟩
    (_ `—→⟨ st ⟩ ↞—-trans (_ ⟨ st′ ⟩←— tr′) tr)
  ≡∎

viewLeft∘—↠-trans : (tr : s —↠ s↓) (tr′ : s↓ —↠ s′)
  → viewLeft (—↠-trans tr tr′)
  ≡ ↞—-trans (viewLeft tr′) (viewLeft tr)
viewLeft∘—↠-trans (_ ∎) tr′ =
  ≡begin
    viewLeft (—↠-trans (_ ∎) tr′)
  ≡⟨⟩
    viewLeft tr′
  ≡˘⟨ ↞—-trans-identityʳ (viewLeft tr′) ⟩
    ↞—-trans (viewLeft tr′) (_ ∎)
  ≡⟨⟩
    ↞—-trans (viewLeft tr′) (viewLeft (_ ∎))
  ≡∎
viewLeft∘—↠-trans (_ —→⟨ st ⟩ tr) tr′ =
  ≡begin
    viewLeft (—↠-trans (_ —→⟨ st ⟩ tr) tr′)
  ≡⟨⟩
    viewLeft (_ —→⟨ st ⟩ —↠-trans tr tr′)
  ≡⟨⟩
    (_ `—→⟨ st ⟩ viewLeft (—↠-trans tr tr′))
  ≡⟨ cong (_ `—→⟨ st ⟩_) (viewLeft∘—↠-trans tr tr′) ⟩
    (_ `—→⟨ st ⟩ ↞—-trans (viewLeft tr′) ( viewLeft tr))
  ≡˘⟨ ↞—-trans∘`—→ _ _ (viewLeft tr′) ⟩
    ↞—-trans (viewLeft tr′) (_ `—→⟨ st ⟩ viewLeft tr)
  ≡⟨⟩
    ↞—-trans (viewLeft tr′) (viewLeft (_ —→⟨ st ⟩ tr))
  ≡∎

-- ** states

open L⁺ using (head; tail; toList; _∷⁺_; _⁺++_; _⁺∷ʳ_)

states⁺ : (s′ ↞— s) → List⁺ A
states⁺ = λ where
  (s ∎) → L⁺.[ s ]
  (s′ ⟨ _ ⟩←— tr) → s′ ∷⁺ states⁺ tr

states : (s′ ↞— s) → List A
states = toList ∘ states⁺

states-↞— : ∀ (s′↠ : s″ ↞— s′) (s↠ : s′ ↞— s) →
  states (↞—-trans s′↠ s↠) ≡ states s′↠ ++ states⁺ s↠ .tail
states-↞— (_ ∎) (_ ∎) = refl
states-↞— (_ ∎) (_ ⟨ _ ⟩←— _) = refl
states-↞— {s″}{s′}{s} (_ ⟨ st ⟩←— s′↠) s↠ =
  ≡begin
    states (↞—-trans (s″ ⟨ st ⟩←— s′↠) s↠)
  ≡⟨⟩
    s″ ∷ states (↞—-trans s′↠ s↠)
  ≡⟨ cong (s″ ∷_) (states-↞— s′↠ s↠) ⟩
    s″ ∷ (states s′↠ ++ states⁺ s↠ .tail)
  ≡⟨⟩
    states (s″ ⟨ st ⟩←— s′↠) ++ states⁺ s↠ .tail
  ≡∎

states⁺-↞— : ∀ (s′↠ : s″ ↞— s′) (s↠ : s′ ↞— s) →
  states⁺ (↞—-trans s′↠ s↠) ≡ states⁺ s′↠ ⁺++ states⁺ s↠ .tail
states⁺-↞— (_ ∎) (_ ∎) = refl
states⁺-↞— (_ ∎) (_ ⟨ _ ⟩←— _) = refl
states⁺-↞— {s″}{s′}{s} (_ ⟨ st ⟩←— s′↠) s↠ =
  ≡begin
    states⁺ (↞—-trans (s″ ⟨ st ⟩←— s′↠) s↠)
  ≡⟨⟩
    s″ ∷ states (↞—-trans s′↠ s↠)
  ≡⟨ cong (s″ ∷_) (states-↞— s′↠ s↠) ⟩
    s″ ∷ (states s′↠ ++ states⁺ s↠ .tail)
  ≡⟨⟩
    states⁺ (s″ ⟨ st ⟩←— s′↠) ⁺++ states⁺ s↠ .tail
  ≡∎

states⁺∘viewLeft : ∀ {tr : s″ ↞— s′} {st : s′ ←— s} →
  states⁺ (s `—→⟨ st ⟩ tr) ≡ states⁺ tr ⁺∷ʳ s
states⁺∘viewLeft {tr = _ ∎} = refl
states⁺∘viewLeft {tr = _ ⟨ _ ⟩←— tr} {st}
  rewrite states⁺∘viewLeft {tr = tr}{st}
  = refl

head≡ : (tr : s′ ↞— s) → states⁺ tr .head ≡ s′
head≡ = λ where
  (_ ∎) → refl
  (_ ⟨ _ ⟩←— _) → refl

open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)

open import Function.Base using (_$′_)
open import Data.List.Relation.Unary.Any using (here; there)

last∈ : (tr : s′ ↞— s) → s′ ∈ states tr
last∈ = λ where
  (_ ∎) → here refl
  (_ ⟨ _ ⟩←— tr) → here refl

first∈ : (tr : s′ ↞— s) → s ∈ states tr
first∈ = λ where
  (_ ∎) → here refl
  (_ ⟨ _ ⟩←— tr) → there $′ first∈ tr

split-by-state : ∀ {s↓} →
    (tr : s′ ↞— s) →
  ∙ s↓ ∈ states tr
  ──────────────────────
  (s↓ ↞— s) × (s′ ↞— s↓)
split-by-state tr (here refl)
   rewrite head≡ tr
 =  tr , (_ ∎)
split-by-state (_ ⟨ x ⟩←— tr) (there s↓∈)
 = let tr′ , tr″ = split-by-state tr s↓∈
   in tr′ , (_ ⟨ x ⟩←— tr″)

states-factor :  ∀ {s₁ s₂} →
    (tr : s′ ↞— s) →
  ∙ s₁ ∈ states tr
  ∙ s₂ ∈ states tr
    ───────────────────────
    (s₂ ↞— s₁) ⊎ (s₁ ↞— s₂)
states-factor tr (here refl) s₂∈
  = inj₂ (subst (_↞— _) (sym $ head≡ tr) $ proj₂ $ split-by-state tr s₂∈)
states-factor tr s₁∈ (here refl)
  = inj₁ ( subst (_↞— _) (sym $ head≡ tr) $ proj₂ $ split-by-state tr s₁∈)
states-factor (_ ⟨ x ⟩←— tr) (there s₁∈) (there s₂∈) = states-factor tr s₁∈ s₂∈

states-factor′ :  ∀ {s₀ s₁} →
    (tr : s′ ↞— s) →
    (tr₀ : s ↞— s₀) →
    (let extTr = ↞—-trans tr tr₀) →
  ∙ s₁ ∈ states extTr
    ───────────────────────
    s₁ ∈ states tr
  ⊎ (s ↞— s₁)
states-factor′ {s₁ = s₁} tr tr₀ s∈
  with ∈-++⁻ (states tr) $ subst (s₁ ∈_) (states-↞— tr tr₀) s∈
... | inj₁ s∈ˡ = inj₁ s∈ˡ
... | inj₂ s∈ʳ = inj₂ $ split-by-state tr₀ (there s∈ʳ) .proj₂

-- ** steps

Step = ∃ λ s → ∃ λ s′ → s —→ s′

steps : (s′ ↞— s) → List Step
steps = λ where
  (_ ∎) → []
  (_ ⟨ st ⟩←— tr) → (-, -, st) ∷ steps tr

steps-trans : ∀ (tr′ : s″ ↞— s′) (tr : s′ ↞— s) →
    ────────────────────────────────────────────────
     steps (↞—-trans tr′ tr) ≡ steps tr′ ++ steps tr
steps-trans = λ where
  (_ ∎) tr → refl
  (_ ⟨ x ⟩←— tr′) tr → cong (_ ∷_) (steps-trans tr′ tr)

steps˘ : (s —↠ s′) → List Step
-- steps˘ = steps ∘ viewLeft
steps˘ = λ where
  (_ ∎) → []
  (_ —→⟨ st ⟩ tr) → (-, -, st) ∷ steps˘ tr

steps˘-trans : ∀ (tr : s —↠ s′) (tr′ : s′ —↠ s″) →
    ────────────────────────────────────────────────
     steps˘ (—↠-trans tr tr′) ≡ steps˘ tr ++ steps˘ tr′
steps˘-trans = λ where
  (_ ∎) tr′ → refl
  (_ —→⟨ _ ⟩ tr) tr′ →  cong (_ ∷_) (steps˘-trans tr tr′)

steps˘∘←— : ∀ {tr : s —↠ s′} {st : s′ —→ s″} →
  steps˘ (_ `⟨ st ⟩←— tr) ≡ (steps˘ tr L.∷ʳ (-, -, st))
steps˘∘←— {tr = _ ∎} = refl
steps˘∘←— {tr = _ —→⟨ _ ⟩ tr} = cong (_ ∷_) $ steps˘∘←— {tr = tr}

steps-viewRight : (tr : s′ ↞— s) → steps˘ (viewRight tr) ≡ L.reverse (steps tr)
steps-viewRight (_ ∎) = refl
steps-viewRight (_ ⟨ st ⟩←— tr)
  = let open EqReasoning in
  ≡begin
    steps˘ (viewRight (_ ⟨ st ⟩←— tr))
  ≡⟨⟩
    steps˘ (_ `⟨ st ⟩←— viewRight tr)
  ≡⟨ steps˘∘←— ⟩
    steps˘ (viewRight tr) L.∷ʳ _
  ≡⟨ cong (L._∷ʳ _) $ steps-viewRight tr ⟩
    L.reverse (steps tr) L.∷ʳ _
  ≡˘⟨ LP.unfold-reverse _ (steps tr) ⟩
    L.reverse (_ ∷ steps tr)
  ≡⟨⟩
    L.reverse (steps (_ ⟨ st ⟩←— tr))
  ≡∎

-- ** property preservation

StepPreserved′ : Rel (Pred A ℓ) _
StepPreserved′ P Q = ∀ {s s′} →
  ∙ s —→ s′
  ∙ P s
    ───────
    Q s′

StepPreserved : Pred (Pred A ℓ) _
StepPreserved P = StepPreserved′ P P

StepPreservedSt : Rel (Pred A ℓ) _
StepPreservedSt P Q = StepPreserved′ (P ∩¹ Q) P

-- ** well-rooted traces

open import Class.HasInitial

module _ ⦃ _ : HasInitial A ⦄ where
  Reachable : Pred A _
  Reachable s = ∃ λ s₀ → Initial s₀ × (s ↞— s₀)

  Invariant : Pred (Pred A ℓ) _
  Invariant = Reachable ⊆¹_

  -- invariance through step preservation
  module _ {P} (initP : Initial ⊆¹ P) (stepP : StepPreserved P) where
    Step⇒Invariant : Invariant P
    Step⇒Invariant = λ where
      (_ , init , (_ ∎)) → initP init
      (_ , init , (_ ⟨ step ⟩←— p)) → stepP step $ Step⇒Invariant (_ , init , p)

  -- reachability-indexed properties
  Trace = ∃ Reachable

  TraceProperty  = Trace → Type

  TraceInvariant : Pred (Pred Trace ℓ) _
  TraceInvariant P = ∀ {s} (Rs : Reachable s) → P (-, Rs)

-- ** factorisation

⟨∣⟩←-inj : ∀{y′ : A}{z← : z ←— y}{←x : y ↞— x}{z←′ : z ←— y′}{←x′ : y′ ↞— x} →
    _≡_ {A = z ↞— x } (z ⟨ z← ∣ y ⟩←— ←x) (z ⟨ z←′ ∣ y′ ⟩←— ←x′)
  → Σ (y ≡ y′) λ where refl →  z← ≡ z←′ × ←x ≡ ←x′
  -- → (y , z← , ←x) ≡ (y′ , z←′ , ←x′)
⟨∣⟩←-inj refl = refl , refl , refl

factor : ∀{w} →
   (y←x : y ↞— x) →
   (z←y : z ↞— y) →
   (w←x : w ↞— x) →
   (z←w : z ↞— w) →
   ↞—-trans z←y y←x ≡ ↞—-trans z←w w←x →
   (y ↞— w) ⊎ (w ↞— y)
factor y←x (_ ∎) w←x z←w eq = inj₁ z←w
factor y←x z←y w←x (_ ∎) eq = inj₂ z←y
factor y←x (_ ⟨ z←y′ ⟩←— z←y) w←x (_ ⟨ z←w′ ⟩←— z←w) eq
  with refl , refl , eq ← ⟨∣⟩←-inj eq
  = factor y←x z←y w←x z←w eq

factor⁺ : ∀ {≪y ≫y ≪w ≫w} →

   (y←x : ≪y ↞— x)
   (y←y : ≫y ←— ≪y)
   (z←y : z  ↞— ≫y)

   (w←x : ≪w ↞— x)
   (w←w : ≫w ←— ≪w)
   (z←w : z  ↞— ≫w) →

     ↞—-trans z←y (_ ⟨ y←y ⟩←— y←x)
   ≡ ↞—-trans z←w (_ ⟨ w←w ⟩←— w←x)
   ──────────────────────────────────────────
     (Step ∋ ≪y , ≫y , y←y) ≡ (≪w , ≫w , w←w)
   ⊎ (≪y ↞— ≫w)
   ⊎ (≪w ↞— ≫y)

factor⁺ y←x y←y (_ ∎) w←x w←w (_ ∎) eq
  with refl , refl , eq ← ⟨∣⟩←-inj eq
  = inj₁ refl
factor⁺ y←x y←y (_ ∎) w←x w←w (_ ⟨ _ ⟩←— z←w) eq
  with refl , refl , eq ← ⟨∣⟩←-inj eq
  = inj₂ (inj₁ z←w)
factor⁺ y←x y←y (_ ⟨ _ ⟩←— z←y) w←x w←w (_ ∎) eq
  with refl , refl , eq ← ⟨∣⟩←-inj eq
  = inj₂ (inj₂ z←y)
factor⁺ y←x y←y (_ ⟨ z←y′ ⟩←— z←y) w←x w←w (_ ⟨ z←w′ ⟩←— z←w) eq
  with refl , refl , eq ← ⟨∣⟩←-inj eq
  = factor⁺ y←x y←y z←y w←x w←w z←w eq
