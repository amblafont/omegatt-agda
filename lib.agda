{-# OPTIONS --without-K --rewriting #-}

module lib where

open import Agda.Primitive

idfun : ∀{ℓ}{A : Set ℓ} → A → A
idfun x = x

-- open import Relation.Binary.PropositionalEquality hiding ([_])

------------------------------------------------------------------------------
-- equality
------------------------------------------------------------------------------

data _≡_ {ℓ}{A : Set ℓ} (x : A) : A → Set ℓ where
  refl : x ≡ x

infix 4 _≡_

{-# BUILTIN REWRITE _≡_ #-}

_◾_ : ∀{ℓ}{A : Set ℓ}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ◾ refl = refl

infixl 4 _◾_

_⁻¹ : ∀{ℓ}{A : Set ℓ}{x y : A} → x ≡ y → y ≡ x
refl ⁻¹ = refl

infix 5 _⁻¹

_≡⟨_⟩_ : ∀{ℓ}{A : Set ℓ}(x : A){y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ x≡y ⟩ y≡z = x≡y ◾ y≡z

infixr 2 _≡⟨_⟩_

_∎ : ∀{ℓ}{A : Set ℓ}(x : A) → x ≡ x
x ∎ = refl

infix  3 _∎

coe : ∀{ℓ}{A B : Set ℓ} → A ≡ B → A → B
coe refl a = a

_≡[_]≡_ : ∀{ℓ}{A B : Set ℓ} → A → A ≡ B → B → Set ℓ
x ≡[ α ]≡ y = coe α x ≡ y

infix 4 _≡[_]≡_

coh-coe : ∀{ℓ}{A B : Set ℓ}(p : A ≡ B) → (a : A) → a ≡[ p ]≡ coe p a
coh-coe refl a = refl

ap : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'}(f : A → B){a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
    → f a₀ ≡ f a₁
ap f refl = refl

transport : ∀{ℓ ℓ'}{A : Set ℓ}(P : A → Set ℓ'){x y : A}(p : x ≡ y) → P x → P y
transport P refl a = a

apd : ∀{ℓ ℓ'}{A : Set ℓ}{B : A → Set ℓ'}(f : (x : A) → B x){a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
    → f a₀ ≡[ ap B a₂ ]≡ f a₁
apd f refl = refl

apid : ∀{ℓ}{A : Set ℓ}{x y : A}(p : x ≡ y) → ap (λ x → x) p ≡ p
apid refl = refl

apap : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : Set ℓ'}{C : Set ℓ''}{f : A → B}{g : B → C}
       {a₀ a₁ : A}(a₂ : a₀ ≡ a₁) → ap (λ x → g (f x)) a₂ ≡ ap g (ap f a₂)
apap refl = refl

J : ∀{ℓ ℓ'}{A : Set ℓ} {x : A} (P : {y : A} → x ≡ y → Set ℓ') → P refl → {y : A} → (w : x ≡ y) → P w
J P pr refl = pr

≡inv : ∀{ℓ}{A : Set ℓ} {x y : A} (p : x ≡ y) → (p ◾ p ⁻¹) ≡ refl
≡inv refl = refl

≡inv' : ∀{ℓ}{A : Set ℓ} {x y : A} (p : x ≡ y) → (p ⁻¹ ◾ p) ≡ refl
≡inv' refl = refl

coeap2 : ∀{ℓ ℓ'}{A : Set ℓ}{B : A → Set ℓ'}{a₀ a₁ : A}(a₂ : a₀ ≡ a₁){t : B a₁}
       → coe (ap B a₂) (coe (ap B (a₂ ⁻¹)) t) ≡ t
coeap2 refl = refl

coeap2' : ∀{ℓ ℓ'}{A : Set ℓ}{B : A → Set ℓ'}{a₀ a₁ : A}(a₂ : a₀ ≡ a₁){t : B a₀}
       → coe (ap B (a₂ ⁻¹)) (coe (ap B a₂) t) ≡ t
coeap2' refl = refl

ap2 : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : Set ℓ'}{C : Set ℓ''}(f : A → B → C)
    → {a₀ a₁ : A}(a₂ : a₀ ≡ a₁){b₀ b₁ : B}(b₂ : b₀ ≡ b₁)
    → f a₀ b₀ ≡ f a₁ b₁
ap2 f refl refl = refl

ap2d : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : A → Set ℓ'}{C : Set ℓ''}(f : (x : A) → B x → C)
    → {a₀ a₁ : A}(a₂ : a₀ ≡ a₁){b₀ : B a₀}{b₁ : B a₁}(b₂ : b₀ ≡[ ap B a₂ ]≡ b₁)
    → f a₀ b₀ ≡ f a₁ b₁
ap2d f refl refl = refl

$$Set=
  : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : A → Set ℓ'}(C : (x : A) → B x → Set ℓ'')
  → {a₀ a₁ : A}(a₂ : a₀ ≡ a₁){b₀ : B a₀}{b₁ : B a₁}(b₂ : b₀ ≡[ ap B a₂ ]≡ b₁)
  → C a₀ b₀ ≡ C a₁ b₁
$$Set= C refl refl = refl

$$= : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : A → Set ℓ'}{C : (x : A) → B x → Set ℓ''}
      (f : (a : A)(b : B a) → C a b)
    → {a₀ a₁ : A}(a₂ : a₀ ≡ a₁){b₀ : B a₀}{b₁ : B a₁}(b₂ : b₀ ≡[ ap B a₂ ]≡ b₁)
    → f a₀ b₀ ≡[ $$Set= C a₂ b₂ ]≡ f a₁ b₁
$$= f refl refl = refl

$$Set=i
  : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : A → Set ℓ'}(C : {x : A} → B x → Set ℓ'')
  → {a₀ a₁ : A}(a₂ : a₀ ≡ a₁){b₀ : B a₀}{b₁ : B a₁}(b₂ : b₀ ≡[ ap B a₂ ]≡ b₁)
  → C b₀ ≡ C b₁
$$Set=i C refl refl = refl

$$=i : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : A → Set ℓ'}{C : {x : A} → B x → Set ℓ''}
       (f : {a : A}(b : B a) → C b)
     → {a₀ a₁ : A}(a₂ : a₀ ≡ a₁){b₀ : B a₀}{b₁ : B a₁}(b₂ : b₀ ≡[ ap B a₂ ]≡ b₁)
     → f b₀ ≡[ $$Set=i C a₂ b₂ ]≡ f b₁
$$=i f refl refl = refl

ap3 : ∀{ℓ ℓ' ℓ'' ℓ'''}{A : Set ℓ}{B : Set ℓ'}{C : Set ℓ''}{D : Set ℓ'''}
      (f : A → B → C → D)
    → {a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
      {b₀ b₁ : B}(b₂ : b₀ ≡ b₁)
      {c₀ c₁ : C}(c₂ : c₀ ≡ c₁)
    → f a₀ b₀ c₀ ≡ f a₁ b₁ c₁
ap3 f refl refl refl = refl

coe2r : ∀{ℓ ℓ'}{A : Set ℓ}{B : A → Set ℓ'}{a₀ a₁ : A}
        (a₂ : a₀ ≡ a₁){b₀ : B a₀}{b₁ : B a₁}
      → b₀ ≡[ ap B a₂ ]≡ b₁ → b₀ ≡ coe (ap B (a₂ ⁻¹)) b₁
coe2r refl p = p

coe2l : ∀{ℓ ℓ'}{A : Set ℓ}{B : A → Set ℓ'}{a₀ a₁ : A}
        (a₂ : a₀ ≡ a₁){b₀ : B a₀}{b₁ : B a₁}
      → b₀ ≡ coe (ap B (a₂ ⁻¹)) b₁ → b₀ ≡[ ap B a₂ ]≡ b₁
coe2l refl p = p

coecoeap
  : ∀{ℓ ℓ'}{A : Set ℓ}{B : A → Set ℓ'}{a b c : A}(p : a ≡ b)(q : b ≡ c)
    {t : B a}
  → coe (ap B q) (coe (ap B p) t) ≡ coe (ap B (p ◾ q)) t
coecoeap refl refl = refl

coecoe : ∀{ℓ}{A B C : Set ℓ}(P : A ≡ B)(Q : B ≡ C){a : A}
       → coe Q (coe P a) ≡ coe (P ◾ Q) a
coecoe refl refl = refl

≡= : ∀{ℓ}{A₀ A₁ : Set ℓ}(A₂ : A₀ ≡ A₁)
     {a₀ : A₀}{a₁ : A₁}(a₂ : a₀ ≡[ A₂ ]≡ a₁)
     {b₀ : A₀}{b₁ : A₁}(b₂ : b₀ ≡[ A₂ ]≡ b₁)
   → (a₀ ≡ b₀) ≡ (a₁ ≡ b₁)
≡= refl refl refl = refl

◾lid : ∀{ℓ}{A : Set ℓ}{x y : A}(p : x ≡ y) → (refl ◾ p) ≡ p
◾lid refl = refl

◾rid : ∀{ℓ}{A : Set ℓ}{x y : A}(p : x ≡ y) → (p ◾ refl) ≡ p
◾rid refl = refl

◾ass : ∀{ℓ}{A : Set ℓ}{a b c d : A}(p : a ≡ b)(q : b ≡ c)(r : c ≡ d)
     → (p ◾ (q ◾ r)) ≡ ((p ◾ q) ◾ r)
◾ass refl refl refl = refl

ap◾ : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'}(f : A → B){a b c : A}(p : a ≡ b)(q : b ≡ c)
    → ap f (p ◾ q) ≡ (ap f p ◾ ap f q)
ap◾ f refl refl = refl

coe-apply :
 ∀ {α β γ}{A : Set α}{B : Set β}(C : A → B → Set γ)
   {b b' : B}(p : b ≡ b')(f : ∀ a → C a b)(a : A)
 → coe (ap (λ x → ∀ a → C a x) p) f a ≡ coe (ap (C a) p) (f a)
coe-apply C refl f a = refl 

coe=
  : ∀{ℓ}{A B : Set ℓ}
    {p₀ p₁ : A ≡ B}(p₂ : p₀ ≡ p₁)
    {t : A}
  → coe p₀ t ≡ coe p₁ t
coe= refl = refl

apconst : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'}{a b : A}(p : a ≡ b){t : B} → ap (λ _ → t) p ≡ refl
apconst refl = refl

ap3const
  : ∀{ℓ ℓ' ℓ'' ℓ'''}{A : Set ℓ}{B : Set ℓ'}{C : Set ℓ''}{D : Set ℓ'''}
    → {a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
      {b₀ b₁ : B}(b₂ : b₀ ≡ b₁)
      {c₀ c₁ : C}(c₂ : c₀ ≡ c₁)
      {d : D}
    → ap3 (λ _ _ _ → d) a₂ b₂ c₂ ≡ refl
ap3const refl refl refl = refl

coeap : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : A → Set ℓ'}{C : A → Set ℓ''}{a a' : A}(p : a ≡ a')
        (f : {a : A} → B a → C a){b : B a}
      → coe (ap C p) (f b) ≡ f (coe (ap B p) b)
coeap refl _ = refl

coeap2d : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : A → Set ℓ'}{C : {a : A} → B a → Set ℓ''}
        {a a' : A}(p : a ≡ a')
        (f : {a : A}(b : B a) → C b){b : B a}
      → coe ($$Set=i C p refl) (f b) ≡ f (coe (ap B p) b)
coeap2d refl _ = refl

apap3 : ∀{ℓ ℓ' ℓ'' ℓ'''}{A : Set ℓ}{B : Set ℓ'}{C : Set ℓ''}{D : Set ℓ'''}
        (f : A → B → C → D)
        {a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
        {b₀ b₁ : B}(b₂ : b₀ ≡ b₁)
        {c₀ c₁ : C}(c₂ : c₀ ≡ c₁)
        {ℓ''''}{E : Set ℓ''''}
        (g : D → E)
      → ap g (ap3 f a₂ b₂ c₂) ≡ ap3 (λ x y z → g (f x y z)) a₂ b₂ c₂
apap3 f refl refl refl g = refl

------------------------------------------------------------------------------
-- sigma
------------------------------------------------------------------------------

record Σ {ℓ ℓ'} (A : Set ℓ) (B : A → Set ℓ') : Set (ℓ ⊔ ℓ') where
  constructor _,Σ_
  field
    proj₁ : A
    proj₂ : B proj₁

infixl 5 _,Σ_

open Σ public

aptot : ∀{ℓ}{A : Set ℓ}{B : A → Set}(f : (x : A) → B x){a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
    → _≡_ {A = Σ Set λ X → X} (B a₀ ,Σ f a₀) (B a₁ ,Σ f a₁)
aptot f refl = refl

,Σ= : ∀{ℓ ℓ'}{A : Set ℓ}{B : A → Set ℓ'}{a a' : A}{b : B a}{b' : B a'}
     (p : a ≡ a') → b ≡[ ap B p ]≡ b' → _≡_ {A = Σ A B} (a ,Σ b) (a' ,Σ b')
,Σ= refl refl = refl

,Σ=0 : ∀{ℓ ℓ'}{A : Set ℓ}{B : A → Set ℓ'}{a a' : A}{b : B a}{b' : B a'}
    → _≡_ {A = Σ A B} (a ,Σ b) (a' ,Σ b') → a ≡ a'
,Σ=0 refl = refl

,Σ=1 : ∀{ℓ ℓ'}{A : Set ℓ}{B : A → Set ℓ'}{a a' : A}{b : B a}{b' : B a'}
      (p : (a ,Σ b) ≡ (a' ,Σ b')) → b ≡[ ap B (,Σ=0 p) ]≡ b'
,Σ=1 refl = refl

,Σ=η : ∀{ℓ ℓ'}{A : Set ℓ}{B : A → Set ℓ'}{w w' : Σ A B}
      (p : w ≡ w') → ,Σ= (,Σ=0 p) (,Σ=1 p) ≡ p
,Σ=η refl = refl

,Σ=β0 : ∀{ℓ ℓ'}{A : Set ℓ}{B : A → Set ℓ'}{a a' : A}{b : B a}{b' : B a'}
       (p : a ≡ a')(q : b ≡[ ap B p ]≡ b') → ,Σ=0 (,Σ= p q) ≡ p
,Σ=β0 refl refl = refl

,Σ=β1 : ∀{ℓ ℓ'}{A : Set ℓ}{B : A → Set ℓ'}{a a' : A}{b : B a}{b' : B a'}
       (p : a ≡ a')(q : b ≡[ ap B p ]≡ b')
     → ,Σ=1 (,Σ= p q) ≡[ ap (λ r → b ≡[ ap B r ]≡ b') (,Σ=β0 p q) ]≡ q
,Σ=β1 refl refl = refl

Σ= : ∀{ℓ ℓ'}
     {A₀ A₁ : Set ℓ}(A₂ : A₀ ≡ A₁)
     {B₀ : A₀ → Set ℓ'}{B₁ : A₁ → Set ℓ'}(B₂ : B₀ ≡[ ap (λ z → z → Set ℓ') A₂ ]≡ B₁)
   → Σ A₀ B₀ ≡ Σ A₁ B₁
Σ= refl refl = refl

,Σ=2 : {A : Set}{B : A → Set}{a : A}{b : B a}
       {α : a ≡ a}{β : b ≡[ ap B α ]≡ b}
     → (w : α ≡ refl) → β ≡[ ap (λ γ → b ≡[ ap B γ ]≡ b) w ]≡ refl
     → ,Σ= α β ≡ refl
,Σ=2 refl refl = refl

,Σ==
  : ∀{ℓ ℓ'}{A : Set ℓ}{B : A → Set ℓ'}
    {a₀ a₁ : A}{b₀ : B a₀}{b₁ : B a₁}
    {p₀ p₁ : a₀ ≡ a₁}(p₂ : p₀ ≡ p₁)
    {q₀ : b₀ ≡[ ap B p₀ ]≡ b₁}{q₁ : b₀ ≡[ ap B p₁ ]≡ b₁}(q₂ : q₀ ≡[ ≡= refl {a₀ = coe (ap B p₀) b₀}{coe (ap B p₁) b₀} (ap (λ z → coe (ap B z) b₀) p₂) refl ]≡ q₁) -- xxx
  → _≡_ (,Σ= p₀ q₀) (,Σ= p₁ q₁)
,Σ== refl refl = refl

ΣisSet
  : ∀{ℓ ℓ'}{A : Set ℓ}{B : A → Set ℓ'}
    (isSetA : {a a' : A}(p q : a ≡ a') → p ≡ q)
    (isSetB : {a : A}{b b' : B a}(p q : b ≡ b') → p ≡ q)
  → {w w' : Σ A B}(p q : w ≡ w') → p ≡ q
ΣisSet {A = A}{B} isSetA isSetB {a ,Σ b}{a' ,Σ b'} p q = ,Σ=η p ⁻¹ ◾ ,Σ== {p₀ = ,Σ=0 p}{,Σ=0 q} (isSetA _ _) {,Σ=1 p}{,Σ=1 q} (isSetB _ _) ◾ ,Σ=η q

-- pointed types

,Σp= : {A₀ A₁ : Set}(A₂ : A₀ ≡ A₁){a₀ : A₀}{a₁ : A₁}(a₂ : a₀ ≡[ A₂ ]≡ a₁)
    → _≡_ {A = Σ Set λ X → X} (A₀ ,Σ a₀) (A₁ ,Σ a₁)
,Σp= A₂ {b₀}{b₁} b₂ = ,Σ= A₂ (coe (ap (λ z → b₀ ≡[ z ]≡ b₁) (apid A₂ ⁻¹)) b₂)

,Σp=1 : {A₀ A₁ : Set}{a₀ : A₀}{a₁ : A₁}
     → (p : (A₀ ,Σ a₀) ≡ (A₁ ,Σ a₁)) → a₀ ≡[ ,Σ=0 p ]≡ a₁
,Σp=1 refl = refl

-- nondependent

_×_ : ∀{ℓ ℓ'} → Set ℓ → Set ℓ' → Set (ℓ ⊔ ℓ')
A × B = Σ A λ _ → B

infixl 4 _×_

,×= : ∀{ℓ}{A B : Set ℓ}{a a' : A}{b b' : B}
    → a ≡ a' → b ≡ b' → _≡_ {A = A × B} (a ,Σ b) (a' ,Σ b')
,×= refl refl = refl

------------------------------------------------------------------------------
-- top
------------------------------------------------------------------------------

record ⊤ : Set where
  constructor tt

set⊤ : {x y : ⊤}(p q : x ≡ y) → p ≡ q
set⊤ refl refl = refl

------------------------------------------------------------------------------
-- bottom
------------------------------------------------------------------------------

data ⊥ : Set where

⊥-elim : ∀{ℓ}{A : Set ℓ} → ⊥ → A
⊥-elim ()

¬ : Set → Set
¬ A = A → ⊥

------------------------------------------------------------------------------
-- disjoint union
------------------------------------------------------------------------------

data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B
infixr 1 _⊎_

ind⊎ : {A B : Set}(P : A ⊎ B → Set) → ((a : A) → P (inl a)) → ((b : B) → P (inr b))
     → (w : A ⊎ B) → P w
ind⊎ P ca cb (inl a) = ca a
ind⊎ P ca cb (inr b) = cb b

------------------------------------------------------------------------------
-- function space
------------------------------------------------------------------------------

module _
  {ℓ ℓ'}{A : Set ℓ}{B : A → Set ℓ'}{f g : (x : A) → B x}
  where

  fun-elim : (w : f ≡ g) → ((x : A) → f x ≡ g x)
  fun-elim w = λ x → ap (λ z → z x) w

  postulate
    funext : (w : (x : A) → f x ≡ g x) → f ≡ g
    fun-β  : (w : (x : A) → f x ≡ g x) → fun-elim (funext w) ≡ w
    fun-η  : (w : f ≡ g)               → funext (fun-elim w) ≡ w

funext-refl
  : ∀{ℓ ℓ'}{A : Set ℓ}{B : A → Set ℓ'}{f : (x : A) → B x}
  → funext {ℓ}{ℓ'}{A}{B}{f}{f}(λ x → refl) ≡ refl
funext-refl {A = A}{B}{f} = fun-η refl

module _
  {ℓ ℓ'}{A : Set ℓ}{B : A → Set ℓ'}
  where

  toi : (f : (x : A) → B x) → ({x : A} → B x)
  toi f {x} = f x

  fromi : (f : {x : A} → B x) → ((x : A) → B x)
  fromi f x = f {x}

  module _
    {f g : {x : A} → B x}
    where

    fun-elimi : (w : (λ {x} → f {x}) ≡ g) → ((x : A) → f {x} ≡ g {x})
    fun-elimi w = fun-elim (ap fromi w)

    funexti : ((x : A) → f {x} ≡ g {x}) → _≡_ {A = {x : A} → B x} f g
    funexti p = ap toi (funext {f = fromi f}{fromi g} p)

    fun-βi : (w : (x : A) → f {x} ≡ g {x}) → fun-elimi (funexti w) ≡ w
    fun-βi w = ap (λ z → fun-elim z) (apap {f = toi}{g = fromi}(funext w) ⁻¹)
             ◾ ap fun-elim (apid (funext w))
             ◾ fun-β w

funexti-refl
  : ∀{ℓ ℓ'}{A : Set ℓ}{B : A → Set ℓ'}{f : {x : A} → B x}
  → funexti {ℓ}{ℓ'}{A}{B}{f}{f}(λ x → refl) ≡ refl
funexti-refl {f = f} = ap (ap (λ z {x} → z x)) (funext-refl {f = λ x → f {x}})

→=
  : ∀{ℓ ℓ'}
    {A₀ A₁ : Set ℓ}(A₂ : A₀ ≡ A₁)
    {B₀ : A₀ → Set ℓ'}{B₁ : A₁ → Set ℓ'}(B₂ : {x₀ : A₀}{x₁ : A₁}(x₂ : x₀ ≡[ A₂ ]≡ x₁) → B₀ x₀ ≡ B₁ x₁)
  → ((x₀ : A₀) → B₀ x₀) ≡ ((x₁ : A₁) → B₁ x₁)
→= {ℓ}{ℓ'}{A} refl {B₀}{B₁} B₂
  = J {A = A → Set ℓ'}{B₀}
      (λ {B₁} B₂ → ((x₀ : A) → B₀ x₀) ≡ ((x₁ : A) → B₁ x₁))
      refl
      {B₁} (funext (λ x → B₂ {x} refl))

→=''
  : ∀{ℓ ℓ'}
    {A₀ A₁ : Set ℓ}(A₂ : A₀ ≡ A₁)
    {B₀ B₁ : Set ℓ'}(B₂ : B₀ ≡ B₁)
  → (A₀ → B₀) ≡ (A₁ → B₁)
→='' refl refl = refl

→='
  : ∀{ℓ ℓ'}
    {A₀ A₁ : Set ℓ}(A₂ : A₀ ≡ A₁)
    {B₀ : A₀ → Set ℓ'}{B₁ : A₁ → Set ℓ'}(B₂ : B₀ ≡[ →='' A₂ refl ]≡ B₁)
  → ((x₀ : A₀) → B₀ x₀) ≡ ((x₁ : A₁) → B₁ x₁)
→=' refl refl = refl

→i='
  : ∀{ℓ ℓ'}
    {A₀ A₁ : Set ℓ}(A₂ : A₀ ≡ A₁)
    {B₀ : A₀ → Set ℓ'}{B₁ : A₁ → Set ℓ'}(B₂ : B₀ ≡[ →='' A₂ refl ]≡ B₁)
  → ({x₀ : A₀} → B₀ x₀) ≡ ({x₁ : A₁} → B₁ x₁)
→i=' refl refl = refl

→='''
  : ∀{ℓ ℓ'}
    {A₀ A₁ : Set ℓ}(A₂ : A₀ ≡ A₁)
    {B₀ : A₀ → A₀ → Set ℓ'}{B₁ : A₁ → A₁ → Set ℓ'}(B₂ : B₀ ≡[ →='' A₂ (→='' A₂ refl) ]≡ B₁)
  → ((x₀ : A₀) → B₀ x₀ x₀) ≡ ((x₁ : A₁) → B₁ x₁ x₁)
→=''' refl refl = refl

$T=
  : ∀{ℓ ℓ'}
    {A₀ A₁ : Set ℓ}(A₂ : A₀ ≡ A₁)
    {B₀ : A₀ → Set ℓ'}{B₁ : A₁ → Set ℓ'}(B₂ : {x₀ : A₀}{x₁ : A₁}(x₂ : x₀ ≡[ A₂ ]≡ x₁) → B₀ x₀ ≡ B₁ x₁)
    {a₀ : A₀}{a₁ : A₁}(a₂ : a₀ ≡[ A₂ ]≡ a₁)
  → B₀ a₀ ≡ B₁ a₁
$T= refl B₂ refl = B₂ refl

fun-2 : {A : Set}{B : A → Set}{f : (x : A) → B x}
      → ((x : A)(p : f x ≡ f x) → p ≡ refl) → (q : f ≡ f) → q ≡ refl
fun-2 w q = coe (ap (λ x → x ≡ refl) (fun-η q))
                (coe (ap (λ x → funext (fun-elim q) ≡ x)
                         (fun-η refl))
                         (ap funext (funext (λ x → w x (fun-elim q x)))))

setCodomain : {A : Set}{B : A → Set}(w : {a : A}{b : B a}{α : b ≡ b} → α ≡ refl)
            → {f g : (x : A) → B x}{α β : f ≡ g} → α ≡ β
setCodomain w {α = α}{refl} = fun-2 (λ x p → w {α = p}) α

module _ {ℓ ℓ' ℓ''}{A : Set ℓ}{B : A → Set ℓ'}{C : {x : A} → B x → Set ℓ''} where

  curry : ((w : Σ A B) → C (proj₂ w)) → ({x : A}(y : B x) → C y)
  curry f {x} y = f (x ,Σ y)

  uncurry : ({x : A}(y : B x) → C y) → ((w : Σ A B) → C (proj₂ w))
  uncurry f (x ,Σ y) = f {x} y

  curryuncurry : (f : {x : A}(y : B x) → C y) → (λ {x} → curry (uncurry f) {x}) ≡ f
  curryuncurry f = funexti λ x → funext λ y → refl

  uncurrycurry : (f : (w : Σ A B) → C (proj₂ w)) → uncurry (curry f) ≡ f
  uncurrycurry f = funext λ { (x ,Σ y) → refl }

------------------------------------------------------------------------------
-- lifting a type
------------------------------------------------------------------------------

record Lift {ℓ ℓ'}(A : Set ℓ) : Set (ℓ ⊔ ℓ') where
  constructor lift
  field
    unlift : A

open Lift public

------------------------------------------------------------------------------
-- natural numbers
------------------------------------------------------------------------------

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

-- {-# BUILTIN NATURAL ℕ #-}

ind : (P : ℕ → Set)(z : P zero)(s : {n : ℕ} → P n → P (suc n))(n : ℕ) → P n
ind P z s zero = z
ind P z s (suc n) = s (ind P z s n)

toLevel : ℕ → Level
toLevel zero = lzero
toLevel (suc n) = lsuc (toLevel n)

------------------------------------------------------------------------------
-- finite sets
------------------------------------------------------------------------------

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)

toLevelF : {n : ℕ} → Fin n → Level
toLevelF zero = lzero
toLevelF (suc n) = lsuc (toLevelF n)

------------------------------------------------------------------------------
-- booleans
------------------------------------------------------------------------------

data Bool : Set where
  true false : Bool

if_then_else_ : {C : Bool → Set}(b : Bool)(c : C true)(d : C false) → C b
if true then c else d = c
if false then c else d = d

------------------------------------------------------------------------------
-- quotient types
------------------------------------------------------------------------------

postulate
  _/_   : ∀{ℓ ℓ'}(A : Set ℓ) → (A → A → Set ℓ') → Set (ℓ ⊔ ℓ')
  [_]/  : ∀{ℓ ℓ'}{A : Set ℓ}{R : A → A → Set ℓ'} → A → A / R
  resp/ : ∀{ℓ ℓ'}{A : Set ℓ}{R : A → A → Set ℓ'}{a₀ a₁ : A}(r : R a₀ a₁)
        → _≡_ {A = A / R} [ a₀ ]/ [ a₁ ]/
  Elim/ : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{R : A → A → Set ℓ'}{B : Set ℓ''}(f : A → B)
          (respf : {a₀ a₁ : A} → R a₀ a₁ → f a₀ ≡ f a₁) → A / R → B
  []/β  : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{R : A → A → Set ℓ'}{B : Set ℓ''}{f : A → B}
          {respf : {a₀ a₁ : A} → R a₀ a₁ → f a₀ ≡ f a₁}{a : A}
        → Elim/ f respf [ a ]/ ≡ f a

  {-# REWRITE []/β #-}

------------------------------------------------------------------------------
-- h-levels
------------------------------------------------------------------------------

set2h1 : ∀{ℓ}{A : Set ℓ}(isSetA : {x y : A} (p q : x ≡ y) → p ≡ q)
       → {x y : A}{p q : x ≡ y}(r s : p ≡ q) → r ≡ s
set2h1 {A = A} isSetA {x}{y}{p}{q} r s = w r ⁻¹ ◾ w s
  where
    s' : p ≡ q
    s' = isSetA p q ◾ isSetA q q ⁻¹
    w : (r : p ≡ q) → s' ≡ r
    w = J (λ {q} s → (isSetA p q ◾ isSetA q q ⁻¹) ≡ s) (≡inv (isSetA p p))

-- pour mon développement
subst : ∀{ℓ ℓ'}{A : Set ℓ}(P : A → Set ℓ'){x y : A}(p : x ≡ y) → P x → P y
subst P p = coe (ap P p)

sym : ∀{ℓ}{A : Set ℓ}{x y : A} → x ≡ y → y ≡ x
sym = _⁻¹

trans : ∀{ℓ}{A : Set ℓ}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans = _◾_

cong : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'}(f : A → B){a₀ a₁ : A} (a₂ : a₀ ≡ a₁)
  → f a₀ ≡ f a₁
cong = ap
