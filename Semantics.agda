{-# OPTIONS --without-K --no-termination-check #-}


module Semantics where

open import BasicSyntax
open import IdentityContextMorphisms
open import Data.Unit
open import Data.Product renaming (_,_ to _,,_)
open import Coinduction
open import Relation.Binary.PropositionalEquality hiding ([_])
open import GroupoidStructure

-- open import GlobularType (∣_∣ to 〚_〛)


∣_∣ : {A : Set₁} → A → A
∣ x ∣ = x

coerce : {A B : Set} → B ≡ A → A → B
coerce refl a = a

⊤-uni : ∀ {A : Set}{a b : A} → A ≡ ⊤ → a ≡ b
⊤-uni refl = refl

-- inspiré de EqHom
-- EqHom : {A B : Glob} → (p : A ≡ B) → {x y : ∣ A ∣} → {m n : ∣ B ∣} → (subst ∣_∣ p x ≡ m) → (subst ∣_∣ p y ≡ n) → ♭ (hom A x y) ≡ ♭ (hom B m n)
-- EqHom {.B} {B} refl {.m} {.n} {m} {n} refl refl = refl
EqEq : {A B : Set} → (p : A ≡ B) → {x y : A} → {m n : B} → (subst ∣_∣ p x ≡ m)
  → (subst ∣_∣ p y ≡ n) → (x ≡ y) ≡ (m ≡ n)
EqEq {.B} {B} refl {.m} {.n} {m} {n} refl refl = refl

postulate
   T : Set

⟦_⟧C   : Con → Set
-- ⟦_⟧T   : ∀{Γ} → Ty Γ → ⟦ Γ ⟧C → Glob
⟦_⟧T   : ∀{Γ} → Ty Γ → ⟦ Γ ⟧C → Set
⟦_⟧tm  : ∀{Γ A} → Tm A → (γ : ⟦ Γ ⟧C) 
        → ∣ ⟦ A ⟧T γ ∣
⟦_⟧S   : ∀{Γ Δ} → Γ ⇒ Δ → ⟦ Γ ⟧C → ⟦ Δ ⟧C
π      : ∀{Γ A} → Var A → (γ : ⟦ Γ ⟧C) 
        → ∣ ⟦ A ⟧T γ ∣
        -- definitionel
⟦_⟧C-β1  : ⟦ ε ⟧C ≡ ⊤
-- definitionel
⟦_⟧C-β2  : ∀ {Γ A} → (⟦ (Γ , A) ⟧C) ≡ 
          Σ (⟦ Γ ⟧C) (λ γ  → ∣ ⟦ A ⟧T γ ∣)

-- definitionel
-- ⟦_⟧T-β1  : ∀{Γ}{γ : ⟦ Γ ⟧C} → ⟦ * ⟧T γ ≡ {!!}
-- definitionel
-- ⟦_⟧T-β2  : ∀{Γ A u v}{γ : ⟦ Γ ⟧C}
--           → ⟦ u =h v ⟧T γ ≡
--           ♭ (hom (⟦ A ⟧T γ) (⟦ u ⟧tm γ) (⟦ v ⟧tm γ))
          -- needed
semSb-T   : ∀ {Γ Δ}(A : Ty Δ)(δ : Γ ⇒ Δ)(γ : ⟦ Γ ⟧C)
          → ⟦ A [ δ ]T ⟧T γ ≡ ⟦ A ⟧T (⟦ δ ⟧S γ)

-- needed
semSb-tm  : ∀{Γ Δ}{A : Ty Δ}(a : Tm A)(δ : Γ ⇒ Δ)
          (γ : ⟦ Γ ⟧C) → subst ∣_∣ (semSb-T A δ γ) 
          (⟦ a [ δ ]tm ⟧tm γ) ≡ ⟦ a ⟧tm (⟦ δ ⟧S γ)

-- needed
semSb-S   : ∀ {Γ Δ Θ}(γ : ⟦ Γ ⟧C)(δ : Γ ⇒ Δ)
          (θ : Δ ⇒ Θ) → ⟦ θ ⊚ δ ⟧S γ ≡ 
          ⟦ θ ⟧S (⟦ δ ⟧S γ)
⟦_⟧tm-β1  : ∀{Γ A}{x : Var A}{γ : ⟦ Γ ⟧C}
          → ⟦ var x ⟧tm γ ≡ π x γ

-- définitionnel
⟦_⟧S-β1  : ∀{Γ}{γ : ⟦ Γ ⟧C} 
          → ⟦ • ⟧S γ ≡ coerce ⟦_⟧C-β1 tt

⟦_⟧S-β2  : ∀{Γ Δ}{A : Ty Δ}{δ : Γ ⇒ Δ}{γ : ⟦ Γ ⟧C}
          {a : Tm (A [ δ ]T)} → ((⟦ δ , a ⟧S )γ )
          ≡ coerce (⟦_⟧C-β2) ((⟦ δ ⟧S γ) ,,
          subst ∣_∣ (semSb-T A δ γ) (⟦ a ⟧tm γ))
          -- needed
semWk-T  : ∀ {Γ A B}(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ B ⟧T γ ∣)
          → ⟦ A +T B ⟧T (coerce ⟦_⟧C-β2 (γ ,, v)) ≡ 
          ⟦ A ⟧T γ


semWk-S  : ∀ {Γ Δ B}{γ : ⟦ Γ ⟧C}{v : ∣ ⟦ B ⟧T γ ∣}
          → (δ : Γ ⇒ Δ) → ⟦ δ +S B ⟧S 
          (coerce ⟦_⟧C-β2 (γ ,, v)) ≡ ⟦ δ ⟧S γ

-- needed
semWk-tm : ∀ {Γ A B}(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ B ⟧T γ ∣)
          → (a : Tm A) → subst ∣_∣ (semWk-T γ v) 
            (⟦ a +tm B ⟧tm (coerce ⟦_⟧C-β2 (γ ,, v))) 
              ≡ (⟦ a ⟧tm γ)
π-β1  : ∀{Γ A}(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ A ⟧T γ ∣) 
      → subst ∣_∣ (semWk-T γ v) 
        (π v0 (coerce ⟦_⟧C-β2 (γ ,, v))) ≡ v

π-β2  : ∀{Γ A B}(x : Var A)(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ B ⟧T γ ∣) 
      → subst ∣_∣ (semWk-T γ v) (π (vS {Γ} {A} {B} x) 
        (coerce ⟦_⟧C-β2 (γ ,, v))) ≡ π x γ
⟦coh⟧  : ∀{Θ} → isContr Θ → (A : Ty Θ) 
        → (θ : ⟦ Θ ⟧C) → ∣ ⟦ A ⟧T θ ∣

⟦ ε ⟧C = ⊤
⟦ Γ , A ⟧C = Σ (⟦ Γ ⟧C) (λ γ  → ∣ ⟦ A ⟧T γ ∣) 

⟦_⟧T {Γ} * γ = T
⟦_⟧T {Γ} (a =h b) γ = ⟦ a ⟧tm γ ≡ ⟦ b ⟧tm γ

⟦_⟧tm {Γ} {A} (var x) γ = π x γ
-- ici j'ai besoin de désactiver le termination checker
⟦_⟧tm {Γ} {.(A [ δ ]T)} (coh isC δ A) γ = subst ∣_∣ (sym (semSb-T A δ γ )) (⟦coh⟧ isC A (⟦ δ ⟧S γ))
-- ∣ ⟦ A [ δ ]T ⟧T γ ∣ → ∣ ⟦ A ⟧T (⟦ δ ⟧S γ) ∣
-- (⟦coh⟧ isC A (⟦ δ ⟧S γ))

⟦_⟧S {Γ} {.ε} • γ = tt
⟦_⟧S {Γ} {.(Δ , A)} (_,_ {Δ = Δ} σ {A} a) γ =
   ⟦ σ ⟧S γ ,, subst  ∣_∣ (semSb-T A σ γ) (⟦ a ⟧tm γ)

-- definitionel
⟦_⟧C-β1 = refl
-- definitionel
⟦_⟧C-β2 {Γ} {Δ} = refl
π {.(Γ , A)} {.(A +T A)} (v0 {Γ} {A}) (γ ,, v) = subst ∣_∣ (sym (semWk-T {A = A} γ v)) v 
π {.(Γ , B)} {.(A +T B)} (vS {Γ} {A} {B} x) (γ ,, v) = subst ∣_∣ (sym (semWk-T {A = A} γ v)) (π x γ)
-- (semWk-T {A = A} {B} γ v)
-- Have: ⟦ A +T B ⟧T (γ ,, v) ≡ ⟦ A ⟧T γ

-- definitionel
-- ⟦_⟧T-β1 {Γ} {γ} = {!!}
-- definitionel
-- ⟦_⟧T-β2 {Γ} {A} {u} {v} {γ} = {!!}

-- needed
semSb-T {Γ} {Δ} * δ γ = refl
semSb-T {Γ} {Δ} (a =h b) δ γ = EqEq (semSb-T _ δ γ) (semSb-tm a δ γ)(semSb-tm b δ γ)
-- rewrite (sym (semSb-tm a δ γ)) | (sym (semSb-tm b δ γ))
--    = {! !}

-- ajout
semSb-V :  {Γ : Con} {Δ : Con} {A : Ty Δ} (x : Var A) (δ : Γ ⇒ Δ) (γ : ⟦ Γ ⟧C)
 → subst ∣_∣ (semSb-T A δ γ) (⟦ x [ δ ]V ⟧tm γ) ≡ π x (⟦ δ ⟧S γ)

-- needed
semSb-tm {Γ} {Δ} {A} (var x) δ γ = semSb-V x δ γ
semSb-tm {Γ} {Δ} {.(A [ δ ]T)} (coh x δ A) δ₁ γ = {!!}


semSb-V {Γ₁} {.(_ , _)} {.(_ +T _)} v0 δ γ = {!!}
semSb-V {Δ} {.(Γ , B)} {.(A +T B)} (vS {Γ} {A} {B} x) (δ , a) γ rewrite
   (sym (semSb-V x δ γ))= {!semSb-V x δ γ!}
   -- avec UIP ça passe

-- needed
semSb-S {Γ} {Δ} {.ε} γ δ • = refl
semSb-S {Γ} {Δ} {.(_ , _)} γ δ (sΘ , a) = {!semSb-S γ δ sΘ!}


⟦_⟧tm-β1 {Γ} {A} {x} {γ} = refl

-- définitionnel
⟦_⟧S-β1 {Γ} {γ} = refl

⟦_⟧S-β2 {Γ} {Δ} {A} {δ} {γ}
          {a} = refl


-- needed
semWk-T {Γ} {*} {B} γ v = refl
semWk-T {Γ} {_=h_ {A} a b} {B} γ v  = EqEq (semWk-T γ v) (semWk-tm γ v a) (semWk-tm γ v b)


semWk-S {Γ} {.ε} {B} {γ} {v} • = refl
semWk-S {Γ} {.(_ , _)} {B} {γ} {v} (δ , a) = {!!}

-- needed
semWk-tm {Γ} {A} {B} γ v (var x) rewrite semWk-T {A = A} γ v = refl
semWk-tm {Γ} {.(A [ δ ]T)} {B} γ v (coh x δ A) = {!!}

π-β1 {Γ} {A}  γ v rewrite (semWk-T {A = A} γ v) = refl

π-β2 {Γ} {A} {B} x γ v rewrite (semWk-T {A = A} γ v) = refl

⟦coh⟧ {.(ε , *)} c* * (a ,, b) = b
⟦coh⟧ {.(ε , *)} c* (a =h b) (u ,, v) = {!!}
-- ⟦coh⟧ {.(Γ , A , (var (vS x) =h var v0))} (ext {Γ} isC {A} x) B ((γ ,, α) ,, β) =
--   {!!}

-- on peut eliminer ce cas
⟦coh⟧ {.(Γ , A , (var (vS x) =h var v0))} (ext {Γ} isC {A} x) * ((γ ,, α) ,, β) = {!!}
⟦coh⟧ {.(Γ , A , (var (vS x) =h var v0))} (ext {Γ} isC {A} x) (_=h_ {C} a b) ((γ ,, α) ,, β) =
  {!⟦coh⟧ isC A γ!}
-- {!⟦coh⟧ isC A γ!}
  -- ⟦coh⟧ isC A γ!
