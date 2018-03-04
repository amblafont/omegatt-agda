{-# OPTIONS --without-K #-}


module SemanticsEquivalences where

open import BasicSyntax
open import IdentityContextMorphisms
open import Data.Unit
open import Data.Product renaming (_,_ to _,,_)
open import Coinduction
open import Relation.Binary.PropositionalEquality hiding ([_])
open import GroupoidStructure

open import GlobularTypes


coerce : {A B : Set} → B ≡ A → A → B
coerce refl a = a

coerce' : {A B : Set} → A ≡ B → A → B
coerce' refl a = a

⊤-uni : ∀ {A : Set}{a b : A} → A ≡ ⊤ → a ≡ b
⊤-uni refl = refl

record isequiv {A B : Set} (f : A → B) : Set where
   field
      invG : B → A
      invD : B → A
      invG_eq :  (x : B) → f (invG x) ≡ x
      invD_eq :  (x : A) → invD (f x) ≡ x

open isequiv

equiv : (A : Set)(B : Set) → Set
equiv A B = Σ (B → A) isequiv

f_equiv : {A B : Set} (e : equiv A B) → B → A
f_equiv e = proj₁ e

g_equiv : {A B : Set} (e : equiv A B) → A → B
g_equiv e = invG (proj₂ e)

record Semantic  : Set₁ where
  field
    ⟦_⟧C   : Con → Set
    ⟦_⟧T   : ∀{Γ} → Ty Γ → ⟦ Γ ⟧C → Set
    ⟦_⟧tm  : ∀{Γ A} → Tm A → (γ : ⟦ Γ ⟧C) 
           →  ⟦ A ⟧T γ 
    ⟦_⟧S   : ∀{Γ Δ} → Γ ⇒ Δ → ⟦ Γ ⟧C → ⟦ Δ ⟧C
    π      : ∀{Γ A} → Var A → (γ : ⟦ Γ ⟧C) 
           →  ⟦ A ⟧T γ 
           -- definitionel
    ⟦_⟧C-β1  : equiv ⟦ ε ⟧C  ⊤
    -- definitionel
    ⟦_⟧C-β2  : ∀ {Γ A} → equiv (⟦ (Γ , A) ⟧C)  
             (Σ (⟦ Γ ⟧C) (λ γ  →  ⟦ A ⟧T γ ))
    
-- definitionel
    -- ⟦_⟧T-β1  : ∀{Γ}{γ : ⟦ Γ ⟧C} → ⟦ * ⟧T γ ≡ G
    -- definitionel

    -- ⟦_⟧T-β2  : ∀{Γ A u v}{γ : ⟦ Γ ⟧C}
    --          → ⟦ u =h v ⟧T γ ≡
    --          ♭ (hom (⟦ A ⟧T γ) (⟦ u ⟧tm γ) (⟦ v ⟧tm γ))
             -- needed
    semSb-T   : ∀ {Γ Δ}(A : Ty Δ)(δ : Γ ⇒ Δ)(γ : ⟦ Γ ⟧C)
              → equiv (⟦ A [ δ ]T ⟧T γ)  (⟦ A ⟧T (⟦ δ ⟧S γ))

-- needed
    semSb-tm  : ∀{Γ Δ}{A : Ty Δ}(a : Tm A)(δ : Γ ⇒ Δ)
              (γ : ⟦ Γ ⟧C) →  
              g_equiv (semSb-T A δ γ)(⟦ a [ δ ]tm ⟧tm γ) ≡ (⟦ a ⟧tm (⟦ δ ⟧S γ))

-- needed
    semSb-S   : ∀ {Γ Δ Θ}(γ : ⟦ Γ ⟧C)(δ : Γ ⇒ Δ)
              (θ : Δ ⇒ Θ) → ⟦ θ ⊚ δ ⟧S γ ≡ 
              ⟦ θ ⟧S (⟦ δ ⟧S γ)
    ⟦_⟧tm-β1  : ∀{Γ A}{x : Var A}{γ : ⟦ Γ ⟧C}
              → ⟦ var x ⟧tm γ ≡ π x γ

-- définitionnel inutile : c'est l'objet terminal
    -- ⟦_⟧S-β1  : ∀{Γ}{γ : ⟦ Γ ⟧C} 
    --          → ⟦ • ⟧S γ ≡ coerce ⟦_⟧C-β1 tt

    ⟦_⟧S-β2  : ∀{Γ Δ}{A : Ty Δ}{δ : Γ ⇒ Δ}{γ : ⟦ Γ ⟧C}
             {a : Tm (A [ δ ]T)} → ((⟦ δ , a ⟧S )γ )
             ≡ f_equiv (⟦_⟧C-β2) ((⟦ δ ⟧S γ) ,,
                g_equiv (semSb-T A δ γ) (⟦ a ⟧tm γ))
             -- needed
    semWk-T  : ∀ {Γ A B}(γ : ⟦ Γ ⟧C)(v :  ⟦ B ⟧T γ )
             → ⟦ A +T B ⟧T (f_equiv ⟦_⟧C-β2 (γ ,, v)) ≡ 
             ⟦ A ⟧T γ
  

    semWk-S  : ∀ {Γ Δ B}{γ : ⟦ Γ ⟧C}{v :  ⟦ B ⟧T γ }
             → (δ : Γ ⇒ Δ) → ⟦ δ +S B ⟧S 
             (f_equiv ⟦_⟧C-β2 (γ ,, v)) ≡ ⟦ δ ⟧S γ

-- needed
    semWk-tm : ∀ {Γ A B}(γ : ⟦ Γ ⟧C)(v :  ⟦ B ⟧T γ )
             → (a : Tm A) → coerce'  (semWk-T γ v) 
               (⟦ a +tm B ⟧tm (f_equiv ⟦_⟧C-β2 (γ ,, v))) 
                 ≡ (⟦ a ⟧tm γ)
    π-β1  : ∀{Γ A}(γ : ⟦ Γ ⟧C)(v :  ⟦ A ⟧T γ ) 
          → coerce' (semWk-T γ v) 
            (π v0 (f_equiv ⟦_⟧C-β2 (γ ,, v))) ≡ v

    π-β2  : ∀{Γ A B}(x : Var A)(γ : ⟦ Γ ⟧C)(v :  ⟦ B ⟧T γ ) 
          → coerce' (semWk-T γ v) (π (vS {Γ} {A} {B} x) 
            (f_equiv ⟦_⟧C-β2 (γ ,, v))) ≡ π x γ

-- intuile
    -- ⟦coh⟧  : ∀{Θ} → isContr Θ → (A : Ty Θ) 
    --        → (θ : ⟦ Θ ⟧C) →  ⟦ A ⟧T θ 
