{-# OPTIONS --without-K --no-termination-check --rewriting #-}


module BasicSyntax where 


open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Product renaming (_,_ to _,,_)

-- # BUILTIN EQUALITY _≡_  #

infix 4 _≅_
infix 4 _=h_
-- infixl 6 _+T_ _+S_ _+tm_
infixl 5 _,_
-- infixl 7 _⊚_

data Con           : Set
data Ty (Γ : Con)  : Set
data Tm            : {Γ : Con}(A : Ty Γ) → Set
-- data Var           : {Γ : Con}(A : Ty Γ) → Set
data _⇒_           : Con → Con → Set
data isContr       : Con → Set
data Con where
  ε     : Con
  _,_   : (Γ : Con)(A : Ty Γ) → Con
data Ty Γ where
  *     : Ty Γ
  _=h_  : {A : Ty Γ}(a b : Tm A) → Ty Γ
  _[_]T : {Δ : Con} → Ty Δ → Γ ⇒ Δ → Ty Γ

data _≅_ {Γ : Con}{A : Ty Γ} :
         {B : Ty Γ} → Tm A → Tm B → Set where
  refl : (b : Tm A) → b ≅ b



Tms : Con → Con → Set
Tms G G' = G ⇒ G'

data _⇒_ where
  •    : ∀{Γ} → Γ ⇒ ε
  _,_  : ∀{Γ Δ}(δ : Γ ⇒ Δ){A : Ty Δ}(a : Tm (A [ δ ]T)) → Γ ⇒ (Δ , A)
  π₁    : ∀{Γ Δ}{A : Ty Δ} → Γ ⇒ (Δ , A) →  Γ ⇒ Δ
  idTms    : ∀{Γ} → Γ ⇒ Γ
  _■_   : ∀{Γ Δ Σ} → Tms Δ Σ → Tms Γ Δ → Tms Γ Σ

data Tm where
  coh  : ∀{Γ Δ} → isContr Δ → (δ : Γ ⇒ Δ) 
       → (A : Ty Δ) → Tm (A [ δ ]T)
  _[_]tm : ∀{Γ Δ}{A : Ty Δ} → Tm A → (σ : Γ ⇒ Δ) → Tm (A [ σ ]T) 
  π₂    : ∀{Γ Δ}{A : Ty Δ}(σ : Γ ⇒ (Δ , A)) → Tm (A [ π₁ σ ]T)

wk : ∀{Γ}{A : Ty Γ} → (Γ , A) ⇒ Γ
wk = π₁ idTms

vz : ∀{Γ}{A : Ty Γ} → Tm {(Γ , A)} (A [ wk ]T)
vz = π₂ idTms

data isContr where
  c*   : isContr (ε , *)
  ext   : ∀ {Γ} {A} → {t : Tm A} → isContr Γ → isContr (Γ , A , ((t [ wk ]tm) =h vz) )


postulate
  [id]T : ∀{Γ}{A : Ty Γ} → A [ idTms ]T ≡ A
  [][]T : ∀{Γ Δ Σ}{A : Ty Σ}{σ : Γ ⇒ Δ}{δ : Δ ⇒ Σ}
    → (A [ δ ]T [ σ ]T) ≡ (A [ δ ■ σ ]T)

  idl   : ∀{Γ Δ}{δ : Tms Γ Δ} → (idTms ■ δ) ≡ δ 
  idr   : ∀{Γ Δ}{δ : Tms Γ Δ} → (δ ■ idTms) ≡ δ 
  ass   : ∀{Γ Δ Σ Ω}{σ : Tms Σ Ω}{δ : Tms Δ Σ}{ν : Tms Γ Δ}
    → ((σ ■ δ) ■ ν) ≡ (σ ■ (δ ■ ν))
  π₁β   : ∀{Γ Δ}{A : Ty Δ}{δ : Tms Γ Δ}{a : Tm (A [ δ ]T)}
    → (π₁ (δ ,  a)) ≡ δ
  πη    : ∀{Γ Δ}{A : Ty Δ}{δ : Tms Γ (Δ , A)}
    → (π₁ δ ,  π₂ δ) ≡ δ
  εη    : ∀{Γ}{σ : Tms Γ ε}
    → σ ≡ •

{-# REWRITE [id]T #-}
{-# REWRITE [][]T #-}
{-# REWRITE idl #-}
{-# REWRITE idr #-}
{-# REWRITE ass #-}
{-# REWRITE π₁β #-}
{-# REWRITE πη #-}
{-# REWRITE εη #-}

  -- ,∘    : ∀{Γ Δ Σ}{δ : Tms Γ Δ}{σ : Tms Σ Γ}{A : Ty Δ}{a : Tm Γ (A [ δ ]T)}
  --   → ((δ ,  a) ■ σ) ≡ ((δ ■ σ) ,  coe (TmΓ= [][]T) (a [ σ ]t))
  -- π₂β   : ∀{Γ Δ}{A : Ty Δ}{δ : Γ  ⇒ Δ}{a : Tm Γ (A [ δ ]T)}
  --   → π₂ (δ ,  a) ≡[ TmΓ= ([]T=′ refl refl refl π₁β) ]≡ a

