{-# OPTIONS --without-K --rewriting #-}

module Syntax where 

infix 30 _↦_
postulate  -- HIT
  _↦_ : ∀ {i} {A : Set i} → A → A → Set i

{-# BUILTIN REWRITE _↦_ #-}

data Con           : Set
data Ty (Γ : Con)  : Set
data Tm            : {Γ : Con}(A : Ty Γ) → Set
-- data Var           : {Γ : Con}(A : Ty Γ) → Set
data _⇒_           : Con → Con → Set
data isContr       : Con → Set

infix 4 _=h_
infixl 5 _,_

data Con where
  ε     : Con
  _,_   : (Γ : Con)(A : Ty Γ) → Con
  
data Ty Γ where
  *     : Ty Γ
  _=h_  : {A : Ty Γ}(a b : Tm A) → Ty Γ
  _[_]T : {Δ : Con} → Ty Δ → Γ ⇒ Δ → Ty Γ

data _⇒_ where
  -- •    : ∀{Γ} → Γ ⇒ ε
  _,_  : ∀{Γ Δ}(δ : Γ ⇒ Δ){A : Ty Δ}(a : Tm (A [ δ ]T)) → Γ ⇒ (Δ , A)
  π₁ : ∀ {Γ} {A : Ty Γ} → (Γ , A) ⇒ Γ
  -- idTms    : ∀{Γ} → Γ ⇒ Γ
  -- _■_   : ∀{Γ Δ Σ} → Tms Δ Σ → Tms Γ Δ → Tms Γ Σ

-- id-sub : ∀ {Γ} → Γ ⇒ Γ
-- id-sub {ε} = •
-- id-sub {Γ , A} = π₁ , var {Γ} A

-- π₁ : ∀ {Γ} {A : Ty Γ} → (Γ , A) ⇒ Γ
-- π₁ {Γ} {A} with id-sub {Γ , A}
-- π₁ {Γ} {A} | x , a = x

data Tm where
  coh : ∀ {Γ} → (A : Ty Γ) → isContr Γ → Tm A
  _[_]tm : ∀{Γ Δ}{A : Ty Δ} → Tm A → (σ : Γ ⇒ Δ) → Tm (A [ σ ]T)
  var : ∀ {Γ} (A : Ty Γ) → Tm {Γ , A} (A [ π₁ ]T)


data isContr where
  c*   : isContr (ε , *)
  ext   : ∀ {Γ} {A} → {t : Tm A} → isContr Γ → isContr (Γ , A , (var A =h (t [ π₁ ]tm) ))

wkT : ∀ {Γ} {A : Ty Γ} (B : Ty Γ) → Ty (Γ , A)
wkT {Γ} {A} B = B [ π₁ ]T

wk : ∀ {Γ} {A : Ty Γ} {B : Ty Γ} (t : Tm B) → Tm (wkT {Γ} {A} B)
wk t = t [ π₁ ]tm

vz : ∀ {Γ} {A : Ty Γ} → Tm {Γ , A} (A [ π₁ ]T)
vz {Γ} {A} = var A

vs : ∀ {Γ} {A B : Ty Γ} (t : Tm A) → Tm {Γ , B} (wkT A)
vs t = {!!}

identity : Tm {ε , * } (var {ε} * =h var {ε} *) 
identity = coh (var {ε} * =h var {ε} *) c*

composition : Tm {ε , * , wkT * , (var (wkT *) =h (wk (var *))) , wkT (wkT *) , (var {!!} =h wk (wk {!!}))} {!!}
composition = {!!}
  
