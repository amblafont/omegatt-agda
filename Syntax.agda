{-# OPTIONS --without-K --rewriting #-}

module Syntax where 

infix 30 _↦_
postulate  -- HIT
  _↦_ : ∀ {i} {A : Set i} → A → A → Set i

{-# BUILTIN REWRITE _↦_ #-}

data Con           : Set
data Ty (Γ : Con)  : Set
data Tm            : {Γ : Con}(A : Ty Γ) → Set
data _⇒_           : Con → Con → Set
data isContr       : Con → Set

infix 4 _=h_
infixl 5 _,_ _∘_

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
  _∘_   : ∀{Γ Δ Σ} → Δ ⇒ Σ → Γ ⇒ Δ → Γ ⇒ Σ

-- id-sub : ∀ {Γ} → Γ ⇒ Γ
-- id-sub {ε} = •
-- id-sub {Γ , A} = π₁ , var {Γ} A

-- π₁ : ∀ {Γ} {A : Ty Γ} → (Γ , A) ⇒ Γ
-- π₁ {Γ} {A} with id-sub {Γ , A}
-- π₁ {Γ} {A} | x , a = x

-- _∘'_   : ∀{Γ Δ Σ} → Δ ⇒ Σ → Γ ⇒ Δ → Γ ⇒ Σ
-- σ ∘' τ = {!!}

data Tm where
  coh : ∀ {Γ} → (A : Ty Γ) → isContr Γ → Tm A
  _[_]tm : ∀{Γ Δ}{A : Ty Δ} → Tm A → (σ : Γ ⇒ Δ) → Tm (A [ σ ]T)
  var : ∀ {Γ} (A : Ty Γ) → Tm {Γ , A} (A [ π₁ ]T)

data isContr where
  c*   : isContr (ε , *)
  ext   : ∀ {Γ} {A} → {t : Tm A} → isContr Γ → isContr (Γ , A , (t [ π₁ ]tm =h var A))

postulate

  ∘T : ∀{Γ Δ Σ} (A : Ty Σ) (σ : Δ ⇒ Σ) (τ : Γ ⇒ Δ) → (A [ σ ∘ τ ]T) ↦ ((A [ σ ]T) [ τ ]T)

{-# REWRITE ∘T #-}

-- postulate

--   ∘e : ∀{Γ Δ Σ} (A : Ty Σ) (B : Ty (Σ , A)) (σ : Δ ⇒ Σ) (τ : Γ ⇒ Δ) (t : Tm (A [ σ ]T)) → (B [ (σ ∘ τ , (t [ τ ]tm)) ]T) ↦ ((B [ σ , t ]T) [ τ ]T)

-- {-# REWRITE ∘e #-}




wkT : ∀ {Γ} {A : Ty Γ} (B : Ty Γ) → Ty (Γ , A)
wkT {Γ} {A} B = B [ π₁ ]T

wk : ∀ {Γ} {A : Ty Γ} {B : Ty Γ} (t : Tm B) → Tm (wkT {Γ} {A} B)
wk t = t [ π₁ ]tm

vz : ∀ {Γ} {A : Ty Γ} → Tm {Γ , A} (A [ π₁ ]T)
vz {Γ} {A} = var A

identity : Tm {ε , * } (var {ε} * =h var {ε} *) 
identity = coh (var {ε} * =h var {ε} *) c*

arrow-con : Con
arrow-con = ε , * , wkT * , ((wk (var *) =h var (wkT *)))

comp-con : Con
--             x    y                   f                         z                      y                       z
comp-con = ε , * , wkT * , (wk (var *) =h var (wkT *)) , wkT (wkT (wkT *)) , (wk (wk (var (wkT *))) =h var (wkT (wkT (wkT *))))

composition : Tm {comp-con} (wk (wk (wk (wk (var *)))) =h wk (var (wkT (wkT (wkT *)))))
composition = coh (wk (wk (wk (wk (var *)))) =h wk (var (wkT (wkT (wkT *)))))
              (ext (ext c*))


unit-right : Tm {arrow-con} ({!!} =h {!!})
unit-right = {!!}

  where σ : arrow-con ⇒ comp-con
        σ = π₁ ∘ (π₁ ∘ π₁) , wk (wk (var *)) , {!Tm (wkT * [ π₁ ∘ (π₁ ∘ π₁) , wk (wk (var *)) ]T)!} , {!!} , {!!} , {!!}
