{-# OPTIONS --without-K --rewriting #-}

module Syntax where 

infix 30 _↦_
postulate  -- HIT
  _↦_ : ∀ {i} {A : Set i} → A → A → Set i

{-# BUILTIN REWRITE _↦_ #-}

data Con           : Set
data Ty            : Con → Set
data Tm            : {Γ : Con}(A : Ty Γ) → Set
data _⇒_           : Con → Con → Set
data isContr       : Con → Set

infix 4 _=h_
infixl 5 _,_ _∘_

data Con where
  ε     : Con
  _,_   : (Γ : Con)(A : Ty Γ) → Con
  
data Ty where
  *     : Ty ε
  _=h_  : {Γ : Con}{A : Ty Γ}(a b : Tm A) → Ty Γ
  _[_]T : {Γ Δ : Con} → Ty Δ → Γ ⇒ Δ → Ty Γ

data _⇒_ where
  idε : ε ⇒ ε
  _,_  : ∀{Γ Δ}(δ : Γ ⇒ Δ){A : Ty Δ}(a : Tm (A [ δ ]T)) → Γ ⇒ (Δ , A)
  π₁ : ∀ {Γ} {A : Ty Γ} → (Γ , A) ⇒ Γ
  _∘_   : ∀{Γ Δ Σ} → Δ ⇒ Σ → Γ ⇒ Δ → Γ ⇒ Σ


data Tm where
  coh : ∀ {Γ} → (A : Ty Γ) → isContr Γ → Tm A
  _[_]tm : ∀{Γ Δ}{A : Ty Δ} → Tm A → (σ : Γ ⇒ Δ) → Tm (A [ σ ]T)
  var : ∀ {Γ} (A : Ty Γ) → Tm {Γ , A} (A [ π₁ ]T)

id-sub : ∀ {Γ} → Γ ⇒ Γ
id-sub {ε} = idε
id-sub {Γ , A} = π₁ , var A

data isContr where
  c*   : isContr (ε , *)
  ext   : ∀ {Γ} {A} → {t : Tm A} → isContr Γ → isContr (Γ , A , (t [ π₁ ]tm =h var A))

postulate

  ∘T : ∀{Γ Δ Σ} (A : Ty Σ) (σ : Δ ⇒ Σ) (τ : Γ ⇒ Δ) → (A [ σ ∘ τ ]T) ↦ ((A [ σ ]T) [ τ ]T)  

{-# REWRITE ∘T #-}

postulate

  ∘t : ∀{Γ Δ Σ} {A : Ty Σ} (t : Tm A) (σ : Δ ⇒ Σ) (τ : Γ ⇒ Δ) → (t [ σ ∘ τ ]tm) ↦ ((t [ σ ]tm) [ τ ]tm)   

{-# REWRITE ∘t #-}

postulate

  ∘e : (Γ Δ Σ : Con) (A : Ty Σ) (B : Ty (Σ , A)) (σ : Δ ⇒ Σ) (τ : Γ ⇒ Δ) (t : Tm (A [ σ ]T)) → (B [ (σ ∘ τ , (t [ τ ]tm)) ]T) ↦ ((B [ σ , t ]T) [ τ ]T) 

{-# REWRITE ∘e #-}

postulate

  πc : ∀ {Γ Δ} (σ : Γ ⇒ Δ) (A : Ty Δ) (B : Ty Δ) (t : Tm (A [ σ ]T)) → ((B [ π₁ ]T) [ σ , t ]T) ↦ (B [ σ ]T)

{-# REWRITE πc #-}

postulate

  πt : ∀ {Γ Δ} (σ : Γ ⇒ Δ) (A : Ty Δ) {B : Ty Δ} (b : Tm B) (t : Tm (A [ σ ]T)) → ((b [ π₁ ]tm) [ σ , t ]tm) ↦ (b [ σ ]tm)

{-# REWRITE πt #-}

postulate

  =-sub : {Γ Δ : Con} {A : Ty Γ} (a b : Tm A) (σ : Δ ⇒ Γ) → ((a =h b) [ σ ]T) ↦ ((a [ σ ]tm) =h (b [ σ ]tm))

{-# REWRITE =-sub #-}

postulate

  vc : {Δ : Con} (A : Ty Δ) → ((var A) [ π₁ , var A ]tm) ↦ var A

{-# REWRITE vc #-}

wkT : ∀ {Γ} {A : Ty Γ} (B : Ty Γ) → Ty (Γ , A)
wkT {Γ} {A} B = B [ π₁ ]T

wk : ∀ {Γ} {A : Ty Γ} {B : Ty Γ} (t : Tm B) → Tm (wkT {Γ} {A} B)
wk t = t [ π₁ ]tm

identity : Tm {ε , * } (var {ε} * =h var {ε} *) 
identity = coh (var {ε} * =h var {ε} *) c*

arrow-con : Con
arrow-con = ε , * , wkT * , ((wk (var *) =h var (wkT *)))

comp-con : Con
--             x    y                   f                         z                      y                       z
comp-con = ε , * , wkT * , (wk (var *) =h var (wkT *)) , wkT (wkT (wkT *)) , (wk (wk (var (wkT *))) =h var (wkT (wkT (wkT *))))

-- ???!!!???!!!
-- composition : Tm {comp-con} (wk (wk (wk (wk (var *)))) =h wk (var (wkT (wkT (wkT *)))))
-- composition = coh (wk (wk (wk (wk (var *)))) =h wk (var (wkT (wkT (wkT *)))))
--               (ext (ext c*))

simple-sub : (ε , * , wkT *) ⇒ (ε , * , wkT *)
simple-sub = π₁ ∘ π₁ , wk (var *) , wk (var *)

unit-right : Tm {arrow-con} ({!!} =h {!!})
unit-right = {!!}

  where τ : (ε , * , wkT *) ⇒ (ε , *)
        τ = π₁ ∘ π₁ , wk (var *)

        id-τ : Tm ((var * =h var *) [ τ ∘ π₁ ]T)
        id-τ =  identity [ τ ∘ π₁ ]tm  
        
        σ : arrow-con ⇒ comp-con
        σ = id-sub {arrow-con} , wk (var (wkT *)) , {!Tm
      ((wk (wk (var (wkT *))) =h var (wkT (wkT (wkT *)))) [
       π₁ , var (wk (var *) =h var (wkT *)) , wk (var (wkT *)) ]T)!}



        
