{-# OPTIONS --without-K --no-termination-check #-}


module Semantics (T : Set) where

open import BasicSyntax
open import IdentityContextMorphisms
-- open import Data.Unit
-- open import Data.Product renaming (_,_ to _,,_)
open import Coinduction
open import GroupoidStructure
open import lib

-- open import GlobularType (∣_∣ to 〚_〛)

postulate
   uip : {l : _} {A : Set l} {a : A} {b : A} (e : a ≡ b) (e' : a ≡ b) → e ≡ e'

∣_∣ : {A : Set₁} → A → A
∣ x ∣ = x

coerce : {A B : Set} → B ≡ A → A → B
coerce refl a = a

-- subst : ∀{ℓ ℓ'}{A : Set ℓ}(P : A → Set ℓ'){x y : A}(p : x ≡ y) → P x → P y
-- subst = transport

-- coe : {A B : Set} → B ≡ A → B → A
-- coe p a = subst (λ x → x) p a

⊤-uni : ∀ {A : Set}{a b : A} → A ≡ ⊤ → a ≡ b
⊤-uni refl = refl

-- inspiré de EqHom
-- EqHom : {A B : Glob} → (p : A ≡ B) → {x y : ∣ A ∣} → {m n : ∣ B ∣} → (subst ∣_∣ p x ≡ m) → (subst ∣_∣ p y ≡ n) → ♭ (hom A x y) ≡ ♭ (hom B m n)
-- EqHom {.B} {B} refl {.m} {.n} {m} {n} refl refl = refl
EqEq : {A B : Set} → (p : A ≡ B) → {x y : A} → {m n : B} → (subst ∣_∣ p x ≡ m)
  → (subst ∣_∣ p y ≡ n) → (x ≡ y) ≡ (m ≡ n)
EqEq {.B} {B} refl {.m} {.n} {m} {n} refl refl = refl

-- postulate
--    T : Set

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

-- semSb-[⊚]T   : ∀{Γ Δ Θ A}{θ : Δ ⇒ Θ}{δ : Γ ⇒ Δ} ∀ {Γ Δ}(A : Ty Δ)(δ : Γ ⇒ Δ)(γ : ⟦ Γ ⟧C)
--   → ⟦ A [ δ ]T ⟧T γ ≡ ⟦ A ⟧T (⟦ δ ⟧S γ)
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
          ≡ coerce (⟦_⟧C-β2) ((⟦ δ ⟧S γ) ,Σ
          subst ∣_∣ (semSb-T A δ γ) (⟦ a ⟧tm γ))
          -- needed
semWk-T  : ∀ {Γ A B}(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ B ⟧T γ ∣)
          → ⟦ A +T B ⟧T (coerce ⟦_⟧C-β2 (γ ,Σ v)) ≡ 
          ⟦ A ⟧T γ


semWk-S  : ∀ {Γ Δ B}{γ : ⟦ Γ ⟧C}{v : ∣ ⟦ B ⟧T γ ∣}
          → (δ : Γ ⇒ Δ) → ⟦ δ +S B ⟧S 
          (coerce ⟦_⟧C-β2 (γ ,Σ v)) ≡ ⟦ δ ⟧S γ

-- needed
semWk-tm : ∀ {Γ A B}(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ B ⟧T γ ∣)
          → (a : Tm A) → subst ∣_∣ (semWk-T γ v) 
            (⟦ a +tm B ⟧tm (coerce ⟦_⟧C-β2 (γ ,Σ v))) 
              ≡ (⟦ a ⟧tm γ)
π-β1  : ∀{Γ A}(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ A ⟧T γ ∣) 
      → subst ∣_∣ (semWk-T γ v) 
        (π v0 (coerce ⟦_⟧C-β2 (γ ,Σ v))) ≡ v

π-β2  : ∀{Γ A B}(x : Var A)(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ B ⟧T γ ∣) 
      → subst ∣_∣ (semWk-T γ v) (π (vS {Γ} {A} {B} x) 
        (coerce ⟦_⟧C-β2 (γ ,Σ v))) ≡ π x γ
⟦coh⟧  : ∀{Θ} → isContr Θ → (A : Ty Θ) 
        → (θ : ⟦ Θ ⟧C) → ∣ ⟦ A ⟧T θ ∣

⟦ ε ⟧C = ⊤
⟦ Γ , A ⟧C = Σ (⟦ Γ ⟧C) (λ γ  → ∣ ⟦ A ⟧T γ ∣) 

⟦_⟧T {Γ} * γ = T
-- T
⟦_⟧T {Γ} (a =h b) γ = ⟦ a ⟧tm γ ≡ ⟦ b ⟧tm γ

⟦_⟧tm {Γ} {A} (var x) γ = π x γ
-- ici j'ai besoin de désactiver le termination checker
⟦_⟧tm {Γ} {.(A [ δ ]T)} (coh isC δ A) γ = subst ∣_∣ (sym (semSb-T A δ γ )) (⟦coh⟧ isC A (⟦ δ ⟧S γ))
-- ∣ ⟦ A [ δ ]T ⟧T γ ∣ → ∣ ⟦ A ⟧T (⟦ δ ⟧S γ) ∣
-- (⟦coh⟧ isC A (⟦ δ ⟧S γ))

⟦_⟧S {Γ} {.ε} • γ = tt
⟦_⟧S {Γ} {.(Δ , A)} (_,_ {Δ = Δ} σ {A} a) γ =
   ⟦ σ ⟧S γ ,Σ subst  ∣_∣ (semSb-T A σ γ) (⟦ a ⟧tm γ)

-- definitionel
⟦_⟧C-β1 = refl
-- definitionel
⟦_⟧C-β2 {Γ} {Δ} = refl
π {.(Γ , A)} {.(A +T A)} (v0 {Γ} {A}) (γ ,Σ v) = subst ∣_∣ (sym (semWk-T {A = A} γ v)) v 
π {.(Γ , B)} {.(A +T B)} (vS {Γ} {A} {B} x) (γ ,Σ v) = subst ∣_∣ (sym (semWk-T {A = A} γ v)) (π x γ)
-- (semWk-T {A = A} {B} γ v)
-- Have: ⟦ A +T B ⟧T (γ ,, v) ≡ ⟦ A ⟧T γ

-- definitionel
-- ⟦_⟧T-β1 {Γ} {γ} = {!!}
-- definitionel
-- ⟦_⟧T-β2 {Γ} {A} {u} {v} {γ} = {!!}

-- needed
semSb-T {Γ} {Δ} * δ γ = refl
semSb-T {Γ} {Δ} (_=h_ {A} a b) δ γ = EqEq (semSb-T A δ γ) (semSb-tm a δ γ)(semSb-tm b δ γ)
-- EqEq (semSb-T _ δ γ) (semSb-tm a δ γ)(semSb-tm b δ γ)
-- rewrite (sym (semSb-tm a δ γ)) | (sym (semSb-tm b δ γ))
--    = {! !}

-- ajout
semSb-V :  {Γ : Con} {Δ : Con} {A : Ty Δ} (x : Var A) (δ : Γ ⇒ Δ) (γ : ⟦ Γ ⟧C)
 → subst ∣_∣ (semSb-T A δ γ) (⟦ x [ δ ]V ⟧tm γ) ≡ π x (⟦ δ ⟧S γ)

-- needed
semSb-tm {Γ} {Δ} {A} (var x) δ γ = semSb-V x δ γ
semSb-tm {Γ} {Δ} {.(A [ δ ]T)} (coh x δ A) δ₁ γ = {!!}


coh-≅ : {Γ : Con}{A : Ty Γ} {B : Ty Γ} {t : Tm A} {u : Tm B} (e : t ≅ u)
  (γ : ⟦ Γ ⟧C) → subst (λ x → ⟦ x ⟧T γ) (≅≡ e) (⟦ t ⟧tm γ) ≡ ⟦ u ⟧tm γ  

coh-≅ (refl b) γ = refl

-- autre manière de le voir
sem-cohOp : {Γ : Con}{A B : Ty Γ}{a : Tm B}(p : A ≡ B) (γ : ⟦  Γ ⟧C)
   → coe (ap (λ x → ⟦ x ⟧T γ) p)  (⟦ a ⟦ p ⟫ ⟧tm γ) ≡ ⟦ a ⟧tm γ  

sem-cohOp refl γ = refl



-- corrolaire
sem-wk-tm : {Γ Δ : Con}
  {A : Ty Δ}{δ : Γ ⇒ Δ}
  {B : Ty Δ}(b : Tm (B [ δ ]T))  
  (t : Tm (A [ δ ]T)) (γ : ⟦ Γ ⟧C) →
   coe (ap (λ x → ⟦ x ⟧T γ) (+T[,]T {A = A} {b = b}))
     (⟦ wk-tm {b = b} t ⟧tm γ) ≡ ⟦ t ⟧tm γ

sem-wk-tm {A = A} b t γ = sem-cohOp  (+T[,]T {A = A} {b = b}) γ

-- subst
-- open ≡-Reasoning
semSb-V {Γ} {.(Γ₁ , A)} {.(A +T A)} (v0 {Γ₁} {A}) (δ , a) γ  = 
    {-

Je dois montrer la commutativité de ce diagramme :

                         semSb-T
       ⟦ wk A [δ, A] ⟧ γ ---------> ⟦ wk A ⟧ o ⟦ δ , a ⟧ γ
              |                              |
              |                              |
              |                              |
     +T[,]T   |                              |  semWk ( ⟦ wk A ⟧ (γ , A) = ⟦ A ⟧ γ)
              |                              |
              |                              |
              |                              |
              V                              V
          ⟦ A [δ] ⟧ γ    --------->     ⟦ A ⟧ o ⟦ δ ⟧ γ
                         semSb-T

je le fais par uip
    -}
    _  ≡⟨
    (ap (λ x → coe x (⟦ wk-tm {A = A} {B = A} {b = a} a ⟧tm γ))
    (uip (ap ∣_∣ (semSb-T (A +T A) (δ , a) γ))
    (ap (λ x → ⟦ x ⟧T γ) (+T[,]T {A = A} {B = A} {b = a}) ◾
    (ap ∣_∣ (semSb-T A δ γ) ◾
    ap ∣_∣
    (sym
    (semWk-T {A = A} (⟦ δ ⟧S γ) (subst ∣_∣ (semSb-T A δ γ) (⟦ a ⟧tm γ))))))
      ))

    ◾
    -- (ap (λ x → subst ∣_∣ x (⟦ wk-tm {A = A} {B = A} {b = a} a ⟧tm γ)) {!uip _ _!}) ◾ 
    coecoe (ap (λ x → ⟦ x ⟧T γ) (+T[,]T {A = A} {B = A} {b = a})) (ap ∣_∣ (semSb-T A δ γ) ◾
    ap ∣_∣
    (sym (semWk-T {A = A} (⟦ δ ⟧S γ) (subst ∣_∣ (semSb-T A δ γ) (⟦ a ⟧tm γ)))))
        {(⟦ wk-tm a ⟧tm γ)} ⁻¹
    ◾ coecoe 
    (ap ∣_∣ (semSb-T A δ γ))
    (ap ∣_∣ (sym (semWk-T {A = A} (⟦ δ ⟧S γ) (subst ∣_∣ (semSb-T A δ γ) (⟦ a ⟧tm γ)))))
      {coe (ap (λ x → ⟦ x ⟧T γ) (+T[,]T  {A = A})) (⟦ wk-tm a ⟧tm γ) }   ⁻¹  ⟩
     ap (λ x → subst ∣_∣  (sym (semWk-T {A = A} (⟦ δ ⟧S γ) (subst ∣_∣ (semSb-T A δ γ) (⟦ a ⟧tm γ))))
        (subst ∣_∣ (semSb-T A δ γ) x)) (sem-wk-tm {A = A} a a γ)

     -- ap (λ x → subst ∣_∣  (sym (semWk-T (⟦ δ ⟧S γ) (subst ∣_∣ (semSb-T A δ γ) (⟦ a ⟧tm γ))))
     --    (subst ∣_∣ (semSb-T A δ γ) x)) (sem-wk-tm a a γ)

     -- cong (λ x → subst ∣_∣  _ (subst ∣_∣ (semSb-T A δ γ) x)) (sem-wk-tm a a γ)
   
   -- ? _ ≡⟨ ? ⟩ ?
   -- sym (sem-wk-tm a a γ)!}
semSb-V {Δ} {.(Γ , B)} {.(A +T B)} (vS {Γ} {A} {B} x) (δ , a) γ =
 -- c'est le même diagramme de cohérence que pour v0
  
-- uip
  ap (λ e → coe e (⟦ wk-tm (x [ δ ]V) ⟧tm γ))
  (uip (ap ∣_∣ (semSb-T (A +T B) (δ , a) γ))
  (ap (λ x₁ → ⟦ x₁ ⟧T γ) (+T[,]T {A = A} {B = B}) ◾
    (ap ∣_∣ (semSb-T A δ γ) ◾
    ap ∣_∣
    (sym
    (semWk-T {A = A} {B = B} (⟦ δ ⟧S γ) (subst ∣_∣ (semSb-T B δ γ) (⟦ a ⟧tm γ))))))
  )
  
  
  ◾
  -- applatissement
  coecoe
  (ap (λ x₁ → ⟦ x₁ ⟧T γ) (+T[,]T {A = A} {B = B}))
 (ap ∣_∣ (semSb-T A δ γ) ◾
  ap ∣_∣ (sym (semWk-T {A = A} {B = B}   (⟦ δ ⟧S γ) (subst ∣_∣ (semSb-T B δ γ) (⟦ a ⟧tm γ)))))
  ⁻¹

  

  ◾
  -- applatissement
  coecoe (ap ∣_∣ (semSb-T A δ γ))
    (ap ∣_∣ (sym (semWk-T {A = A} {B = B}   (⟦ δ ⟧S γ) (subst ∣_∣ (semSb-T B δ γ) (⟦ a ⟧tm γ)))))
    ⁻¹
      
  ◾
  ap
  (λ e →       subst ∣_∣
  (sym (semWk-T {A = A} {B = B}   (⟦ δ ⟧S γ) (subst ∣_∣ (semSb-T B δ γ) (⟦ a ⟧tm γ))))
  (subst ∣_∣ (semSb-T A δ γ) e)
  )
  (sem-wk-tm a (x [ δ ]V) γ) 
  
  -- (subst ∣_∣ (semSb-T B δ γ) e)
  -- {!sem-wk-tm _ (x [ δ ]V) γ!}
  ◾
  -- utilisation de l'hypothèse de récurrence
  ap (λ e →  subst ∣_∣
  (sym (semWk-T {A = A} {B = B} (⟦ δ ⟧S γ) (subst ∣_∣ (semSb-T B δ γ) (⟦ a ⟧tm γ))))
  e
  ) ((semSb-V x δ γ) )
  -- {!? ◾ ? (semSb-V x δ γ) ⁻¹!}
-- with (sym (semSb-V x δ γ))
-- ... | p = {! p!}
-- rewrite
--    (sym (semSb-V x δ γ))= {!semSb-V x δ γ!}
   -- avec UIP ça passe

-- needed
semSb-S {Γ} {Δ} {.ε} γ δ • = refl
semSb-S {Γ} {Δ} {.(Δ₁ , A)} γ δ (_,_ {Δ = Δ₁} sΘ {A} a) =
  ,Σ= (semSb-S γ δ sΘ)
  -- on réécrit
  -- (⟦ (a [ δ ]tm) ⟦ [⊚]T ⟫ ⟧tm γ)
  -- en utilisant sem-cohOp
    (
    ap (λ x → coe (ap (λ γ₁ → ∣ ⟦ A ⟧T γ₁ ∣) (semSb-S γ δ sΘ))
       (subst ∣_∣ (semSb-T A (sΘ ⊚ δ) γ) x)
   )
  ( coe2r {B = (λ x → ⟦ x ⟧T γ)} ([⊚]T {A = A})
   (sem-cohOp { a = (a [ δ ]tm)}  ([⊚]T ) γ))
   
    ◾
    -- utilisation de semSb-tm
    ( ap (λ x → coe (ap (λ γ₁ → ∣ ⟦ A ⟧T γ₁ ∣) (semSb-S γ δ sΘ))
    (subst ∣_∣ (semSb-T A (sΘ ⊚ δ) γ) (coe (ap (λ x → ⟦ x ⟧T γ) ([⊚]T {A = A} ⁻¹)) x)
    )
    )
    (coe2r {B = ∣_∣} (semSb-T (A [ sΘ ]T) δ γ)
    (semSb-tm a δ γ ))
 
    ◾
    {-
    On doit vérifier le diagramme suivant : 

                        semSb-S
  ⟦ A [ σ ⊚ δ ] ⟧ γ ----------------> ⟦ A [σ][δ] ⟧ γ
         |                                   |
         |                                   |
 semSb-T |                                   |
         |                                   |
         V                                   |
  ⟦ A ⟧ o ⟦ σ ⊚ δ ⟧ γ                             semSb-T
         |                                   |
         |                                   |
 semSb-S |                                   |
         |                                   |
         V                                   V
  ⟦ A ⟧ o ⟦ σ ⟧ o ⟦ δ ⟧ γ  <----------  ⟦ A [σ] ⟧ o ⟦ δ ⟧ γ
                              semSb-T


J'utilise uip pour le démontrer

-}
    -- aplatissement
    (
    coecoe
    (ap ∣_∣ (semSb-T A (sΘ ⊚ δ) γ))
    (ap (λ γ₁ → ∣ ⟦ A ⟧T γ₁ ∣) (semSb-S γ δ sΘ))
    ◾
    (
    coecoe
    (ap (λ x → ⟦ x ⟧T γ) ([⊚]T {A = A}⁻¹))
    (ap ∣_∣ (semSb-T A (sΘ ⊚ δ) γ) ◾
    ap (λ γ₁ → ∣ ⟦ A ⟧T γ₁ ∣) (semSb-S γ δ sΘ))
    ◾
    (coecoe
       (ap ∣_∣ (semSb-T (A [ sΘ ]T) δ γ ⁻¹))
       (ap (λ x → ⟦ x ⟧T γ) ([⊚]T {A = A} ⁻¹) ◾
        (ap ∣_∣ (semSb-T A (sΘ ⊚ δ) γ) ◾
        ap (λ γ₁ → ∣ ⟦ A ⟧T γ₁ ∣) (semSb-S γ δ sΘ)))
     ◾
     -- ici uip
     ap (λ e → coe e (⟦ a ⟧tm (⟦ δ ⟧S γ)))
     (uip
     (ap ∣_∣ (semSb-T (A [ sΘ ]T) δ γ ⁻¹) ◾
        (ap (λ x → ⟦ x ⟧T γ) ([⊚]T {A = A}⁻¹) ◾
        (ap ∣_∣ (semSb-T A (sΘ ⊚ δ) γ) ◾
        ap (λ γ₁ → ∣ ⟦ A ⟧T γ₁ ∣) (semSb-S γ δ sΘ))))
     (ap ∣_∣ (semSb-T A sΘ (⟦ δ ⟧S γ)))
     )
     
  )
    )
      )
      -- Have: ⟦ a ⟧tm (⟦ δ ⟧S γ) ≡
      -- subst ∣_∣ (semSb-T (A [ sΘ ]T) δ γ) (⟦ a [ δ ]tm ⟧tm γ)
      -- (semSb-tm a δ γ)
       ))
-- {!,Σ= (semSb-S γ δ sΘ)!}
-- semSb-S {Γ} {Δ} {.(_ , _)} γ δ (sΘ , a) = {!semSb-S γ δ sΘ!}


⟦_⟧tm-β1 {Γ} {A} {x} {γ} = refl

-- définitionnel
⟦_⟧S-β1 {Γ} {γ} = refl

⟦_⟧S-β2 {Γ} {Δ} {A} {δ} {γ}
          {a} = refl


-- needed
semWk-T {Γ} {*} {B} γ v = refl
semWk-T {Γ} {_=h_ {A} a b} {B} γ v  = EqEq (semWk-T {A = A} {B = B} γ v) (semWk-tm γ v a) (semWk-tm γ v b)


semWk-S {Γ} {.ε} {B} {γ} {v} • = refl
semWk-S {Γ} {.(Δ , A)} {B} {γ} {v} (_,_ {Δ = Δ} δ {A} a)
  = ,Σ= (semWk-S {B = B} {γ = γ} {v = v} δ)
  {-
  Following commutative diagramme
                             [+S]T
    ⟦ A [ wk δ] ⟧ (γ , v)   -------->   ⟦ wk (A [δ]) ⟧ (γ, v)
          |                                   |
          |                                   |
semSb-T   |                                   |
          |                                   |
          V                                   |
    ⟦ A ⟧ o ⟦ wk δ ⟧ (γ , v)                           semWK-T
          |                                   |
          |                                   |
          |                                   |
semWk-S   |                                   |
          |                                   |
          |                                   |
          V                                   V
    ⟦ A ⟧ o ⟦ δ ⟧ (γ)  <----------------- ⟦ A [ δ ] ⟧ (γ)
                           semSb-T

by uip
  -}
    (
    -- aplatissement
    coecoe (ap ∣_∣ (semSb-T A (δ +S B) (γ ,Σ v)))(ap (λ v₁ → ∣ ⟦ A ⟧T v₁ ∣) (semWk-S δ))
      ◾
      -- uip
      ap (λ x → coe x (⟦ wk-tm+ B (a +tm B) ⟧tm (γ ,Σ v)))
       (uip (ap ∣_∣ (semSb-T A (δ +S B) (γ ,Σ v)) ◾
       ap (λ v₁ → ∣ ⟦ A ⟧T v₁ ∣) (semWk-S δ))
       (ap (λ x → ⟦ x ⟧T (γ ,Σ v)) ([+S]T {A = A} {B = B} {δ = δ}) ◾
       (ap ∣_∣ (semWk-T {A = A [ δ ]T} γ v) ◾ ap ∣_∣ (semSb-T A δ γ)))
        )
         
       ◾
       coecoe (ap (λ x → ⟦ x ⟧T (γ ,Σ v)) ([+S]T {A = A} {B = B} {δ = δ}))
           (ap ∣_∣ (semWk-T {A = A [ δ ]T} γ v) ◾ ap ∣_∣ (semSb-T A δ γ)) ⁻¹
       -- coecoe (ap (λ x → ⟦ x ⟧T (γ ,Σ v)) ([+S]T {B = B}))(ap ∣_∣ (semWk-T γ v) ◾ ap ∣_∣ (semSb-T A δ γ)) ⁻¹
  ◾
  coecoe (ap ∣_∣ (semWk-T {A = A [ δ ]T } γ v)) (ap ∣_∣ (semSb-T A δ γ))
     ⁻¹
  
  -- coecoe (ap ∣_∣ (semWk-T {A = {!A [ δ ]T!} } γ v)) (ap ∣_∣ (semSb-T A δ γ))

-- fin aplatissement
    ◾
    -- on enlève le wk-tm+
    
    ap (λ x →
      subst ∣_∣ (semSb-T A δ γ)
      (subst ∣_∣ (semWk-T {A = A [ δ ]T} γ v) x)
    )
     (sem-cohOp {a = (a +tm B)}([+S]T {A = A} {B = B} {δ = δ}) (γ ,Σ v))
    
    -- (sem-cohOp {a = (a +tm B)}([+S]T {A = A} {B = B} {δ = δ}) (γ ,Σ v))
    ◾
    -- on utilise wk-tm
    ap (λ x → subst ∣_∣ (semSb-T A δ γ) x) (semWk-tm {B = B} γ v a))

-- needed
semWk-tm {Γ} {A} {B} γ v (var x) = coeap2 ( semWk-T {A = A} {B = B}  γ v)
semWk-tm {Γ} {.(A [ δ ]T)} {B} γ v (coh x δ A) = {!!}

π-β1 {Γ} {A}  γ v = coeap2 (semWk-T {A = A} {B = A} γ v)

π-β2 {Γ} {A} {B} x γ v = coeap2 (semWk-T {A = A} {B = B} γ v)

⟦coh⟧ {.(ε , *)} c* * (a ,Σ b) = b
⟦coh⟧ {.(ε , *)} c* (a =h b) (u ,Σ v) = {!!}
-- ⟦coh⟧ {.(Γ , A , (var (vS x) =h var v0))} (ext {Γ} isC {A} x) B ((γ ,, α) ,, β) =
--   {!!}

-- on peut eliminer ce cas
⟦coh⟧ {.(Γ , A , (var (vS x) =h var v0))} (ext {Γ} isC {A} x) * ((γ ,Σ α) ,Σ β) = {!!}
⟦coh⟧ {.(Γ , A , (var (vS x) =h var v0))} (ext {Γ} isC {A} x) (_=h_ {C} a b) ((γ ,Σ α) ,Σ β) =
  {!⟦coh⟧ isC A γ!}
-- {!⟦coh⟧ isC A γ!}
  -- ⟦coh⟧ isC A γ!
