{-# OPTIONS --without-K --no-termination-check #-}


module Semantics (T : Set) where

open import BasicSyntax
-- open import IdentityContextMorphisms
-- open import Data.Unit
-- open import Data.Product renaming (_,_ to _,,_)
-- open import Coinduction
-- open import GroupoidStructure
open import lib

postulate
   uip : {l : _} {A : Set l} {a : A} {b : A} (e : a ≡ b) (e' : a ≡ b) → e ≡ e'

∣_∣ : {l : _} {A : Set l} → A → A
∣_∣ = idfun

coerce : {A B : Set} → B ≡ A → A → B
coerce refl a = a

-- subst : ∀{ℓ ℓ'}{A : Set ℓ}(P : A → Set ℓ'){x y : A}(p : x ≡ y) → P x → P y
-- subst = transport

-- coe : {A B : Set} → B ≡ A → B → A
-- coe p a = subst (λ x → x) p a

⊤-uni : ∀ {A : Set}{a b : A} → A ≡ ⊤ → a ≡ b
⊤-uni refl = refl


-- postulate
--    T : Set

⟦_⟧C   : Con → Set
⟦_⟧T   : ∀{Γ} → Ty Γ → ⟦ Γ ⟧C → Set


-- ⟦_⟧T   : ∀{Γ} → Ty Γ → ⟦ Γ ⟧C → Glob
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
          (θ : Δ ⇒ Θ) → ⟦ θ ⊚ δ ⟧S γ ≡ ⟦ θ ⟧S (⟦ δ ⟧S γ)
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

-- autre manière de le voir
sem-cohOp : {Γ : Con}{A B : Ty Γ}{a : Tm B}(p : A ≡ B) (γ : ⟦  Γ ⟧C)
   → coe (ap (λ x → ⟦ x ⟧T γ) p)  (⟦ a ⟦ p ⟫ ⟧tm γ) ≡ ⟦ a ⟧tm γ  

sem-cohOp refl γ = refl

sem-tm-γ :  {Γ : Con}{A : Ty Γ}(a : Tm A){γ : ⟦ Γ ⟧C}{δ : ⟦ Γ ⟧C}(p : γ ≡ δ) →
  ⟦ a ⟧tm δ ≡ subst ⟦ A ⟧T p (⟦ a ⟧tm γ)

sem-tm-γ a refl = refl

sem-⟦coh⟧-γ : {Γ : Con}(isC : isContr Γ)(A : Ty Γ){γ : ⟦ Γ ⟧C}{δ : ⟦ Γ ⟧C}(p : γ ≡ δ) →
  ⟦coh⟧ isC A δ ≡ subst ⟦ A ⟧T p ( ⟦coh⟧ isC A γ )

sem-⟦coh⟧-γ isC A refl = refl

-- needed
semSb-tm {Γ} {Δ} {A} (var x) δ γ = semSb-V x δ γ
semSb-tm {Γ} {Δ} {.(A [ δ ]T)} (coh x δ A) δ₁ γ = 
  subst ∣_∣ (semSb-T (A [ δ ]T) δ₁ γ)
    (⟦ coh x (δ ⊚ δ₁) A ⟦ sym [⊚]T ⟫ ⟧tm γ)
  -- on commence par enlever le ⟦ _ ⟫
  ≡⟨ ap (λ x → subst ∣_∣ (semSb-T (A [ δ ]T) δ₁ γ) x)
          (coe2l (( [⊚]T {A = A} {θ = δ} {δ = δ₁}))
          (sem-cohOp { a = coh x (δ ⊚ δ₁) A } (sym( [⊚]T {A = A} {θ = δ} {δ = δ₁})) γ ⁻¹)) ⁻¹ ⟩
  -- _
  subst ∣_∣ (semSb-T (A [ δ ]T) δ₁ γ)
  (coe (ap (λ v → ⟦ v ⟧T γ) ( [⊚]T {A = A} {θ = δ} {δ = δ₁}))
    (subst ∣_∣ (sym (semSb-T A (δ ⊚ δ₁) γ))
    (⟦coh⟧ x A (⟦ δ ⊚ δ₁ ⟧S γ))))

{-
    On doit vérifier le même diagramme que pour semSb-S
    on le fait par uip
-}
-- aplatissement
  ≡⟨ 
  coecoe
     (ap (λ v → ⟦ v ⟧T γ) ( [⊚]T {A = A} {θ = δ} {δ = δ₁}))
     (ap ∣_∣ (semSb-T (A [ δ ]T) δ₁ γ))
  ◾
  
  coecoe (ap ∣_∣ (sym (semSb-T A (δ ⊚ δ₁) γ)))
    (ap (λ v → ⟦ v ⟧T γ) ( [⊚]T {A = A} {θ = δ} {δ = δ₁}) ◾ ap ∣_∣ (semSb-T (A [ δ ]T) δ₁ γ))
  
  ◾
  -- uip
  
  ap (λ e → coe e (⟦coh⟧ x A (⟦ δ ⊚ δ₁ ⟧S γ)))

  (uip
    (ap ∣_∣ (sym (semSb-T A (δ ⊚ δ₁) γ)) ◾
      (ap (λ v → ⟦ v ⟧T γ) ( [⊚]T {A = A} {θ = δ} {δ = δ₁}) ◾ ap ∣_∣ (semSb-T (A [ δ ]T) δ₁ γ)))
    (ap ⟦ A ⟧T (semSb-S γ δ₁ δ) ◾
      ap ∣_∣ (sym (semSb-T A δ (⟦ δ₁ ⟧S γ))))
  )
  
   
  ◾
  
  coecoe (ap ⟦ A ⟧T (semSb-S γ δ₁ δ))
    (ap ∣_∣ (sym (semSb-T A δ (⟦ δ₁ ⟧S γ))))
    ⁻¹
  
  
    ⟩
    -- maintenant j'utilise semSb-S : ⟦ θ ⊚ δ ⟧S γ ≡ ⟦ θ ⟧S (⟦ δ ⟧S γ) 
    ap (λ z →       subst ∣_∣ (sym (semSb-T A δ (⟦ δ₁ ⟧S γ))) z)
    (sem-⟦coh⟧-γ x A (semSb-S γ δ₁ δ) ⁻¹)
    
  -- (semSb-S γ δ₁ δ)



-- coe2l (( [⊚]T {A = A} {θ = δ} {δ = δ₁})) (sem-cohOp { a = coh x (δ ⊚ δ₁) A } (sym( [⊚]T {A = A} {θ = δ} {δ = δ₁})) γ ⁻¹)!}






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

                        [⊚]T
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

semWk-tm {Γ} {.(A [ δ ]T)} {B} γ v (coh x δ A) = 
  -- on élimine le ⟦ ⟫
  
   ap (λ z → subst ∣_∣ (semWk-T {A = A [ δ ]T}  {B = B} γ v) z)
   (
    (
    coe2l ( [+S]T {A = A} {δ = δ})
    (sem-cohOp {a = coh x (δ +S B) A }  (sym ( [+S]T {A = A} {δ = δ})) (γ ,Σ v) ⁻¹)
    ⁻¹
    )
    )

  ◾
  {- 



  même diagramme que pour semWk-S. On le montre par uip



  -}

  -- aplatissement
  coecoe 
    (ap (λ x₁ → ⟦ x₁ ⟧T (γ ,Σ v)) ( [+S]T {A = A} {δ = δ}))
    (ap ∣_∣ (semWk-T {A = A [ δ ]T} {B = B} γ v))

  ◾
  coecoe
  (ap ∣_∣ (sym (semSb-T A (δ +S B) (γ ,Σ v))))
  (ap (λ x₁ → ⟦ x₁ ⟧T (γ ,Σ v)) ( [+S]T {A = A} {δ = δ}) ◾
    ap ∣_∣ (semWk-T {A = A [ δ ]T} {B = B} γ v))

  ◾
  -- uip
  
  ap (λ e → coe e (⟦coh⟧ x A (⟦ δ +S B ⟧S (γ ,Σ v))))
  (uip
    (ap ∣_∣ (sym (semSb-T A (δ +S B) (γ ,Σ v))) ◾
      (ap (λ x₁ → ⟦ x₁ ⟧T (γ ,Σ v)) ( [+S]T {A = A} {δ = δ}) ◾
       ap ∣_∣ (semWk-T {A = A [ δ ]T} {B = B} γ v)))
    (ap ⟦ A ⟧T (semWk-S {B = B} {γ = γ} {v = v} δ ) ◾ ap ∣_∣ (sym (semSb-T A δ γ)))
  )


    
  ◾
  
  coecoe
  (ap ⟦ A ⟧T (semWk-S {B = B} {γ = γ} {v = v} δ ))
  (ap ∣_∣ (sym (semSb-T A δ γ)))
  ⁻¹
  
  ◾
  -- on expoite semwk-S : ⟦ δ +S B ⟧S (γ ,Σ v) ≡ ⟦ δ ⟧S γ
  
  ap (λ z → subst ∣_∣ (sym (semSb-T A δ γ)) z)
  (
  sem-⟦coh⟧-γ x A 
    (semWk-S {B = B} {γ = γ} {v = v} δ )
    ⁻¹
    )
  
-- {!semWk-S {B = B} {γ = γ} {v = v} δ !}

-- sem-cohOp

π-β1 {Γ} {A}  γ v = coeap2 (semWk-T {A = A} {B = A} γ v)

π-β2 {Γ} {A} {B} x γ v = coeap2 (semWk-T {A = A} {B = B} γ v)

-- ⟦coh⟧ {.(ε , *)} c* * (a ,Σ b) = b
-- ⟦coh⟧ {.(ε , *)} c* (a =h b) (u ,Σ v) = {!!}
-- -- ⟦coh⟧ {.(Γ , A , (var (vS x) =h var v0))} (ext {Γ} isC {A} x) B ((γ ,, α) ,, β) =
-- --   {!!}

-- -- on peut eliminer ce cas
-- ⟦coh⟧ {.(Γ , A , (var (vS x) =h var v0))} (ext {Γ} isC {A} x) * ((γ ,Σ α) ,Σ β) = {!!}
-- ⟦coh⟧ {.(Γ , A , (var (vS x) =h var v0))} (ext {Γ} isC {A} x) (_=h_ {C} a b) ((γ ,Σ α) ,Σ β) =
--   {!⟦coh⟧ isC A γ!}
-- {!⟦coh⟧ isC A γ!}
  -- ⟦coh⟧ isC A γ!

{-


POUR INTERPRETER LES COHERENCES


-}

-- def A.4.3
idA : {Δ : Con} → isContr Δ → T → ⟦ Δ ⟧C

-- def A.4.3
JA : {Δ : Con} → (isC : isContr Δ) (P : ⟦ Δ ⟧C → Set) (d : (a : T) → P(idA isC a))
  (δ : ⟦ Δ ⟧C) → P δ

-- A.4.4
iA : {Δ : Con} (isC : isContr Δ) (a : T) (A : Ty Δ)  → ⟦ A ⟧T (idA isC a)

-- A.4.6
eq-tm-iA : {Δ : Con }(isC : isContr Δ)(a : T) {B : Ty Δ}
  (t : Tm B ) 
  → ⟦ t ⟧tm (idA isC a) ≡ iA isC a B

eq-var-iA : {Δ : Con }(isC : isContr Δ)(a : T) {B : Ty Δ}
  (x : Var B ) 
 → π x (idA isC a) ≡ iA isC a B

-- A.4.5
subst-idA : {Δ : Con} {Γ : Con} (isCΔ : isContr Δ)(isCΓ : isContr Γ)
  (σ : Δ ⇒ Γ) (a : T) → ⟦ σ ⟧S (idA  isCΔ a) ≡ (idA  isCΓ a)

-- preuve manquante dans Brunerie : dim T [ σ ]  = dim T
semSb-iA :  {Δ : Con} {Γ : Con} (isCΔ : isContr Δ)(isCΓ : isContr Γ)
  (σ : Δ ⇒ Γ)
  (a : T) (A : Ty Γ) →
   coe (ap (λ v₁ → ∣ ⟦ A ⟧T v₁ ∣) (subst-idA isCΔ isCΓ σ a))
    (subst ∣_∣ (semSb-T A σ (idA isCΔ a)) (iA isCΔ a (A [ σ ]T)))
      ≡ iA isCΓ a A

-- règle de cohérence nécessaire  à définir en même temps que semSb-iA pour
-- définir ce dernier
-- mais là on va supposer UIP (est-ce raisonnable d'ailleurs ?)
{-

                        eq-tm-iA
   ⟦ a [ σ ] ⟧ idΔ -------------------->      iΔ
          |                                   |
          |                                   |
 semSb-tm |                                   |
          |                                   |
          V                                   |
semSb-T # ⟦ a ⟧ o ⟦ σ ⟧ idΔ                 semSb-iA
          |                                   |
          |                                   |
subst-idA |                                   |
          |                                   |
          V                                   V
semSb-T # subst-idA # ⟦ a ⟧ idΓ ----------> semSb-T # subst-idA # iΓ
                                 eq-tm-iA
-}
eq-tm-iA-semSb-iA :  {Δ : Con} {Γ : Con} (isCΔ : isContr Δ)(isCΓ : isContr Γ)
  (σ : Δ ⇒ Γ) {A : Ty Γ} (a : Tm A) (x : T) →
  eq-tm-iA isCΔ x (a [ σ ]tm) ≡
    (
    coe2r (semSb-T A σ (idA isCΔ x)) (semSb-tm a σ (idA isCΔ x))
    ◾
    ap (coe (ap (λ v → ∣ v ∣) (semSb-T A σ (idA isCΔ x) ⁻¹)))
    (coe2r 
      (subst-idA isCΔ isCΓ σ x)
       (apd ⟦ a ⟧tm (subst-idA isCΔ isCΓ σ x))
       ◾
       ap (coe (ap (λ v → ∣ ⟦ A ⟧T v ∣) (subst-idA isCΔ isCΓ σ x ⁻¹)))
         (eq-tm-iA isCΓ x a)
       )
    ◾
    coe2r ((semSb-T A σ (idA isCΔ x)))
    (
       coe2r (subst-idA isCΔ isCΓ σ x ) (semSb-iA isCΔ isCΓ σ x A)
       ) ⁻¹)

eq-tm-iA-semSb-iA isCΔ isCΓ σ a x = uip _ _


ap-cst : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'}(b : B){a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
  → ap (λ x → b) a₂ ≡ refl

ap-cst b refl = refl

-- lemme A.4.3
JA-idA : {Δ : Con} → (isC : isContr Δ) (P : ⟦ Δ ⟧C → Set) (d : (a : T) → P(idA isC a))
  (a : T) → JA isC P d (idA isC a) ≡ d a


-- idA {Δ }isC a = ?
idA {.(ε , *)} c* a = tt ,Σ a
idA {.(_ , _ , (var (vS t) =h var v0))} (ext isC t) a = ((idA isC a) ,Σ
  (⟦ var t ⟧tm (idA isC a))) ,Σ refl

wk-iA : 
  {Γ     : Con}
  (isC   : isContr Γ)
  (a     : T)
  (A     : Ty Γ)
  {B    : Ty Γ}
  (t     : Var B)
  →
   (subst ∣_∣ (sym (semWk-T {A = A +T B} {B = (var (vS t)) =h (var v0) } (idA isC a ,Σ π t (idA isC a)) refl))
   (subst ∣_∣ (sym (semWk-T {A = A} {B = B} (idA isC a) (π t (idA isC a))))
   (iA isC a A))
   )
   ≡
   iA (ext isC t) a (A +T B +T (var (vS t) =h var v0))
   
   -- idfun (subst ∣_∣ (sym (semWk-T {A = A +T B} {B = (var (vS t)) =h (var v0) } (idA isC a ,Σ π t (idA isC a)) refl))
   -- (subst ∣_∣ (sym (semWk-T {A = A} {B = B} (idA isC a) (π t (idA isC a))))
   -- (iA isC a A))
   -- )
   -- has type ⟦ A +T B +T (var (vS t) =h var v0) ⟧T (idA (ext isC t) a)



-- version avec terme
-- idA {.(ε , *)} c* a = tt ,Σ a
-- idA {.(_ , A , (t +tm A =h var v0))} (ext isC {A} t) a =
--   ((idA isC a) ,Σ (⟦ t ⟧tm (idA isC a))) ,Σ
--    coe2r
--   ((semWk-T {A = A}{B = A} (idA isC a) (⟦ t ⟧tm (idA isC a))))
--    (semWk-tm {A = A}{ B = A}(idA isC a) (⟦ t ⟧tm (idA isC a)) t)
  
 --  coe2r
 -- ((semWk-T {A = A}{B = A} (idA isC a) (⟦ t ⟧tm (idA isC a))))
 --  (semWk-tm {A = A}{ B = A}(idA isC a) (⟦ t ⟧tm (idA isC a)) t)

coe-cancel : ∀{ℓ}{A B : Set ℓ} → (p : A ≡ B) → {a : A}{b : A} →
  (coe p a ≡ coe p b) → a ≡ b

coe-cancel refl q = q

ap-coe-cancel : ∀{ℓ}{A B : Set ℓ} → (p : A ≡ B) → {a : A}{b : A} →
   (q : coe p a ≡ coe p b) → ap (λ x → coe p x) (coe-cancel p q) ≡ q

ap-coe-cancel refl refl = refl

coe-cancel-ap-id : ∀{ℓ}{A B : Set ℓ} → (p : A ≡ B) → {a : A} 
   → coe-cancel  ( ap (λ x → x) p)
  {a = a}
   refl  ≡ refl

coe-cancel-ap-id refl  = refl

coh-degueu1 : ∀{ℓ}{A B : Set ℓ} → (p : B ≡ A) → {a : B}
  → (P : (subst ∣_∣ (p ) a ≡ subst ∣_∣ (p ) a)  → Set)
  →
  ap P (ap-coe-cancel (ap ∣_∣ ( p )) {a = a} {b = a} refl) ≡
   ap (λ z → P (ap (coe (ap ∣_∣ (p ))) z))
     (coe-cancel-ap-id (p ))
   

coh-degueu1 refl P = refl


-- JA {Δ} isC P d δ = {!!}
JA {.(ε , *)} c* P d (tt ,Σ a) = d a
JA {.(_ , A , (var (vS t) =h var v0))} (ext isC {A} t) P d (γ ,Σ z ,Σ u) =
   subst (λ v → P (γ ,Σ z ,Σ v))
     (ap-coe-cancel (ap ∣_∣ (sym (semWk-T {A = A} {B = A} γ z))) u)
     (
     J {A = ⟦ A ⟧T γ}
     ( λ { {y} e → P ((γ ,Σ y) ,Σ (ap (subst ∣_∣ (sym (semWk-T {A = A}{B = A} γ y) )) e))})
     -- Pr
     (JA isC (λ δ' → P ((δ' ,Σ (⟦ var t ⟧tm δ')) ,Σ refl)) d γ)
     (coe-cancel ( ap ∣_∣ (sym (semWk-T {A = A} {B = A} γ z))) u)
    )
-- J {A = ⟦ A ⟧T γ} Pr
-- (JA isC (λ δ' → P ((δ' ,Σ (⟦ var t ⟧tm δ')) ,Σ refl)) d γ)
-- (coe-cancel ( ap ∣_∣ (sym (semWk-T {A = A} {B = A} γ z))) u)
  -- J {A = ⟦ A ⟧T γ} Pr
  -- (JA isC (λ δ' → P ((δ' ,Σ (⟦ var t ⟧tm δ')) ,Σ refl)) d γ)
  -- (coe-cancel {p = ap ∣_∣ (sym (semWk-T {A = A} {B = A} γ z))} u)
  -- {!(coe-cancel {p = ap ∣_∣ (sym (semWk-T {A = A} {B = A} γ z))} u) !}
  -- (coe-cancel u)
  
  where
  -- Pr' : {y : ⟦ A ⟧T γ}
  -- Pr' : {y : _}
  --   (e :
  --   subst ∣_∣ (sym (semWk-T {A = A} {B = A} γ y)) (⟦ var t ⟧tm γ) ≡ 
  --    y
  
  --   subst ∣_∣ (sym (semWk-T {A = A} {B = A} γ y)) y
    -- ) → Set
  Pr : {y : ⟦ A ⟧T γ} (e : ⟦ var t ⟧tm γ ≡ y) → Set
  Pr {y} e = P ((γ ,Σ y) ,Σ (ap (subst ∣_∣ (sym (semWk-T {A = A}{B = A} γ y) )) e))
  -- Pr' {y} e = P ((γ ,Σ ?) ,Σ ?)



-- version avec termes
-- JA {.(ε , *)} c* P d (tt ,Σ a) = d a
-- JA {.(_ , A , (t +tm A =h var v0))} (ext isC {A} t) P d δ = {!!}

⟦coh⟧ isC A δ = JA isC ⟦ A ⟧T (λ a → iA isC a A ) δ 

-- A.4.4 par induction sur le type
-- iA isC a A = {!!}
iA isC a * = a
iA isC a (x =h y) =
  eq-tm-iA isC a x ◾ eq-tm-iA isC a y ⁻¹

  
-- correspond à subst-iA
-- par récurrence sur le type
-- semSb-iA isCΔ isCΓ σ a A = {!!}
semSb-iA isCΔ isCΓ σ a * = subst (λ e → a ≡[ e ]≡ a)((ap-cst T (subst-idA isCΔ isCΓ σ a)) ⁻¹) refl
-- subst (λ e → a ≡[ e ]≡ a)((ap-cst T (subst-idA isCΔ isCΓ σ a)) ⁻¹) refl
semSb-iA isCΔ isCΓ σ a (_=h_ {A = A} x y) = 
-- on utilise eq-tm-iA-semSb-iA
  ap2 (λ u v → coe
  (ap (λ v₁ → ∣ ⟦ x ⟧tm v₁ ≡ ⟦ y ⟧tm v₁ ∣)
  (subst-idA isCΔ isCΓ σ a))
  (subst ∣_∣
  (EqEq (semSb-T A σ (idA isCΔ a)) (semSb-tm x σ (idA isCΔ a))
  (semSb-tm y σ (idA isCΔ a)))
  (u ◾ (v ⁻¹)) ))
  (eq-tm-iA-semSb-iA isCΔ isCΓ σ x a)
  (eq-tm-iA-semSb-iA isCΔ isCΓ σ y a)
  
  ◾
  -- on a affaire à une cohérence dégueu
  coh-degueu2 ⟦ x [ σ ]tm ⟧tm ⟦ y [ σ ]tm ⟧tm
  ⟦ x ⟧tm ⟦ y  ⟧tm
  ⟦ σ ⟧S
  (eq-tm-iA isCΓ a x)
  (eq-tm-iA isCΓ a y)
  (subst-idA isCΔ isCΓ σ a)
  (semSb-T A σ (idA isCΔ a))
  (semSb-tm x σ (idA isCΔ a))
  (semSb-tm y σ (idA isCΔ a))
  (semSb-iA isCΔ isCΓ σ a A)
    


refl' : {l  : _}{A : Set l} (a : A) → a ≡ a
refl' a = refl

refl'-eq : {l  : _}{A : Set l} (a : A) → refl' a ≡ refl
refl'-eq a = refl

-- subst-idA isCΔ isCΓ σ a = {!!}
-- par récurrence sur σ et sur isCΓ
subst-idA isCΔ () • a
subst-idA isCΔ c* (σ , t) a =
  ,Σ= refl (eq-tm-iA isCΔ a t)
subst-idA isCΔ (ext isCΓ {A} t) (σ , u , v) a =
  ,Σ= (,Σ= (subst-idA isCΔ isCΓ σ a)
   (
   -- coe (ap (λ γ → ⟦ .A ⟧T γ) (subst-idA isCΔ isCΓ σ a))
   -- (coe (ap (λ x → x) (semSb-T .A σ (idA isCΔ a)))
   -- (⟦ u ⟧tm (idA isCΔ a)))
   -- ≡ π t (idA isCΓ a)
   ap
   ( λ z → coe (ap (λ v₁ → ∣ ⟦ A ⟧T v₁ ∣) (subst-idA isCΔ isCΓ σ a))
      (subst ∣_∣ (semSb-T A σ (idA isCΔ a)) z)
      )
   (eq-tm-iA isCΔ a u)
   ◾
   semSb-iA isCΔ isCΓ σ a A
   ◾
   eq-var-iA isCΓ a t ⁻¹
   ) )
   -- uip ??
   -- cf test pour le but
   (
   -- dans cette preuve, il y a des endroits où j'ai le droit d'utiliser uip
   -- et d'autres non
   {-

dans HTS, on restreint l'élimination de J de l'égalité homotopique à
P : (a : A) (e : x = y) → Uf
Uf est l'univers des types fibrants (qui ne parlent pas de l'égalité stricte)

   -}
   {!(,Σ= (subst-idA isCΔ isCΓ σ a)
   (ap
   (λ z →
   coe (ap (λ v₁ → ⟦ A ⟧T v₁) (subst-idA isCΔ isCΓ σ a))
   (coe (ap (λ x → x) (semSb-T A σ (idA isCΔ a))) z))
   (eq-tm-iA isCΔ a u)
   ◾ semSb-iA isCΔ isCΓ σ a A
   ◾ eq-var-iA isCΓ a t ⁻¹))!}
  ◾
  (refl'-eq _)
   )
  -- ,Σ= (,Σ= {!subst-idA isCΔ isCΓ σ!} {!!}) {!!}

-- JA-idA  isCΔ P d a = {!!}
-- A.4.3
JA-idA c* P d a = refl
JA-idA (ext isCΔ {A} t) P d a =
  {!
  ap
  (λ z →
  coe z
  (J
  (λ {y} e →
  P
  (idA isCΔ a ,Σ y ,Σ
  ap (coe (ap (λ x → x) (semWk-T {A = A} {B = A} (idA isCΔ a) y ⁻¹)))
  e))
  (JA isCΔ (λ δ' → P (δ' ,Σ π t δ' ,Σ refl)) d (idA isCΔ a))
  (coe-cancel
  (ap (λ x → x)
  (semWk-T {A = A} {B = A} (idA isCΔ a) (π t (idA isCΔ a)) ⁻¹))
  {a = π t (idA isCΔ a)} {b = π t (idA isCΔ a)} refl)))
  !}
 {- 
  ap
  (λ z →
      coe z
      (J
      (λ {y} e →
      P
      (idA isCΔ a ,Σ y ,Σ
      ap (coe (ap (λ x → x) (semWk-T {A = A} {B = A} (idA isCΔ a) y ⁻¹)))
      e))
      (JA isCΔ (λ δ' → P (δ' ,Σ π t δ' ,Σ refl)) d (idA isCΔ a))
      (coe-cancel
      (ap (λ x → x)
      (semWk-T {A = A} {B = A} (idA isCΔ a) (π t (idA isCΔ a)) ⁻¹))
      {a = π t (idA isCΔ a)} {b = π t (idA isCΔ a)} refl)))
  (    coh-degueu1  (semWk-T {A = A} {B = A} (idA isCΔ a) (π t (idA isCΔ a)) ⁻¹)
      (λ v → P (idA isCΔ a ,Σ π t (idA isCΔ a) ,Σ v))
  )

-}
  


   ◾
  apd (J
  (λ {y} e →
  P
  (idA isCΔ a ,Σ y ,Σ
  ap (coe (ap (λ x → x) (semWk-T {A = A} (idA isCΔ a) y ⁻¹))) e))
  (JA isCΔ (λ δ' → P (δ' ,Σ π t δ' ,Σ refl)) d (idA isCΔ a))
  )
  (coe-cancel-ap-id (semWk-T {A = A}{B = A} (idA isCΔ a) (π t (idA isCΔ a)) ⁻¹)
  )
  
  ◾
  (JA-idA isCΔ (λ δ' → P (δ' ,Σ ⟦ var t ⟧tm δ' ,Σ refl)) d a )
  
  -- : subst ∣_∣ (sym (semWk-T (idA isCΔ a) (π t (idA isCΔ a))))
  -- (π t (idA isCΔ a))
  -- ≡
  -- subst ∣_∣ (sym (semWk-T (idA isCΔ a) (π t (idA isCΔ a))))
  -- (π t (idA isCΔ a))) →



-- eq-tm-iA isC a {B} t = {!!}
-- par récurrence sur le terme
eq-tm-iA isC a {B} (var x) = eq-var-iA isC a x
eq-tm-iA isC a {.(A [ δ ]T)} (coh isCΓ δ A) =
  
  ap (λ z → coe (ap (λ x → x) (semSb-T A δ (idA isC a) ⁻¹)) z)
  (
  J {x = idA  isCΓ a}
  (λ {y} e → JA isCΓ ⟦ A ⟧T (λ a₁ → iA isCΓ a₁ A) y ≡
     coe (ap ⟦ A ⟧T e) (iA isCΓ a A))
     (JA-idA isCΓ ⟦ A ⟧T (λ a₁ → iA isCΓ a₁ A) a)
     ((subst-idA isC isCΓ δ a)⁻¹)
     )
     ◾
    -- en utilisant semSb-iA 
     coe2r
     (semSb-T A δ (idA isC a))
     (
     coe2r
       (subst-idA isC isCΓ δ a)
       (semSb-iA isC isCΓ δ a A)) ⁻¹
  

  -- J {x = idA  isCΓ a}
  -- (λ {y} e → JA isCΓ ⟦ A ⟧T (λ a₁ → iA isCΓ a₁ A) y ≡
  -- coe (ap ⟦ A ⟧T e) (iA isCΓ a A))
  -- (JA-idA isCΓ ⟦ A ⟧T (λ a₁ → iA isCΓ a₁ A) a)
  -- ((subst-idA isC isCΓ δ a)⁻¹)


  -- Goal: coe (ap (λ x → x) (semSb-T A δ (idA isC a) ⁻¹))
  -- (JA isCΓ ⟦ A ⟧T (λ a₁ → iA isCΓ a₁ A) (⟦ δ ⟧S (idA isC a)))
  -- ≡ iA isC a (A [ δ ]T)
  -- Have: JA isCΓ ⟦ A ⟧T (λ a₁ → iA isCΓ a₁ A) (⟦ δ ⟧S (idA isC a)) ≡
  -- coe (ap ⟦ A ⟧T (?4 T isC isCΓ δ a ⁻¹)) (iA isCΓ a A)

-- par récurrence sur la variable
-- eq-var-iA isC a {B} x = {!!}
eq-var-iA c* a {.*} v0 = refl
eq-var-iA (ext isC t) a {.(var (vS (vS t)) =h var (vS v0))} v0 = {!!}
eq-var-iA c* a {.(_ +T *)} (vS ())
eq-var-iA (ext isC t) a {.(_ +T _ +T (var (vS t) =h var v0))} (vS v0) = {!!}

eq-var-iA (ext isC {A} t) a {.(B +T A +T (var (vS t) =h var v0))} (vS (vS {A = B} x)) =
 ap
   (λ z →
      subst ∣_∣
      (sym (semWk-T {A = B +T A} {B = (var (vS t)) =h (var v0) } (idA isC a ,Σ π t (idA isC a)) refl))
      (subst ∣_∣
       (sym (semWk-T {A = B} {B = A} (idA isC a) (π t (idA isC a)))) z))
   (eq-var-iA isC a  x)
 
  -- ap
  --   (λ z →
  --      subst ∣_∣
  --      (sym (semWk-T {A = B +T A} {B = (var (vS t)) =h (var v0) } (idA isC a ,Σ π t (idA isC a)) refl))
  --      (subst ∣_∣
  --       (sym (semWk-T {A = B} {B = A} (idA isC a) (π t (idA isC a)))) z))
  --   {!!}
  ◾
  wk-iA isC a B t
  
  


-- par récurrence sur le type A
-- wk-iA isCΓ a A {B} t = {!!}
wk-iA isCΓ a * {B} t = refl
-- uip ??
wk-iA isCΓ a (_=h_ {A} x y) {B} t =
  uip _ _
  
 
