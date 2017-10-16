{-# OPTIONS --without-K --no-termination-check  #-}

-- question : est-ce que le schéma d'élimination de l'égalité homotopique
-- ne s'applique qe pour les types fibrants ??

-- j'ai besoin de savoir que pour type A de la syntaxe, ⟦ A ⟧T γ est fibrant
-- ⟦ Δ ⟧ est fibrant 
-- dans cette version, on a 2 égalités : une stricte (celle de lib.agda)
-- et celle de T

open import libhomot

module Semantics2Eq (T : Set) ⦃ FibT : Fib T ⦄ where

open import BasicSyntax
open import lib


postulate
   admit : {l : _} {A : Set l} → A

postulate
   uip : {l : _} {A : Set l} {a : A} {b : A} (e : a ≡ b) (e' : a ≡ b) → e ≡ e'



⟦_⟧C   : Con → Set
⟦_⟧T   : ∀{Γ} → Ty Γ → ⟦ Γ ⟧C → Set

Fib-C : (Γ : Con) → Fib (⟦ Γ ⟧C)
Fib-T : {Γ : Con} (A : Ty Γ) (γ : ⟦ Γ ⟧C) → Fib (⟦ A ⟧T γ)


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

semSb-T   : ∀ {Γ Δ}(A : Ty Δ)(δ : Γ ⇒ Δ)(γ : ⟦ Γ ⟧C)
          → ⟦ A [ δ ]T ⟧T γ ≡ ⟦ A ⟧T (⟦ δ ⟧S γ)

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
semWk-T'  : ∀ {Γ} A B (γ : ⟦ Γ ⟧C)(v : ∣ ⟦ B ⟧T γ ∣)
          → ⟦ A +T B ⟧T (coerce ⟦_⟧C-β2 (γ ,Σ v)) ≡ 
          ⟦ A ⟧T γ
semWk-T  : ∀ {Γ A B}(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ B ⟧T γ ∣)
          → ⟦ A +T B ⟧T (coerce ⟦_⟧C-β2 (γ ,Σ v)) ≡ 
          ⟦ A ⟧T γ

semWk-T {Γ} {A} {B} = semWk-T' A B


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

Fib-C ε = ⊤-Fib
Fib-C (Γ , A) =  Σ-Fib ⦃ fibA = Fib-C Γ ⦄ ⦃ fibB = Fib-T A  ⦄ 


⟦_⟧T {Γ} * γ = T
-- T
⟦_⟧T {Γ} (a =h b) γ = ⟦ a ⟧tm γ ≡T ⟦ b ⟧tm γ

Fib-T {Γ} * γ = FibT
Fib-T {Γ} (_=h_ {A = A} a b) γ = eq-Fib ⦃ fibA = (Fib-T A γ) ⦄ (⟦ a ⟧tm γ) (⟦ b ⟧tm γ)

⟦_⟧tm {Γ} {A} (var x) γ = π x γ
-- ici j'ai besoin de désactiver le termination checker
⟦_⟧tm {Γ} {.(A [ δ ]T)} (coh isC δ A) γ = subst ∣_∣ (sym (semSb-T A δ γ )) (⟦coh⟧ isC A (⟦ δ ⟧S γ))

⟦_⟧S {Γ} {.ε} • γ = tt
⟦_⟧S {Γ} {.(Δ , A)} (_,_ {Δ = Δ} σ {A} a) γ =
   ⟦ σ ⟧S γ ,Σ subst  ∣_∣ (semSb-T A σ γ) (⟦ a ⟧tm γ)

-- definitionel
⟦_⟧C-β1 = refl
-- definitionel
⟦_⟧C-β2 {Γ} {Δ} = refl
π {.(Γ , A)} {.(A +T A)} (v0 {Γ} {A}) (γ ,Σ v) = subst ∣_∣ (sym (semWk-T {A = A} γ v)) v 
π {.(Γ , B)} {.(A +T B)} (vS {Γ} {A} {B} x) (γ ,Σ v) = subst ∣_∣ (sym (semWk-T {A = A} γ v)) (π x γ)

-- needed
semSb-T {Γ} {Δ} * δ γ = refl
semSb-T {Γ} {Δ} (_=h_ {A} a b) δ γ = 
  Eq2G _≡T_ (semSb-T A δ γ) (semSb-tm a δ γ)(semSb-tm b δ γ)

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
       ))


⟦_⟧tm-β1 {Γ} {A} {x} {γ} = refl

-- définitionnel
⟦_⟧S-β1 {Γ} {γ} = refl

⟦_⟧S-β2 {Γ} {Δ} {A} {δ} {γ}
          {a} = refl


-- needed
semWk-T' {Γ} * B γ v = refl
semWk-T' {Γ} (_=h_ {A} a b) B γ v  =
  Eq2G _≡T_ (semWk-T' A B γ v) (semWk-tm γ v a) (semWk-tm γ v b)


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


{-


POUR INTERPRETER LES COHERENCES


-}

-- def A.4.3
idA : {Δ : Con} → isContr Δ → T → ⟦ Δ ⟧C

-- def A.4.3
-- JA : {Δ : Con} → (isC : isContr Δ) (P : ⟦ Δ ⟧C → Set) (d : (a : T) → P(idA isC a))
--   (δ : ⟦ Δ ⟧C) → P δ

-- def A.4.3
JA-fib : {Δ : Con} → (isC : isContr Δ) (P : ⟦ Δ ⟧C → Set)
  ⦃ fibP : (δ : ⟦ Δ ⟧C) → Fib (P δ) ⦄
  (d : (a : T) → P(idA isC a))
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



ap-cst : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'}(b : B){a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
  → ap (λ x → b) a₂ ≡ refl

ap-cst b refl = refl

-- lemme A.4.3

-- JA-idA : {Δ : Con} → (isC : isContr Δ) (P : ⟦ Δ ⟧C → Set) (d : (a : T) → P(idA isC a))
--   (a : T) → JA isC P d (idA isC a) ≡ d a

JA-idA-fib : {Δ : Con} → (isC : isContr Δ) (P : ⟦ Δ ⟧C → Set)
  ⦃ fibP : (δ : ⟦ Δ ⟧C) → Fib (P δ) ⦄
   (d : (a : T) → P(idA isC a)) (a : T) → JA-fib isC P ⦃ fibP = fibP ⦄ d (idA isC a) ≡ d a

-- idA {Δ }isC a = ?
idA {.(ε , *)} c* a = tt ,Σ a
idA {.(_ , _ , (var (vS t) =h var v0))} (ext isC t) a = ((idA isC a) ,Σ
  (⟦ var t ⟧tm (idA isC a))) ,Σ (reflT' _)

wk-iA : 
  {Γ     : Con}
  (isC   : isContr Γ)
  (a     : T)
  (A     : Ty Γ)
  {B    : Ty Γ}
  (t     : Var B)
  →
   (subst ∣_∣ (sym (semWk-T {A = A +T B} {B = (var (vS t)) =h (var v0) } (idA isC a ,Σ π t (idA isC a)) reflT))
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
{-
JA {.(ε , *)} c* P d (tt ,Σ a) = d a
JA {.(_ , A , (var (vS t) =h var v0))} (ext isC {A} t) P d (γ ,Σ z ,Σ u) =
  
  coe
  (ap (λ w → P (γ ,Σ z ,Σ w))
    (coe2 (Eq2G (_≡T_) (sym (semWk-T' A A γ z)) refl refl) u))
    -- ⟦ A ⟧T γ est fibrant (facile : par récurrence sur A)
    -- et il faut que P δ soit fibrant
  (JT {A = ⟦ A ⟧T γ}
  ( λ  {y} e → P ((γ ,Σ y) ,Σ (coe (Eq2G _≡T_ (sym (semWk-T' A A γ y)) refl refl) e)))
  (subst (λ w → P (γ ,Σ π t γ ,Σ w))
    (Refl2G _ reflT' (sym (semWk-T' A A γ _)) refl ⁻¹  )
     (JA isC (λ δ' → P ((δ' ,Σ (⟦ var t ⟧tm δ')) ,Σ reflT' _)) d γ) )
  (coe (Eq2G _≡T_ (sym (semWk-T' A A γ _)) refl refl ⁻¹) u)
  )
  
  
-}


JA-fib {.(ε , *)} c* P d (tt ,Σ a) = d a
JA-fib {.(_ , A , (var (vS t) =h var v0))} (ext isC {A} t) P {{fibP}} d (γ ,Σ z ,Σ u) =
  
  coe
  (ap (λ w → P (γ ,Σ z ,Σ w))
  (coe2 (Eq2G (_≡T_) (sym (semWk-T' A A γ z)) refl refl) u))
  (JFib {A = ⟦ A ⟧T γ} ⦃ fibA = Fib-T A γ ⦄
  ( λ  {y} e → P ((γ ,Σ y) ,Σ (coe (Eq2G _≡T_ (sym (semWk-T' A A γ y)) refl refl) e)))
  ⦃ fibP = λ y e →
       fibP ((γ ,Σ y) ,Σ (coe (Eq2G _≡T_ (sym (semWk-T' A A γ y)) refl refl) e))
  ⦄
  (subst (λ w → P (γ ,Σ π t γ ,Σ w))
  (Refl2G _ reflT' (sym (semWk-T' A A γ _)) refl ⁻¹  )
  (JA-fib isC (λ δ' → P ((δ' ,Σ (⟦ var t ⟧tm δ')) ,Σ reflT' _))
      ⦃ fibP = (λ δ' → fibP ((δ' ,Σ (⟦ var t ⟧tm δ')) ,Σ reflT' _)) ⦄
     d γ) )
  (coe (Eq2G _≡T_ (sym (semWk-T' A A γ _)) refl refl ⁻¹) u)
  )
  


-- version avec termes
-- JA {.(ε , *)} c* P d (tt ,Σ a) = d a
-- JA {.(_ , A , (t +tm A =h var v0))} (ext isC {A} t) P d δ = {!!}

-- ok
⟦coh⟧ isC A δ = JA-fib isC ⟦ A ⟧T ⦃ fibP = Fib-T A ⦄ (λ a → iA isC a A )  δ 

-- A.4.4 par induction sur le type
-- iA isC a A = {!!}
iA isC a * = a
-- je peux composer, on est dans un type fibrant
iA isC a (x =h y) = coe ( ap2 _≡T_ (eq-tm-iA isC a x ⁻¹) (eq-tm-iA isC a y ⁻¹)) (reflT' _)

  -- eq-tm-iA isC a x ◾ eq-tm-iA isC a y ⁻¹


reflT'-eq : {l  : _}{A : Set l} (a : A) → reflT' a ≡ reflT
reflT'-eq a = refl

-- P refl refl a = refl

  
-- correspond à subst-iA
-- par récurrence sur le type
-- semSb-iA isCΔ isCΓ σ a A = {!!}
semSb-iA isCΔ isCΓ σ a * = subst (λ e → a ≡[ e ]≡ a)((ap-cst T (subst-idA isCΔ isCΓ σ a)) ⁻¹) refl
-- subst (λ e → a ≡[ e ]≡ a)((ap-cst T (subst-idA isCΔ isCΓ σ a)) ⁻¹) refl
semSb-iA isCΔ isCΓ σ a (_=h_ {A = A} x y) =
-- on utilise eq-tm-iA-semSb-iA
  
  
  -- aplatissement
  cccoe

    (ap2 _≡T_ (eq-tm-iA isCΔ a (x [ σ ]tm) ⁻¹)
      (eq-tm-iA isCΔ a (y [ σ ]tm) ⁻¹))
    (ap ∣_∣ (Eq2G _≡T_ (semSb-T A σ (idA isCΔ a)) (semSb-tm x σ (idA isCΔ a))
      (semSb-tm y σ (idA isCΔ a))))
    (ap (λ v₁ → ∣ ⟦ x ⟧tm v₁ ≡T ⟦ y ⟧tm v₁ ∣)
      (subst-idA isCΔ isCΓ σ a))
  ◾ 
  ap
     {A = (iA isCΔ a (A [ σ ]T) ≡T iA isCΔ a (A [ σ ]T)) ≡
         (⟦ x ⟧tm (idA isCΓ a) ≡T ⟦ y ⟧tm (idA isCΓ a)) }
     (λ e → coe e (reflT {x = iA isCΔ a (A [ σ ]T)}))
     (uip
      (ap2 _≡T_ (eq-tm-iA isCΔ a (x [ σ ]tm) ⁻¹)
        (eq-tm-iA isCΔ a (y [ σ ]tm) ⁻¹)
        ◾
        ap ∣_∣
        (Eq2G (_≡T_) (semSb-T A σ (idA isCΔ a))
        (semSb-tm x σ (idA isCΔ a)) (semSb-tm y σ (idA isCΔ a)))
        ◾
        ap (λ v₁ → ∣ ⟦ x ⟧tm v₁ ≡T ⟦ y ⟧tm v₁ ∣) (subst-idA isCΔ isCΓ σ a))
      (Eq2G (_≡T_)
        (semSb-T A σ (idA isCΔ a) ◾ ap ⟦ A ⟧T (subst-idA isCΔ isCΓ σ a))
        (coh4 (semSb-T A σ (idA isCΔ a))
        (ap ⟦ A ⟧T (subst-idA isCΔ isCΓ σ a)) (iA isCΔ a (A [ σ ]T))
        ◾ semSb-iA isCΔ isCΓ σ a A)
        (coh4 (semSb-T A σ (idA isCΔ a))
        (ap ⟦ A ⟧T (subst-idA isCΔ isCΓ σ a)) (iA isCΔ a (A [ σ ]T))
        ◾ semSb-iA isCΔ isCΓ σ a A)
        ◾ ap2 _≡T_ (eq-tm-iA isCΓ a x ⁻¹) (eq-tm-iA isCΓ a y ⁻¹))
      )
  ◾ 
  -- aplatissement
  coecoe
    (Eq2G _≡T_
      (semSb-T A σ (idA isCΔ a) ◾ ap ⟦ A ⟧T (subst-idA isCΔ isCΓ σ a))
      (coh4 (semSb-T A σ (idA isCΔ a))
      (ap ⟦ A ⟧T (subst-idA isCΔ isCΓ σ a)) (iA isCΔ a (A [ σ ]T))
      ◾ semSb-iA isCΔ isCΓ σ a A)
      (coh4 (semSb-T A σ (idA isCΔ a))
      (ap ⟦ A ⟧T (subst-idA isCΔ isCΓ σ a)) (iA isCΔ a (A [ σ ]T))
      ◾ semSb-iA isCΔ isCΓ σ a A))
    (ap2 _≡T_ (eq-tm-iA isCΓ a x ⁻¹) (eq-tm-iA isCΓ a y ⁻¹))
    ⁻¹

  
  ◾ 
  ap (coe (ap2 _≡T_ (eq-tm-iA isCΓ a x ⁻¹) (eq-tm-iA isCΓ a y ⁻¹)))
  (coh-degueu5 {P = ⟦ A [ σ ]T ⟧T }{Q = ⟦ A ⟧T} ⟦ σ ⟧S (subst-idA isCΔ isCΓ σ a)
  (semSb-T A σ (idA isCΔ a))
  (semSb-iA isCΔ isCΓ σ a A)
  ⁻¹
  )
  
  
    

  



-- subst-idA isCΔ isCΓ σ a = {!!}
-- par récurrence sur σ et sur isCΓ
subst-idA isCΔ () • a
subst-idA isCΔ c* (σ , t) a =
  ,Σ= refl (eq-tm-iA isCΔ a t)
subst-idA isCΔ (ext isCΓ {A} t) (σ , u , v) a =
  ,Σ= (,Σ= (subst-idA isCΔ isCΓ σ a)
  ((
  ap
  ( λ z → coe (ap (λ v₁ → ∣ ⟦ A ⟧T v₁ ∣) (subst-idA isCΔ isCΓ σ a))
  (subst ∣_∣ (semSb-T A σ (idA isCΔ a)) z)
  )
  (eq-tm-iA isCΔ a u)
  ◾
  semSb-iA isCΔ isCΓ σ a A
  ◾
  eq-var-iA isCΓ a t ⁻¹
  )))

 {-
************************


Je mets la preuve suivante en commentaire car agda met 15s à typer le fihcier


************************

-}
-- ce admit a été vérifier post-fib
   admit

-- début du commentage hardcore
  {-
  -- ici est la difficulté
  -- ⟦ v ⟧ réécrit par eq-tm-iA donne
  --    (reflT' (iA isCΔ a ((A +T A) [ σ , u ]T)))
  -- réécrit par +T[,]T donne
  --    +T[,]T # (reflT' (iA isCΔ a (A  [ σ  ]T)))
  -- réécrit par semSb-iA
  --     subst-idA # semSb-T # +[,]T # (reflT' (iA isCΓ a A))

  -- ce qui est pas mal car de l'autre côté on a :
  --   reflT' (subst ∣_∣ (sym (semWk-T {A = A} {B = A} (idA isCΓ a) (π t (idA isCΓ a))))
  --       (π t (idA isCΓ a)))
  -- qui se réécrit (eq-var-ia)
  --   reflT' (subst ∣_∣ (sym (semWk-T {A = A} {B = A} (idA isCΓ a) (π t (idA isCΓ a))))
  --       (iA isCΓ a A))


  (
  ap
  -- don't care about this part : it is the context
    (λ z →
       coe
       (ap
        (λ γ →
           coe (ap (λ x → x) (semWk-T {A = A} {B = A} (proj₁ γ) (proj₂ γ) ⁻¹)) (π t (proj₁ γ))
           ≡T coe (ap (λ x → x) (semWk-T {A = A} {B = A} (proj₁ γ) (proj₂ γ) ⁻¹)) (proj₂ γ))
        (,Σ= (subst-idA isCΔ isCΓ σ a)
         (ap
          (λ z₁ →
             coe (ap (λ v₁ → ⟦ A ⟧T v₁) (subst-idA isCΔ isCΓ σ a))
             (coe (ap (λ x → x) (semSb-T A σ (idA isCΔ a))) z₁))
          (eq-tm-iA isCΔ a u)
          ◾ semSb-iA isCΔ isCΓ σ a A
          ◾ eq-var-iA isCΓ a t ⁻¹)))
       (coe
        (ap (λ x → x)
         (Eq2G _≡T_ (semSb-T (A +T A) (σ , u) (idA isCΔ a))
          (ap  (λ e → coe e (⟦ (t [ σ ]V) ⟦ +T[,]T  ⟫ ⟧tm
              (idA isCΔ a)))
           (uip (ap (λ x → x) (semSb-T (A +T A) (σ , u) (idA isCΔ a)))
            (ap (λ x₁ → ⟦ x₁ ⟧T (idA isCΔ a))
              (+T[,]T {Δ = _} {A = A} {δ = σ}) ◾
             (ap (λ x → x) (semSb-T A σ (idA isCΔ a)) ◾
              ap (λ x → x)
              (semWk-T {A = A} {B = A} (⟦ σ ⟧S (idA isCΔ a))
               (coe (ap (λ x → x) (semSb-T A σ (idA isCΔ a)))
                (⟦ u ⟧tm (idA isCΔ a)))
               ⁻¹))))
           ◾
           coecoe (ap (λ x₁ → ⟦ x₁ ⟧T (idA isCΔ a)) (+T[,]T {A = A} ))
           (ap (λ x → x) (semSb-T A σ (idA isCΔ a)) ◾
            ap (λ x → x)
            (semWk-T {A = A} {B = A} (⟦ σ ⟧S (idA isCΔ a))
             (coe (ap (λ x → x) (semSb-T A σ (idA isCΔ a)))
              (⟦ u ⟧tm (idA isCΔ a)))
             ⁻¹))
           ⁻¹
           ◾
           coecoe (ap (λ x → x) (semSb-T A σ (idA isCΔ a)))
           (ap (λ x → x)
           (semWk-T {A = A} {B = A} (⟦ σ ⟧S (idA isCΔ a))
             (coe (ap (λ x → x) (semSb-T A σ (idA isCΔ a)))
              (⟦ u ⟧tm (idA isCΔ a)))
             ⁻¹))
           ⁻¹
           ◾
           ap
           (λ e →
              coe
              (ap (λ x → x)
              (semWk-T  {A = A} {B = A} (⟦ σ ⟧S (idA isCΔ a))
                (coe (ap (λ x → x) (semSb-T A σ (idA isCΔ a)))
                 (⟦ u ⟧tm (idA isCΔ a)))
                ⁻¹))
              (coe (ap (λ x → x) (semSb-T A σ (idA isCΔ a))) e))
           (sem-cohOp
             (+T[,]T {A = A} {B = A} {δ = σ})
               (idA isCΔ a))
           ◾
           ap
           (coe
            (ap (λ x → x)
            (semWk-T {A = A} {B = A} (⟦ σ ⟧S (idA isCΔ a))
              (coe (ap (λ x → x) (semSb-T A σ (idA isCΔ a)))
               (⟦ u ⟧tm (idA isCΔ a)))
              ⁻¹)))
           (semSb-V t σ (idA isCΔ a)))
          (ap (λ x → coe x (⟦ u ⟦ +T[,]T {A = A} {B = A}{δ = σ} ⟫ ⟧tm (idA isCΔ a)))
           (uip (ap (λ x → x) (semSb-T (A +T A) (σ , u) (idA isCΔ a)))
            (ap (λ x → ⟦ x ⟧T (idA isCΔ a)) (+T[,]T {A = A}{B = A} {δ = σ}) ◾
             (ap (λ x → x) (semSb-T A σ (idA isCΔ a)) ◾
              ap (λ x → x)
              (semWk-T {A = A} {B = A} (⟦ σ ⟧S (idA isCΔ a))
               (coe (ap (λ x → x) (semSb-T A σ (idA isCΔ a)))
                (⟦ u ⟧tm (idA isCΔ a)))
               ⁻¹))))
           ◾
           coecoe (ap (λ x → ⟦ x ⟧T (idA isCΔ a)) (+T[,]T {A = A}{B = A} {δ = σ}))
           (ap (λ x → x) (semSb-T A σ (idA isCΔ a)) ◾
           ap (λ x → x)
           (semWk-T {A = A} {B = A} (⟦ σ ⟧S (idA isCΔ a))
           (coe (ap (λ x → x) (semSb-T A σ (idA isCΔ a)))
           (⟦ u ⟧tm (idA isCΔ a)))
           ⁻¹))
           ⁻¹
           ◾
           coecoe (ap (λ x → x) (semSb-T A σ (idA isCΔ a)))
           (ap (λ x → x)
           (semWk-T {A = A} {B = A} (⟦ σ ⟧S (idA isCΔ a))
           (coe (ap (λ x → x) (semSb-T A σ (idA isCΔ a)))
           (⟦ u ⟧tm (idA isCΔ a)))
           ⁻¹))
           ⁻¹
           ◾
           ap
           (λ x →
           coe
           (ap (λ x₁ → x₁)
           (semWk-T {A = A} {B = A} (⟦ σ ⟧S (idA isCΔ a))
           (coe (ap (λ x₁ → x₁) (semSb-T A σ (idA isCΔ a)))
           (⟦ u ⟧tm (idA isCΔ a)))
           ⁻¹))
           (coe (ap (λ x₁ → x₁) (semSb-T A σ (idA isCΔ a))) x))
           (sem-cohOp (+T[,]T {A = A}{B = A} {δ = σ}) (idA isCΔ a)))))
        z))
    (
    (eq-tm-iA isCΔ a v)
    ◾
    -- coe

-- (ap 
--   (λ z → coe
--     (ap2 _≡T_ (eq-tm-iA isCΔ a (wk-tm (t [ σ ]V)) ⁻¹)
--     (eq-tm-iA isCΔ a (wk-tm u) ⁻¹))
--     z)
    
    (ap 
      (λ z → coe
        (ap2 _≡T_ (eq-tm-iA isCΔ a (wk-tm (t [ σ ]V)) ⁻¹)
        (eq-tm-iA isCΔ a (wk-tm u) ⁻¹))
        z)
        (
        coe-inv
        {p = 
      (Eq2G (_≡T_)
      (ap (λ z → ⟦ z ⟧T (idA isCΔ a)) (+T[,]T  {A = A} {B = A}{δ = σ} {b = u}) ◾
        (semSb-T A σ (idA isCΔ a) ◾
        ap (λ v₁ → ∣ ⟦ A ⟧T v₁ ∣) (subst-idA isCΔ isCΓ σ a)))
        (coecoeap (ap (λ z → ⟦ z ⟧T (idA isCΔ a)) (+T[,]T  {A = A} {B = A}{δ = σ} {b = u}))
        (semSb-T A σ (idA isCΔ a) ◾
        ap (λ v₁ → ∣ ⟦ A ⟧T v₁ ∣) (subst-idA isCΔ isCΓ σ a))
        ⁻¹
        ◾
        (ap
        (λ z →
            subst idfun
            (semSb-T A σ (idA isCΔ a) ◾
            ap (λ v₁ → ∣ ⟦ A ⟧T v₁ ∣) (subst-idA isCΔ isCΓ σ a))
            z)
        (ap (λ z → coe z (iA isCΔ a ((A +T A) [ σ , u ]T)))
        (apid (ap (λ z → ⟦ z ⟧T (idA isCΔ a)) (+T[,]T  {A = A} {B = A}{δ = σ} {b = u})))
          ◾ apd (iA isCΔ a) (+T[,]T  {A = A} {B = A}{δ = σ} {b = u}))
        ◾
        coh4 (semSb-T A σ (idA isCΔ a))
        (ap (λ v₁ → ∣ ⟦ A ⟧T v₁ ∣) (subst-idA isCΔ isCΓ σ a))
        (iA isCΔ a (A [ σ ]T))
        ◾ semSb-iA isCΔ isCΓ σ a A))
        (coecoeap (ap (λ z → ⟦ z ⟧T (idA isCΔ a)) (+T[,]T  {A = A} {B = A}{δ = σ} {b = u}))
        (semSb-T A σ (idA isCΔ a) ◾
        ap (λ v₁ → ∣ ⟦ A ⟧T v₁ ∣) (subst-idA isCΔ isCΓ σ a))
        ⁻¹
        ◾
        (ap
        (λ z →
            subst idfun
            (semSb-T A σ (idA isCΔ a) ◾
            ap (λ v₁ → ∣ ⟦ A ⟧T v₁ ∣) (subst-idA isCΔ isCΓ σ a))
            z)
        (ap (λ z → coe z (iA isCΔ a ((A +T A) [ σ , u ]T)))
        (apid (ap (λ z → ⟦ z ⟧T (idA isCΔ a)) (+T[,]T  {A = A} {B = A}{δ = σ} {b = u})))
        ◾ apd (iA isCΔ a) (+T[,]T  {A = A} {B = A}{δ = σ} {b = u}))
        ◾
        coh4 (semSb-T A σ (idA isCΔ a))
        (ap (λ v₁ → ∣ ⟦ A ⟧T v₁ ∣) (subst-idA isCΔ isCΓ σ a))
        (iA isCΔ a (A [ σ ]T))
        ◾ semSb-iA isCΔ isCΓ σ a A)))        
        }
        (
        Refl2G _≡T_ reflT'
          (
          ap (λ z → ⟦ z ⟧T (idA isCΔ a)) (+T[,]T  {A = A} {B = A}{δ = σ} {b = u})
          ◾
          ((semSb-T A σ (idA isCΔ a))
          ◾
          (ap (λ v₁ → ∣ ⟦ A ⟧T v₁ ∣) (subst-idA isCΔ isCΓ σ a))
          )
          )
        {a = (iA isCΔ a ((A +T A) [ σ , u ]T))}
        {b = iA isCΓ a A}
        (
        coecoeap {B = idfun}
        (ap (λ z → ⟦ z ⟧T (idA isCΔ a)) (+T[,]T  {A = A} {B = A}{δ = σ} {b = u}))
        ((semSb-T A σ (idA isCΔ a))
          ◾
          (ap (λ v₁ → ∣ ⟦ A ⟧T v₁ ∣) (subst-idA isCΔ isCΓ σ a))
        )
        {t = (iA isCΔ a ((A +T A) [ σ , u ]T))}
        ⁻¹
        ◾
        (
        ap
          (λ z →
             subst idfun
             (semSb-T A σ (idA isCΔ a) ◾
              ap (λ v₁ → ∣ ⟦ A ⟧T v₁ ∣) (subst-idA isCΔ isCΓ σ a))
             z)
          (
          ap (λ z → coe z (iA isCΔ a ((A +T A) [ σ , u ]T)))
          (apid (ap (λ z → ⟦ z ⟧T (idA isCΔ a)) (+T[,]T  {A = A} {B = A}{δ = σ} {b = u})))
          ◾
          apd (iA isCΔ a)
            (+T[,]T  {A = A} {B = A}{δ = σ} {b = u})
          )
        ◾
        coh4 (semSb-T A σ (idA isCΔ a))
        (ap (λ v₁ → ∣ ⟦ A ⟧T v₁ ∣) (subst-idA isCΔ isCΓ σ a))
        (iA isCΔ a (A [ σ ]T))
        
        ◾
        semSb-iA isCΔ isCΓ σ a A
        )

        )
        )
        )
        
       

    )
    
    )
  ◾
  -- aplatissement
  
  coe4
  ((Eq2G ( _≡T_)
    (ap (λ z → ⟦ z ⟧T (idA isCΔ a)) (+T[,]T' A A σ) ◾
     (semSb-T A σ (idA isCΔ a) ◾
      ap (λ v₁ → ⟦ A ⟧T v₁) (subst-idA isCΔ isCΓ σ a)))
    (coecoeap (ap (λ z → ⟦ z ⟧T (idA isCΔ a)) (+T[,]T' A A σ))
     (semSb-T A σ (idA isCΔ a) ◾
      ap (λ v₁ → ⟦ A ⟧T v₁) (subst-idA isCΔ isCΓ σ a))
     ⁻¹
     ◾
     (ap
      (λ z →
         coe
         (ap (λ x → x)
          (semSb-T A σ (idA isCΔ a) ◾
           ap (λ v₁ → ⟦ A ⟧T v₁) (subst-idA isCΔ isCΓ σ a)))
         z)
      (ap (λ z → coe z (iA isCΔ a ((A +T A) [ σ , u ]T)))
       (apid (ap (λ z → ⟦ z ⟧T (idA isCΔ a)) (+T[,]T' A A σ)))
       ◾ apd (iA isCΔ a) (+T[,]T' A A σ))
      ◾
      coh4 (semSb-T A σ (idA isCΔ a))
      (ap (λ v₁ → ⟦ A ⟧T v₁) (subst-idA isCΔ isCΓ σ a))
      (iA isCΔ a (A [ σ ]T))
      ◾ semSb-iA isCΔ isCΓ σ a A))
    (coecoeap (ap (λ z → ⟦ z ⟧T (idA isCΔ a)) (+T[,]T' A A σ))
     (semSb-T A σ (idA isCΔ a) ◾
      ap (λ v₁ → ⟦ A ⟧T v₁) (subst-idA isCΔ isCΓ σ a))
     ⁻¹
     ◾
     (ap
      (λ z →
         coe
         (ap (λ x → x)
          (semSb-T A σ (idA isCΔ a) ◾
           ap (λ v₁ → ⟦ A ⟧T v₁) (subst-idA isCΔ isCΓ σ a)))
         z)
      (ap (λ z → coe z (iA isCΔ a ((A +T A) [ σ , u ]T)))
       (apid (ap (λ z → ⟦ z ⟧T (idA isCΔ a)) (+T[,]T' A A σ)))
       ◾ apd (iA isCΔ a) (+T[,]T' A A σ))
      ◾
      coh4 (semSb-T A σ (idA isCΔ a))
      (ap (λ v₁ → ⟦ A ⟧T v₁) (subst-idA isCΔ isCΓ σ a))
      (iA isCΔ a (A [ σ ]T))
      ◾ semSb-iA isCΔ isCΓ σ a A))
    ⁻¹))

  ((ap2 _≡T_ (eq-tm-iA isCΔ a ((t [ σ ]V) ⟦ +T[,]T' A A σ ⟫) ⁻¹)
    (eq-tm-iA isCΔ a (u ⟦ +T[,]T' A A σ ⟫) ⁻¹)))

  ((ap (λ x → x)
  (Eq2G (_≡T_) (semSb-T (A +T A) (σ , u) (idA isCΔ a))
   (ap (λ e → coe e (⟦ (t [ σ ]V) ⟦ +T[,]T' A A σ ⟫ ⟧tm (idA isCΔ a)))
    (uip (ap (λ x → x) (semSb-T (A +T A) (σ , u) (idA isCΔ a)))
     (ap (λ x₁ → ⟦ x₁ ⟧T (idA isCΔ a)) (+T[,]T' A A σ) ◾
      (ap (λ x → x) (semSb-T A σ (idA isCΔ a)) ◾
       ap (λ x → x)
       (semWk-T' A A (⟦ σ ⟧S (idA isCΔ a))
        (coe (ap (λ x → x) (semSb-T A σ (idA isCΔ a)))
         (⟦ u ⟧tm (idA isCΔ a)))
        ⁻¹))))
    ◾
    coecoe (ap (λ x₁ → ⟦ x₁ ⟧T (idA isCΔ a)) (+T[,]T' A A σ))
    (ap (λ x → x) (semSb-T A σ (idA isCΔ a)) ◾
     ap (λ x → x)
     (semWk-T' A A (⟦ σ ⟧S (idA isCΔ a))
      (coe (ap (λ x → x) (semSb-T A σ (idA isCΔ a)))
       (⟦ u ⟧tm (idA isCΔ a)))
      ⁻¹))
    ⁻¹
    ◾
    coecoe (ap (λ x → x) (semSb-T A σ (idA isCΔ a)))
    (ap (λ x → x)
     (semWk-T' A A (⟦ σ ⟧S (idA isCΔ a))
      (coe (ap (λ x → x) (semSb-T A σ (idA isCΔ a)))
       (⟦ u ⟧tm (idA isCΔ a)))
      ⁻¹))
    ⁻¹
    ◾
    ap
    (λ e →
       coe
       (ap (λ x → x)
        (semWk-T' A A (⟦ σ ⟧S (idA isCΔ a))
         (coe (ap (λ x → x) (semSb-T A σ (idA isCΔ a)))
          (⟦ u ⟧tm (idA isCΔ a)))
         ⁻¹))
       (coe (ap (λ x → x) (semSb-T A σ (idA isCΔ a))) e))
    (sem-cohOp (+T[,]T' A A σ) (idA isCΔ a))
    ◾
    ap
    (coe
     (ap (λ x → x)
      (semWk-T' A A (⟦ σ ⟧S (idA isCΔ a))
       (coe (ap (λ x → x) (semSb-T A σ (idA isCΔ a)))
        (⟦ u ⟧tm (idA isCΔ a)))
       ⁻¹)))
    (semSb-V t σ (idA isCΔ a)))
   (ap (λ x → coe x (⟦ u ⟦ +T[,]T' A A σ ⟫ ⟧tm (idA isCΔ a)))
    (uip (ap (λ x → x) (semSb-T (A +T A) (σ , u) (idA isCΔ a)))
     (ap (λ x → ⟦ x ⟧T (idA isCΔ a)) (+T[,]T' A A σ) ◾
      (ap (λ x → x) (semSb-T A σ (idA isCΔ a)) ◾
       ap (λ x → x)
       (semWk-T' A A (⟦ σ ⟧S (idA isCΔ a))
        (coe (ap (λ x → x) (semSb-T A σ (idA isCΔ a)))
         (⟦ u ⟧tm (idA isCΔ a)))
        ⁻¹))))
    ◾
    coecoe (ap (λ x → ⟦ x ⟧T (idA isCΔ a)) (+T[,]T' A A σ))
    (ap (λ x → x) (semSb-T A σ (idA isCΔ a)) ◾
     ap (λ x → x)
     (semWk-T' A A (⟦ σ ⟧S (idA isCΔ a))
      (coe (ap (λ x → x) (semSb-T A σ (idA isCΔ a)))
       (⟦ u ⟧tm (idA isCΔ a)))
      ⁻¹))
    ⁻¹
    ◾
    coecoe (ap (λ x → x) (semSb-T A σ (idA isCΔ a)))
    (ap (λ x → x)
     (semWk-T' A A (⟦ σ ⟧S (idA isCΔ a))
      (coe (ap (λ x → x) (semSb-T A σ (idA isCΔ a)))
       (⟦ u ⟧tm (idA isCΔ a)))
      ⁻¹))
    ⁻¹
    ◾
    ap
    (λ x →
       coe
       (ap (λ x₁ → x₁)
        (semWk-T' A A (⟦ σ ⟧S (idA isCΔ a))
         (coe (ap (λ x₁ → x₁) (semSb-T A σ (idA isCΔ a)))
          (⟦ u ⟧tm (idA isCΔ a)))
         ⁻¹))
       (coe (ap (λ x₁ → x₁) (semSb-T A σ (idA isCΔ a))) x))
    (sem-cohOp (+T[,]T' A A σ) (idA isCΔ a))))))

  ((ap
  (λ γ →
  coe (ap (λ x → x) (semWk-T' A A (proj₁ γ) (proj₂ γ) ⁻¹))
  (π t (proj₁ γ))
  ≡T
  coe (ap (λ x → x) (semWk-T' A A (proj₁ γ) (proj₂ γ) ⁻¹)) (proj₂ γ))
  (,Σ= (subst-idA isCΔ isCΓ σ a)
  (ap
  (λ z₁ →
  coe (ap (λ v₁ → ⟦ A ⟧T v₁) (subst-idA isCΔ isCΓ σ a))
  (coe (ap (λ x → x) (semSb-T A σ (idA isCΔ a))) z₁))
  (eq-tm-iA isCΔ a u)
  ◾ semSb-iA isCΔ isCΓ σ a A
  ◾ eq-var-iA isCΓ a t ⁻¹))))
  
  -- uip
  ◾
  
  ap (λ z → coe z (reflT' (iA isCΓ a A)))
  (uip



    (Eq2G (_≡T_)
      (ap (λ z → ⟦ z ⟧T (idA isCΔ a)) (+T[,]T' A A σ) ◾
        (semSb-T A σ (idA isCΔ a) ◾
        ap (λ v₁ → ⟦ A ⟧T v₁) (subst-idA isCΔ isCΓ σ a)))
      (coecoeap (ap (λ z → ⟦ z ⟧T (idA isCΔ a)) (+T[,]T' A A σ))
        (semSb-T A σ (idA isCΔ a) ◾
        ap (λ v₁ → ⟦ A ⟧T v₁) (subst-idA isCΔ isCΓ σ a))
        ⁻¹
        ◾
        (ap
        (λ z →
            coe
            (ap (λ x → x)
            (semSb-T A σ (idA isCΔ a) ◾
              ap (λ v₁ → ⟦ A ⟧T v₁) (subst-idA isCΔ isCΓ σ a)))
            z)
        (ap (λ z → coe z (iA isCΔ a ((A +T A) [ σ , u ]T)))
          (apid (ap (λ z → ⟦ z ⟧T (idA isCΔ a)) (+T[,]T' A A σ)))
          ◾ apd (iA isCΔ a) (+T[,]T' A A σ))
        ◾
        coh4 (semSb-T A σ (idA isCΔ a))
        (ap (λ v₁ → ⟦ A ⟧T v₁) (subst-idA isCΔ isCΓ σ a))
        (iA isCΔ a (A [ σ ]T))
        ◾ semSb-iA isCΔ isCΓ σ a A))
      (coecoeap (ap (λ z → ⟦ z ⟧T (idA isCΔ a)) (+T[,]T' A A σ))
        (semSb-T A σ (idA isCΔ a) ◾
        ap (λ v₁ → ⟦ A ⟧T v₁) (subst-idA isCΔ isCΓ σ a))
        ⁻¹
        ◾
        (ap
        (λ z →
            coe
            (ap (λ x → x)
            (semSb-T A σ (idA isCΔ a) ◾
              ap (λ v₁ → ⟦ A ⟧T v₁) (subst-idA isCΔ isCΓ σ a)))
            z)
        (ap (λ z → coe z (iA isCΔ a ((A +T A) [ σ , u ]T)))
          (apid (ap (λ z → ⟦ z ⟧T (idA isCΔ a)) (+T[,]T' A A σ)))
          ◾ apd (iA isCΔ a) (+T[,]T' A A σ))
        ◾
        coh4 (semSb-T A σ (idA isCΔ a))
        (ap (λ v₁ → ⟦ A ⟧T v₁) (subst-idA isCΔ isCΓ σ a))
        (iA isCΔ a (A [ σ ]T))
        ◾ semSb-iA isCΔ isCΓ σ a A))
      ⁻¹
      ◾
      ap2 _≡T_ (eq-tm-iA isCΔ a ((t [ σ ]V) ⟦ +T[,]T' A A σ ⟫) ⁻¹)
      (eq-tm-iA isCΔ a (u ⟦ +T[,]T' A A σ ⟫) ⁻¹)
      ◾
      ap (λ x → x)
      (Eq2G (_≡T_) (semSb-T (A +T A) (σ , u) (idA isCΔ a))
        (ap (λ e → coe e (⟦ (t [ σ ]V) ⟦ +T[,]T' A A σ ⟫ ⟧tm (idA isCΔ a)))
        (uip (ap (λ x → x) (semSb-T (A +T A) (σ , u) (idA isCΔ a)))
          (ap (λ x₁ → ⟦ x₁ ⟧T (idA isCΔ a)) (+T[,]T' A A σ) ◾
          (ap (λ x → x) (semSb-T A σ (idA isCΔ a)) ◾
            ap (λ x → x)
            (semWk-T' A A (⟦ σ ⟧S (idA isCΔ a))
            (coe (ap (λ x → x) (semSb-T A σ (idA isCΔ a)))
              (⟦ u ⟧tm (idA isCΔ a)))
            ⁻¹))))
        ◾
        coecoe (ap (λ x₁ → ⟦ x₁ ⟧T (idA isCΔ a)) (+T[,]T' A A σ))
        (ap (λ x → x) (semSb-T A σ (idA isCΔ a)) ◾
          ap (λ x → x)
          (semWk-T' A A (⟦ σ ⟧S (idA isCΔ a))
          (coe (ap (λ x → x) (semSb-T A σ (idA isCΔ a)))
            (⟦ u ⟧tm (idA isCΔ a)))
          ⁻¹))
        ⁻¹
        ◾
        coecoe (ap (λ x → x) (semSb-T A σ (idA isCΔ a)))
        (ap (λ x → x)
          (semWk-T' A A (⟦ σ ⟧S (idA isCΔ a))
          (coe (ap (λ x → x) (semSb-T A σ (idA isCΔ a)))
            (⟦ u ⟧tm (idA isCΔ a)))
          ⁻¹))
        ⁻¹
        ◾
        ap
        (λ e →
            coe
            (ap (λ x → x)
            (semWk-T' A A (⟦ σ ⟧S (idA isCΔ a))
              (coe (ap (λ x → x) (semSb-T A σ (idA isCΔ a)))
              (⟦ u ⟧tm (idA isCΔ a)))
              ⁻¹))
            (coe (ap (λ x → x) (semSb-T A σ (idA isCΔ a))) e))
        (sem-cohOp (+T[,]T' A A σ) (idA isCΔ a))
        ◾
        ap
        (coe
          (ap (λ x → x)
          (semWk-T' A A (⟦ σ ⟧S (idA isCΔ a))
            (coe (ap (λ x → x) (semSb-T A σ (idA isCΔ a)))
            (⟦ u ⟧tm (idA isCΔ a)))
            ⁻¹)))
        (semSb-V t σ (idA isCΔ a)))
        (ap (λ x → coe x (⟦ u ⟦ +T[,]T' A A σ ⟫ ⟧tm (idA isCΔ a)))
        (uip (ap (λ x → x) (semSb-T (A +T A) (σ , u) (idA isCΔ a)))
          (ap (λ x → ⟦ x ⟧T (idA isCΔ a)) (+T[,]T' A A σ) ◾
          (ap (λ x → x) (semSb-T A σ (idA isCΔ a)) ◾
            ap (λ x → x)
            (semWk-T' A A (⟦ σ ⟧S (idA isCΔ a))
            (coe (ap (λ x → x) (semSb-T A σ (idA isCΔ a)))
              (⟦ u ⟧tm (idA isCΔ a)))
            ⁻¹))))
        ◾
        coecoe (ap (λ x → ⟦ x ⟧T (idA isCΔ a)) (+T[,]T' A A σ))
        (ap (λ x → x) (semSb-T A σ (idA isCΔ a)) ◾
          ap (λ x → x)
          (semWk-T' A A (⟦ σ ⟧S (idA isCΔ a))
          (coe (ap (λ x → x) (semSb-T A σ (idA isCΔ a)))
            (⟦ u ⟧tm (idA isCΔ a)))
          ⁻¹))
        ⁻¹
        ◾
        coecoe (ap (λ x → x) (semSb-T A σ (idA isCΔ a)))
        (ap (λ x → x)
          (semWk-T' A A (⟦ σ ⟧S (idA isCΔ a))
          (coe (ap (λ x → x) (semSb-T A σ (idA isCΔ a)))
            (⟦ u ⟧tm (idA isCΔ a)))
          ⁻¹))
        ⁻¹
        ◾
        ap
        (λ x →
            coe
            (ap (λ x₁ → x₁)
            (semWk-T' A A (⟦ σ ⟧S (idA isCΔ a))
              (coe (ap (λ x₁ → x₁) (semSb-T A σ (idA isCΔ a)))
              (⟦ u ⟧tm (idA isCΔ a)))
              ⁻¹))
            (coe (ap (λ x₁ → x₁) (semSb-T A σ (idA isCΔ a))) x))
        (sem-cohOp (+T[,]T' A A σ) (idA isCΔ a))))
      ◾
      ap
      (λ γ →
          coe (ap (λ x → x) (semWk-T' A A (proj₁ γ) (proj₂ γ) ⁻¹))
          (π t (proj₁ γ))
          ≡T
          coe (ap (λ x → x) (semWk-T' A A (proj₁ γ) (proj₂ γ) ⁻¹)) (proj₂ γ))
      (,Σ= (subst-idA isCΔ isCΓ σ a)
        (ap
        (λ z₁ →
            coe (ap (λ v₁ → ⟦ A ⟧T v₁) (subst-idA isCΔ isCΓ σ a))
            (coe (ap (λ x → x) (semSb-T A σ (idA isCΔ a))) z₁))
        (eq-tm-iA isCΔ a u)
        ◾ semSb-iA isCΔ isCΓ σ a A
        ◾ eq-var-iA isCΓ a t ⁻¹)))




    (Eq2G (_≡T_)
    (semWk-T' A A (idA isCΓ a) (π t (idA isCΓ a)) ⁻¹)
    (ap
    (λ z →
    coe
    (ap (λ x → x) (semWk-T' A A (idA isCΓ a) (π t (idA isCΓ a)) ⁻¹)) z)
    (eq-var-iA isCΓ a t ⁻¹))
    (ap
    (λ z →
    coe
    (ap (λ x → x) (semWk-T' A A (idA isCΓ a) (π t (idA isCΓ a)) ⁻¹)) z)
    (eq-var-iA isCΓ a t ⁻¹)))
  )
  

  ◾ 
  -- du cooté droit on a
  -- reflT' 
  --   (subst ∣_∣ (sym (semWk-T {A = A} {B = A} (idA isCΓ a) (π t (idA isCΓ a))))
  --   (π t (idA isCΓ a)))
  -- que l'on réécrit en un transport de reflT' (iA Γ) par eq-var-iA t
    Refl2G _≡T_ reflT'
    (sym (semWk-T {A = A} {B = A} (idA isCΓ a) (π t (idA isCΓ a))))

    {b = (subst ∣_∣ (sym (semWk-T {A = A} {B = A} (idA isCΓ a) (π t (idA isCΓ a))))
      (π t (idA isCΓ a)))}
      (ap (λ z → subst idfun (sym (semWk-T {A = A} {B = A} (idA isCΓ a) (π t (idA isCΓ a))))
         z) (eq-var-iA isCΓ a t ⁻¹))
  
  )
  -- -}


 
-- A.4.3
JA-idA-fib c* P d a = refl
JA-idA-fib (ext isCΔ {A} t) P ⦃ fibP = fibP ⦄ d a =
-- on transforme JT du transport de reflT  en transport de JT de refl
{-
****************

Je commente la preuve et je mets admit pour que ca compile plus vite

****************
vérifié post-fib
-}
   admit
  
 {- 
  ap
    (λ z →
       coe
       (ap (λ w → P (idA isCΔ a ,Σ π t (idA isCΔ a) ,Σ w))
        (coe2
         (Eq2G _≡T_ (sym (semWk-T' A A (idA isCΔ a) (π t (idA isCΔ a))))
          refl refl)
         (reflT'
          (subst ∣_∣ (sym (semWk-T' A A (idA isCΔ a) (π t (idA isCΔ a))))
           (π t (idA isCΔ a))))))
       z)
    (
    coe2r 
      (coe-inv
      {p = (Eq2G (_≡T_)
        (sym (semWk-T' A A (idA isCΔ a) (π t (idA isCΔ a)))) refl refl
        )}
      (Refl2G (_≡T_) (reflT')
      (sym (semWk-T' A A (idA isCΔ a) (π t (idA isCΔ a)))) refl)
      ⁻¹)
    (apd
      (λ z →
         JFib
         ⦃ fibA = Fib-T A (idA isCΔ a) ⦄
         (λ {y} e →
            P
            (idA isCΔ a ,Σ y ,Σ
             coe (Eq2G _≡T_ (sym (semWk-T' A A (idA isCΔ a) y)) refl refl) e))
             ⦃ fibP = (λ y e →
             fibP
             (idA isCΔ a ,Σ y ,Σ
             coe (Eq2G _≡T_ (sym (semWk-T' A A (idA isCΔ a) y)) refl refl) e)) ⦄
         (subst (λ w → P (idA isCΔ a ,Σ π t (idA isCΔ a) ,Σ w))
          (Refl2G _≡T_ reflT'
           (sym (semWk-T' A A (idA isCΔ a) (π t (idA isCΔ a)))) refl
           ⁻¹)
          (JA-fib isCΔ
           (λ δ' →
              P
              (δ' ,Σ π t δ' ,Σ
               reflT' (subst ∣_∣ (sym (semWk-T' A A δ' (π t δ'))) (π t δ'))))
               ⦃ fibP = (λ δ' →
                fibP
                (δ' ,Σ π t δ' ,Σ
                reflT' (subst ∣_∣ (sym (semWk-T' A A δ' (π t δ'))) (π t δ')))) ⦄
           d (idA isCΔ a)))
         z)
      {a₀ =
       coe
       (Eq2G _≡T_ (sym (semWk-T' A A (idA isCΔ a) (π t (idA isCΔ a))))
        refl refl
        ⁻¹)
       (reflT'
        (subst ∣_∣ (sym (semWk-T' A A (idA isCΔ a) (π t (idA isCΔ a))))
         (π t (idA isCΔ a))))}
         (coe-inv {p = (Eq2G (_≡T_)
         (sym (semWk-T' A A (idA isCΔ a) (π t (idA isCΔ a)))) refl refl
         )}
         (Refl2G _≡T_ reflT'
         (sym (semWk-T' A A (idA isCΔ a) (π t (idA isCΔ a)))) refl
         ) ⁻¹))
         ◾
         ap
           (coe
            (ap
             (λ z →
                P
                (idA isCΔ a ,Σ π t (idA isCΔ a) ,Σ
                 coe
                 (Eq2G _≡T_ (semWk-T' A A (idA isCΔ a) (π t (idA isCΔ a)) ⁻¹) refl
                  refl)
                 z))
             ((coe-inv
                {p = (Eq2G (_≡T_)
                (sym (semWk-T' A A (idA isCΔ a) (π t (idA isCΔ a)))) refl refl
                )}
               (Refl2G _≡T_ reflT'
                (semWk-T' A A (idA isCΔ a) (π t (idA isCΔ a)) ⁻¹) refl)
               ⁻¹)
              ⁻¹)))
              -- utilisation explicite de la règle de réduction
              (βJFib ⦃ fibA =
                  Fib-T A (idA isCΔ a) 
                ⦄
                (λ {y} e →
              P
              (idA isCΔ a ,Σ y ,Σ
              coe
              (Eq2G (_≡T_) (sym (semWk-T' A A (idA isCΔ a) y)) refl
              refl)
              e))
              ⦃ fibP = (λ y e →
              fibP
              (idA isCΔ a ,Σ y ,Σ
              coe
              (Eq2G (_≡T_) (sym (semWk-T' A A (idA isCΔ a) y)) refl
              refl)
              e)) ⦄
              (subst (λ w → P (idA isCΔ a ,Σ π t (idA isCΔ a) ,Σ w))
              (Refl2G (_≡T_) (reflT')
              (sym (semWk-T' A A (idA isCΔ a) (π t (idA isCΔ a)))) refl
              ⁻¹)
              (JA-fib isCΔ
              (λ δ' →
              P
                (δ' ,Σ π t δ' ,Σ
                  reflT' (subst ∣_∣ (sym (semWk-T' A A δ' (π t δ'))) (π t δ'))))
              ⦃ fibP = (λ δ' →
                  fibP
                  (δ' ,Σ π t δ' ,Σ
                  reflT' (subst ∣_∣ (sym (semWk-T' A A δ' (π t δ'))) (π t δ')))) ⦄
              d (idA isCΔ a)
              ))
              )
         )
      ◾
      cccoe



     (ap (λ w → P (idA isCΔ a ,Σ π t (idA isCΔ a) ,Σ w))
     (Refl2G (_≡T_) (reflT')
     (sym (semWk-T' A A (idA isCΔ a) (π t (idA isCΔ a)))) refl
     ⁻¹)
     )



    (ap
    (λ z →
    P
    (idA isCΔ a ,Σ π t (idA isCΔ a) ,Σ
    coe
    (Eq2G (_≡T_)
    (sym (semWk-T' A A (idA isCΔ a) (π t (idA isCΔ a)))) refl refl)
    z))
    ((coe-inv
      {p = (Eq2G (_≡T_)
      (sym (semWk-T' A A (idA isCΔ a) (π t (idA isCΔ a)))) refl refl
      )}
    (Refl2G (_≡T_) (reflT')
    (sym (semWk-T' A A (idA isCΔ a) (π t (idA isCΔ a)))) refl)
    ⁻¹)
    ⁻¹))



      ((ap (λ w → P (idA isCΔ a ,Σ π t (idA isCΔ a) ,Σ w))
      (coe2
      (Eq2G (_≡T_)
      (sym (semWk-T' A A (idA isCΔ a) (π t (idA isCΔ a)))) refl refl)
      (reflT'
      (subst ∣_∣ (sym (semWk-T' A A (idA isCΔ a) (π t (idA isCΔ a))))
      (π t (idA isCΔ a)))))))
      
      ◾
      
      ap (λ z → coe z (JA-fib isCΔ
        (λ δ' →
        P
        (δ' ,Σ π t δ' ,Σ
        reflT' (subst ∣_∣ (sym (semWk-T' A A δ' (π t δ'))) (π t δ'))))
        ⦃ fibP = (λ δ' →
        fibP
        (δ' ,Σ π t δ' ,Σ
        reflT' (subst ∣_∣ (sym (semWk-T' A A δ' (π t δ'))) (π t δ')))) ⦄
        d (idA isCΔ a)))

      (uip
      ((ap (λ w → P (idA isCΔ a ,Σ π t (idA isCΔ a) ,Σ w))
      (Refl2G (_≡T_) (reflT')
      (sym (semWk-T' A A (idA isCΔ a) (π t (idA isCΔ a)))) refl
      ⁻¹)
      ◾
      ap
      (λ z →
      P
      (idA isCΔ a ,Σ π t (idA isCΔ a) ,Σ
      coe
      (Eq2G (_≡T_)
      (sym (semWk-T' A A (idA isCΔ a) (π t (idA isCΔ a)))) refl refl)
      z))
      ((coe-inv
        {p = (Eq2G (_≡T_)
          (sym (semWk-T' A A (idA isCΔ a) (π t (idA isCΔ a)))) refl refl
        )}
      (Refl2G (_≡T_) (reflT')
      (sym (semWk-T' A A (idA isCΔ a) (π t (idA isCΔ a)))) refl)
      ⁻¹)
      ⁻¹)
      ◾
      ap (λ w → P (idA isCΔ a ,Σ π t (idA isCΔ a) ,Σ w))
      (coe2
      (Eq2G (_≡T_)
      (sym (semWk-T' A A (idA isCΔ a) (π t (idA isCΔ a)))) refl refl)
      (reflT'
      (subst ∣_∣ (sym (semWk-T' A A (idA isCΔ a) (π t (idA isCΔ a))))
      (π t (idA isCΔ a)))))))
      refl
      )
      
      ◾
      JA-idA-fib isCΔ (λ δ' →
        P
        (δ' ,Σ π t δ' ,Σ
        reflT' (subst ∣_∣ (sym (semWk-T' A A δ' (π t δ'))) (π t δ'))))
        ⦃ fibP = (λ δ' →
        fibP
        (δ' ,Σ π t δ' ,Σ
        reflT' (subst ∣_∣ (sym (semWk-T' A A δ' (π t δ'))) (π t δ')))) ⦄
        d a


 --   -}
  
  



-- JA-fib isCΓ ⟦ A ⟧T (λ a₁ → iA isCΓ a₁ A) (⟦ δ ⟧S (idA isC a)) ≡
-- coe (ap (λ v → ⟦ A ⟧T v) (subst-idA isC isCΓ δ a ⁻¹)) (iA isCΓ a A)

-- eq-tm-iA isC a {B} t = {!!}
-- par récurrence sur le terme
eq-tm-iA isC a {B} (var x) = eq-var-iA isC a x
eq-tm-iA isC a {.(A [ δ ]T)} (coh isCΓ δ A) =
  
  ap (λ z → coe (ap (λ x → x) (semSb-T A δ (idA isC a) ⁻¹)) z)
  -- TODO coucou
  (
  (
  J {x = idA  isCΓ a}
  (λ {y} e → JA-fib isCΓ ⟦ A ⟧T ⦃ fibP = Fib-T A ⦄ (λ a₁ → iA isCΓ a₁ A) y ≡
     coe (ap ⟦ A ⟧T e) (iA isCΓ a A))
     (JA-idA-fib isCΓ ⟦ A ⟧T ⦃ fibP = Fib-T A ⦄ (λ a₁ → iA isCΓ a₁ A) a)
     ((subst-idA isC isCΓ δ a)⁻¹)
     )
  )
  -- (
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

postulate
   admit-eq-var : {l : _} {A : Set l} → A

-- par récurrence sur le type A
-- wk-iA isCΓ a A {B} t = {!!}
wk-iA isCΓ a * {B} t = refl
wk-iA isCΓ a (_=h_ {A = A} x y) {B} t =
  -- aplatissement
  cccoe
  (ap2 _≡T_ (eq-tm-iA isCΓ a x ⁻¹) (eq-tm-iA isCΓ a y ⁻¹))
  (ap (λ x₁ → x₁)
    (Eq2G _≡T_ (semWk-T' A B (idA isCΓ a) (π t (idA isCΓ a)))
    (semWk-tm (idA isCΓ a) (π t (idA isCΓ a)) x)
    (semWk-tm (idA isCΓ a) (π t (idA isCΓ a)) y)
    ⁻¹))
  (ap (λ x₁ → x₁)
    (Eq2G _≡T_
    (semWk-T' (A +T B) (var (vS t) =h var v0)
    (idA isCΓ a ,Σ π t (idA isCΓ a)) reflT)
    (semWk-tm (idA isCΓ a ,Σ π t (idA isCΓ a)) reflT (x +tm B))
    (semWk-tm (idA isCΓ a ,Σ π t (idA isCΓ a)) reflT (y +tm B))
    ⁻¹))


  ◾
  -- uip
   ap (λ z → coe z (reflT' (iA isCΓ a A)))
  (uip



    (ap2 _≡T_ (eq-tm-iA isCΓ a x ⁻¹) (eq-tm-iA isCΓ a y ⁻¹) ◾
        ap (λ x₁ → x₁)
        (Eq2G (_≡T_)
        (semWk-T' A B (idA isCΓ a) (π t (idA isCΓ a)))
        (semWk-tm (idA isCΓ a) (π t (idA isCΓ a)) x)
        (semWk-tm (idA isCΓ a) (π t (idA isCΓ a)) y)
        ⁻¹)
        ◾
        ap (λ x₁ → x₁)
        (Eq2G (_≡T_)
        (semWk-T' (A +T B) (var (vS t) =h var v0)
        (idA isCΓ a ,Σ π t (idA isCΓ a)) reflT)
        (semWk-tm (idA isCΓ a ,Σ π t (idA isCΓ a)) reflT (x +tm B))
        (semWk-tm (idA isCΓ a ,Σ π t (idA isCΓ a)) reflT (y +tm B))
        ⁻¹))




    ((Eq2G (_≡T_)
      (semWk-T' A B (idA isCΓ a) (π t (idA isCΓ a)) ⁻¹ ◾
      semWk-T' (A +T B) (var (vS t) =h var v0)
      (idA isCΓ a ,Σ π t (idA isCΓ a)) reflT
      ⁻¹)
      (coecoeap (semWk-T' A B (idA isCΓ a) (π t (idA isCΓ a)) ⁻¹)
      (semWk-T' (A +T B) (var (vS t) =h var v0)
      (idA isCΓ a ,Σ π t (idA isCΓ a)) reflT
      ⁻¹)
      ⁻¹
      ◾ wk-iA isCΓ a A t)
      (coecoeap (semWk-T' A B (idA isCΓ a) (π t (idA isCΓ a)) ⁻¹)
      (semWk-T' (A +T B) (var (vS t) =h var v0)
      (idA isCΓ a ,Σ π t (idA isCΓ a)) reflT
      ⁻¹)
      ⁻¹
      ◾ wk-iA isCΓ a A t)
      ◾
      ap2 _≡T_
      (eq-tm-iA (ext isCΓ t) a (x +tm B +tm (var (vS t) =h var v0)) ⁻¹)
      (eq-tm-iA (ext isCΓ t) a (y +tm B +tm (var (vS t) =h var v0)) ⁻¹)))
  )
  
  ◾
  -- aplatissement
  coecoe
  (Eq2G (_≡T_)
    (semWk-T' A B (idA isCΓ a) (π t (idA isCΓ a)) ⁻¹ ◾
    semWk-T' (A +T B) (var (vS t) =h var v0)
    (idA isCΓ a ,Σ π t (idA isCΓ a)) reflT
    ⁻¹)
    (coecoeap (semWk-T' A B (idA isCΓ a) (π t (idA isCΓ a)) ⁻¹)
    (semWk-T' (A +T B) (var (vS t) =h var v0)
    (idA isCΓ a ,Σ π t (idA isCΓ a)) reflT
    ⁻¹)
    ⁻¹
    ◾ wk-iA isCΓ a A t)
    (coecoeap (semWk-T' A B (idA isCΓ a) (π t (idA isCΓ a)) ⁻¹)
    (semWk-T' (A +T B) (var (vS t) =h var v0)
    (idA isCΓ a ,Σ π t (idA isCΓ a)) reflT
    ⁻¹)
    ⁻¹
    ◾ wk-iA isCΓ a A t))
  (ap2 _≡T_
    (eq-tm-iA (ext isCΓ t) a (x +tm B +tm (var (vS t) =h var v0)) ⁻¹)
    (eq-tm-iA (ext isCΓ t) a (y +tm B +tm (var (vS t) =h var v0)) ⁻¹))
  ⁻¹
  

  ◾
  ap
    (λ z →
       coe
       (ap2 _≡T_
        (eq-tm-iA (ext isCΓ t) a (x +tm B +tm (var (vS t) =h var v0)) ⁻¹)
        (eq-tm-iA (ext isCΓ t) a (y +tm B +tm (var (vS t) =h var v0)) ⁻¹))
       z)
       (Refl2G _≡T_ reflT'
          (
          (semWk-T' A B (idA isCΓ a) (π t (idA isCΓ a)) ⁻¹)
          ◾
          ((semWk-T' (A +T B) ( (var (vS t)) =h (var v0) ) (idA isCΓ a ,Σ π t (idA isCΓ a)) reflT ⁻¹)
          )
          
          )
       {b = iA (ext isCΓ t) a (A +T B +T (var (vS t) =h var v0))}
       (
       coecoeap (semWk-T' A B (idA isCΓ a) (π t (idA isCΓ a)) ⁻¹)
         (semWk-T' (A +T B) ( (var (vS t)) =h (var v0) ) (idA isCΓ a ,Σ π t (idA isCΓ a)) reflT ⁻¹)
         {t = (iA isCΓ a A)}
         ⁻¹
        
       ◾
       wk-iA isCΓ a A t
       )
       )

-- par récurrence sur la variable et sur le contexte
-- eq-var-iA isC a {B} x = {!!}
eq-var-iA c* a {.*} v0 = refl
eq-var-iA c* a {.(_ +T *)} (vS ())
eq-var-iA (ext isC {A} t) a {.(A +T A +T (var (vS t) =h var v0))} (vS v0) = 
    ap
    (λ z →
    coe
    (ap (λ x₁ → x₁)
    (semWk-T' (A +T A) (var (vS t) =h var v0)
    (idA isC a ,Σ π t (idA isC a)) reflT
    ⁻¹))
    (coe
    (ap (λ x₁ → x₁) (semWk-T' A A (idA isC a) (π t (idA isC a)) ⁻¹))
    z))
    (eq-var-iA isC a t)
    ◾
    wk-iA isC a A t

eq-var-iA (ext isC {A} t) a {.(var (vS (vS t)) =h var (vS v0))} v0 =
  
  ap
    (subst ∣_∣
    (sym
    (semWk-T' (var (vS t) =h var v0) (var (vS t) =h var v0) (idA isC a ,Σ π t (idA isC a))
    (reflT'
    (subst ∣_∣ (sym (semWk-T' A A (idA isC a) (π t (idA isC a))))
    (π t (idA isC a)))))))
   ((
   coe-inv
   {p =
      (Eq2G (_≡T_)
      (sym
      (semWk-T' (A +T A) (var (vS t) =h var v0)
      (idA isC a ,Σ π t (idA isC a)) reflT))
      (ap
      (λ z →
      subst idfun
      (sym
      (semWk-T' (A +T A) (var (vS t) =h var v0)
      (idA isC a ,Σ π t (idA isC a)) reflT))
      (subst ∣_∣ (sym (semWk-T' A A (idA isC a) (π t (idA isC a)))) z))
      (eq-var-iA isC a t)
      ◾ wk-iA isC a A t)
      (ap
      (λ z →
      subst idfun
      (sym
      (semWk-T' (A +T A) (var (vS t) =h var v0)
      (idA isC a ,Σ π t (idA isC a)) reflT))
      (subst ∣_∣ (sym (semWk-T' A A (idA isC a) (π t (idA isC a)))) z))
      (eq-var-iA isC a t)
      ◾ wk-iA isC a A t))
   }
   (Refl2G _≡T_ reflT' (sym (semWk-T' (A +T A) (var (vS t) =h var v0)
        (idA isC a ,Σ π t (idA isC a)) reflT))
        {a = (subst ∣_∣ (sym (semWk-T' A A (idA isC a) (π t (idA isC a))))
           (π t (idA isC a)))}

          (
           ap
             (λ z →
                subst idfun
                (sym
                 (semWk-T' (A +T A) (var (vS t) =h var v0)
                  (idA isC a ,Σ π t (idA isC a)) reflT))
                (subst ∣_∣ (sym (semWk-T' A A (idA isC a) (π t (idA isC a)))) z))
             (eq-var-iA isC a t)
          ◾
          wk-iA isC a A t)
   )


   )) 
    ◾
    (
   coecoe
      (
       (Eq2G (_≡T_)
        (sym
         (semWk-T' (A +T A) (var (vS t) =h var v0)
          (idA isC a ,Σ π t (idA isC a)) reflT))
        (ap
         (λ z →
            subst idfun
            (sym
             (semWk-T' (A +T A) (var (vS t) =h var v0)
              (idA isC a ,Σ π t (idA isC a)) reflT))
            (subst ∣_∣ (sym (semWk-T' A A (idA isC a) (π t (idA isC a)))) z))
         (eq-var-iA isC a t)
         ◾ wk-iA isC a A t)
        (ap
         (λ z →
            subst idfun
            (sym
             (semWk-T' (A +T A) (var (vS t) =h var v0)
              (idA isC a ,Σ π t (idA isC a)) reflT))
            (subst ∣_∣ (sym (semWk-T' A A (idA isC a) (π t (idA isC a)))) z))
         (eq-var-iA isC a t)
         ◾ wk-iA isC a A t)
        ⁻¹)
       )
       (ap ∣_∣
       (sym
        (Eq2G _≡T_
         (semWk-T' (A +T A) (var (vS t) =h var v0)
          (idA isC a ,Σ π t (idA isC a))
          (reflT'
           (subst ∣_∣ (sym (semWk-T' A A (idA isC a) (π t (idA isC a))))
            (π t (idA isC a)))))
         (coeap2
         (semWk-T' (A +T A) (var (vS t) =h var v0) (idA isC a ,Σ π t (idA isC a))
           (reflT'
            (subst ∣_∣ (sym (semWk-T' A A (idA isC a) (π t (idA isC a))))
             (π t (idA isC a))))))
         (coeap2
         (semWk-T' (A +T A) (var (vS t) =h var v0) (idA isC a ,Σ π t (idA isC a))
           (reflT'
            (subst ∣_∣ (sym (semWk-T' A A (idA isC a) (π t (idA isC a))))
             (π t (idA isC a)))))))))
    
    ◾
    -- jusqu'ici tout marchait bien
    
  ap
    (λ z →
       coe z
       (reflT' (iA (ext isC t) a (A +T A +T (var (vS t) =h var v0)))))

    (
    uip



    (
      (
      (Eq2G (_≡T_)
      (sym
      (semWk-T' (A +T A) (var (vS t) =h var v0)
      (idA isC a ,Σ π t (idA isC a)) reflT))
      (ap
      (λ z →
      subst idfun
      (sym
      (semWk-T' (A +T A) (var (vS t) =h var v0)
      (idA isC a ,Σ π t (idA isC a)) reflT))
      (subst ∣_∣ (sym (semWk-T' A A (idA isC a) (π t (idA isC a)))) z))
      (eq-var-iA isC a t)
      ◾ wk-iA isC a A t)
      (ap
      (λ z →
      subst idfun
      (sym
      (semWk-T' (A +T A) (var (vS t) =h var v0)
      (idA isC a ,Σ π t (idA isC a)) reflT))
      (subst ∣_∣ (sym (semWk-T' A A (idA isC a) (π t (idA isC a)))) z))
      (eq-var-iA isC a t)
      ◾ wk-iA isC a A t)
      ⁻¹)
      )
    ◾
      (ap ∣_∣
      (sym
      (Eq2G _≡T_
      (semWk-T' (A +T A) (var (vS t) =h var v0)
      (idA isC a ,Σ π t (idA isC a))
      (reflT'
      (subst ∣_∣ (sym (semWk-T' A A (idA isC a) (π t (idA isC a))))
      (π t (idA isC a)))))
      (coeap2
      (semWk-T' (A +T A) (var (vS t) =h var v0) (idA isC a ,Σ π t (idA isC a))
      (reflT'
      (subst ∣_∣ (sym (semWk-T' A A (idA isC a) (π t (idA isC a))))
      (π t (idA isC a))))))
      (coeap2
      (semWk-T' (A +T A) (var (vS t) =h var v0) (idA isC a ,Σ π t (idA isC a))
      (reflT'
      (subst ∣_∣ (sym (semWk-T' A A (idA isC a) (π t (idA isC a))))
      (π t (idA isC a)))))))))
   )




   -- (ap2 _≡T_ (admit-eq-var ⁻¹)
   (ap2 _≡T_ (eq-var-iA (ext isC t) a (vS (vS t)) ⁻¹)
    ((ap
    (λ z →
    coe
    (ap (λ x₁ → x₁)
    (semWk-T' (A +T A) (var (vS t) =h var v0)
    (idA isC a ,Σ π t (idA isC a)) reflT
    ⁻¹))
    (coe
    (ap (λ x₁ → x₁) (semWk-T' A A (idA isC a) (π t (idA isC a)) ⁻¹))
    z))
    (eq-var-iA isC a t)
    ◾ wk-iA isC a A t)
    ⁻¹))
    )
    
    )
  
  {-
   
   ap
     (subst ∣_∣
      (sym
      (semWk-T' (var (vS t) =h var v0) (var (vS t) =h var v0) (idA isC a ,Σ π t (idA isC a))
        (reflT'
         (subst ∣_∣ (sym (semWk-T' A A (idA isC a) (π t (idA isC a))))
          (π t (idA isC a)))))))
   (
   coe-inv
   {p =
      (Eq2G (_≡T_)
      (sym
      (semWk-T' (A +T A) (var (vS t) =h var v0)
      (idA isC a ,Σ π t (idA isC a)) reflT))
      (ap
      (λ z →
      subst idfun
      (sym
      (semWk-T' (A +T A) (var (vS t) =h var v0)
      (idA isC a ,Σ π t (idA isC a)) reflT))
      (subst ∣_∣ (sym (semWk-T' A A (idA isC a) (π t (idA isC a)))) z))
      (eq-var-iA isC a t)
      ◾ wk-iA isC a A t)
      (ap
      (λ z →
      subst idfun
      (sym
      (semWk-T' (A +T A) (var (vS t) =h var v0)
      (idA isC a ,Σ π t (idA isC a)) reflT))
      (subst ∣_∣ (sym (semWk-T' A A (idA isC a) (π t (idA isC a)))) z))
      (eq-var-iA isC a t)
      ◾ wk-iA isC a A t))
   }
   (Refl2G _≡T_ reflT' (sym (semWk-T' (A +T A) (var (vS t) =h var v0)
        (idA isC a ,Σ π t (idA isC a)) reflT))
        {a = (subst ∣_∣ (sym (semWk-T' A A (idA isC a) (π t (idA isC a))))
           (π t (idA isC a)))}

          (
           ap
             (λ z →
                subst idfun
                (sym
                 (semWk-T' (A +T A) (var (vS t) =h var v0)
                  (idA isC a ,Σ π t (idA isC a)) reflT))
                (subst ∣_∣ (sym (semWk-T' A A (idA isC a) (π t (idA isC a)))) z))
             (eq-var-iA isC a t)
          ◾
          wk-iA isC a A t)
   )


   )
   ◾
   -- aplatissement
   -- {!
   coecoe
      (
       (Eq2G (_≡T_)
        (sym
         (semWk-T' (A +T A) (var (vS t) =h var v0)
          (idA isC a ,Σ π t (idA isC a)) reflT))
        (ap
         (λ z →
            subst idfun
            (sym
             (semWk-T' (A +T A) (var (vS t) =h var v0)
              (idA isC a ,Σ π t (idA isC a)) reflT))
            (subst ∣_∣ (sym (semWk-T' A A (idA isC a) (π t (idA isC a)))) z))
         (eq-var-iA isC a t)
         ◾ wk-iA isC a A t)
        (ap
         (λ z →
            subst idfun
            (sym
             (semWk-T' (A +T A) (var (vS t) =h var v0)
              (idA isC a ,Σ π t (idA isC a)) reflT))
            (subst ∣_∣ (sym (semWk-T' A A (idA isC a) (π t (idA isC a)))) z))
         (eq-var-iA isC a t)
         ◾ wk-iA isC a A t)
        ⁻¹)
       )
       (ap ∣_∣
       (sym
        (Eq2G _≡T_
         (semWk-T' (A +T A) (var (vS t) =h var v0)
          (idA isC a ,Σ π t (idA isC a))
          (reflT'
           (subst ∣_∣ (sym (semWk-T' A A (idA isC a) (π t (idA isC a))))
            (π t (idA isC a)))))
         (coeap2
         (semWk-T' (A +T A) (var (vS t) =h var v0) (idA isC a ,Σ π t (idA isC a))
           (reflT'
            (subst ∣_∣ (sym (semWk-T' A A (idA isC a) (π t (idA isC a))))
             (π t (idA isC a))))))
         (coeap2
         (semWk-T' (A +T A) (var (vS t) =h var v0) (idA isC a ,Σ π t (idA isC a))
           (reflT'
            (subst ∣_∣ (sym (semWk-T' A A (idA isC a) (π t (idA isC a))))
             (π t (idA isC a)))))))))

   -- !}
   -- -}
   
-- uip
{-
  ◾
  ap
    (λ z →
       coe z
       (reflT' (iA (ext isC t) a (A +T A +T (var (vS t) =h var v0)))))

  {!!}
  --  -}
{-
    (
    uip



    (
      (
      (Eq2G (_≡T_)
      (sym
      (semWk-T' (A +T A) (var (vS t) =h var v0)
      (idA isC a ,Σ π t (idA isC a)) reflT))
      (ap
      (λ z →
      subst idfun
      (sym
      (semWk-T' (A +T A) (var (vS t) =h var v0)
      (idA isC a ,Σ π t (idA isC a)) reflT))
      (subst ∣_∣ (sym (semWk-T' A A (idA isC a) (π t (idA isC a)))) z))
      (eq-var-iA isC a t)
      ◾ wk-iA isC a A t)
      (ap
      (λ z →
      subst idfun
      (sym
      (semWk-T' (A +T A) (var (vS t) =h var v0)
      (idA isC a ,Σ π t (idA isC a)) reflT))
      (subst ∣_∣ (sym (semWk-T' A A (idA isC a) (π t (idA isC a)))) z))
      (eq-var-iA isC a t)
      ◾ wk-iA isC a A t)
      ⁻¹)
      )
    ◾
      (ap ∣_∣
      (sym
      (Eq2G _≡T_
      (semWk-T' (A +T A) (var (vS t) =h var v0)
      (idA isC a ,Σ π t (idA isC a))
      (reflT'
      (subst ∣_∣ (sym (semWk-T' A A (idA isC a) (π t (idA isC a))))
      (π t (idA isC a)))))
      (coeap2
      (semWk-T' (A +T A) (var (vS t) =h var v0) (idA isC a ,Σ π t (idA isC a))
      (reflT'
      (subst ∣_∣ (sym (semWk-T' A A (idA isC a) (π t (idA isC a))))
      (π t (idA isC a))))))
      (coeap2
      (semWk-T' (A +T A) (var (vS t) =h var v0) (idA isC a ,Σ π t (idA isC a))
      (reflT'
      (subst ∣_∣ (sym (semWk-T' A A (idA isC a) (π t (idA isC a))))
      (π t (idA isC a)))))))))
   )




    (ap2 _≡T_
    ((ap
    (λ z →
    coe
    (ap (λ x₁ → x₁)
    (semWk-T' (A +T A) (var (vS t) =h var v0)
    (idA isC a ,Σ π t (idA isC a)) reflT
    ⁻¹))
    (coe
    (ap (λ x₁ → x₁) (semWk-T' A A (idA isC a) (π t (idA isC a)) ⁻¹))
    z))
    (eq-var-iA isC a t)
    ◾ wk-iA isC a A t)
    ⁻¹)
    ((ap
    (λ z →
    coe
    (ap (λ x₁ → x₁)
    (semWk-T' (A +T A) (var (vS t) =h var v0)
    (idA isC a ,Σ π t (idA isC a)) reflT
    ⁻¹))
    (coe
    (ap (λ x₁ → x₁) (semWk-T' A A (idA isC a) (π t (idA isC a)) ⁻¹))
    z))
    (eq-var-iA isC a t)
    ◾ wk-iA isC a A t)
    ⁻¹))
    )
    -- -}
  {- 
  
  ap
  (λ z → coe z (reflT' (iA (ext isC t) a (A +T A +T (var (vS t) =h var v0)))))
  (uip

      ((Eq2G (_≡T_)
       (sym
        (semWk-T' (A +T A) (var (vS t) =h var v0)
         (idA isC a ,Σ π t (idA isC a)) reflT))
       (ap
        (λ z →
           subst idfun
           (sym
            (semWk-T' (A +T A) (var (vS t) =h var v0)
             (idA isC a ,Σ π t (idA isC a)) reflT))
           (subst ∣_∣ (sym (semWk-T' A A (idA isC a) (π t (idA isC a)))) z))
        (eq-var-iA isC a t)
        ◾ wk-iA isC a A t)
       (ap
        (λ z →
           subst idfun
           (sym
            (semWk-T' (A +T A) (var (vS t) =h var v0)
             (idA isC a ,Σ π t (idA isC a)) reflT))
           (subst ∣_∣ (sym (semWk-T' A A (idA isC a) (π t (idA isC a)))) z))
        (eq-var-iA isC a t)
        ◾ wk-iA isC a A t)
       ⁻¹
       ◾
       ap ∣_∣
       (sym
        (Eq2G (_≡T_)
         (semWk-T' (A +T A) (var (vS t) =h var v0)
          (idA isC a ,Σ π t (idA isC a))
          (reflT'
           (subst ∣_∣ (sym (semWk-T' A A (idA isC a) (π t (idA isC a))))
            (π t (idA isC a)))))
         (coeap2
          (semWk-T (idA isC a ,Σ π t (idA isC a))
           (reflT'
            (subst ∣_∣ (sym (semWk-T' A A (idA isC a) (π t (idA isC a))))
             (π t (idA isC a))))))
         (coeap2
          (semWk-T (idA isC a ,Σ π t (idA isC a))
           (reflT'
            (subst ∣_∣ (sym (semWk-T' A A (idA isC a) (π t (idA isC a))))
             (π t (idA isC a))))))))))



      (ap2 _≡T_
      ((ap
      (λ z →
      coe
      (ap (λ x₁ → x₁)
      (semWk-T' (A +T A) (var (vS t) =h var v0)
      (idA isC a ,Σ π t (idA isC a)) reflT
      ⁻¹))
      (coe
      (ap (λ x₁ → x₁) (semWk-T' A A (idA isC a) (π t (idA isC a)) ⁻¹))
      z))
      (eq-var-iA isC a t)
      ◾ wk-iA isC a A t)
      ⁻¹)
      ((ap
      (λ z →
      coe
      (ap (λ x₁ → x₁)
      (semWk-T' (A +T A) (var (vS t) =h var v0)
      (idA isC a ,Σ π t (idA isC a)) reflT
      ⁻¹))
      (coe
      (ap (λ x₁ → x₁) (semWk-T' A A (idA isC a) (π t (idA isC a)) ⁻¹))
      z))
      (eq-var-iA isC a t)
      ◾ wk-iA isC a A t)
      ⁻¹))

   )

 
 -- -}

  

eq-var-iA (ext isC {A} t) a {.(B +T A +T (var (vS t) =h var v0))} (vS (vS {A = B} x))
  = 
  {-
  ************
  Ici je mets admit pour que ça aille plus vite
  ************
  vérifié post-fib
  -}
   admit-eq-var
   {-
  ap
    (λ z →
       coe
       (ap (λ x₁ → x₁)
        (semWk-T' (B +T A) (var (vS t) =h var v0)
         (idA isC a ,Σ π t (idA isC a)) reflT
         ⁻¹))
       (coe
        (ap (λ x₁ → x₁) (semWk-T' B A (idA isC a) (π t (idA isC a)) ⁻¹))
        z))
    (eq-var-iA isC a x)
  ◾
  wk-iA isC a B t
  --   -}

