-- {-# OPTIONS --without-K #-}


module TypeOmegaGroupoids (T : Set)  where

open import BasicSyntax
open import lib
open import libhomot
open import DefOmegaGroupoids
import Semantics2Eq


to-omega-groupoid : {{ fibT : Fib T }} → DefOmegaGroupoids.Semantic
to-omega-groupoid = record
                    { ⟦_⟧C = Semantics2Eq.⟦_⟧C T
                    ; ⟦_⟧T = Semantics2Eq.⟦_⟧T T
                    ; ⟦_⟧tm = Semantics2Eq.⟦_⟧tm T
                    ; ⟦_⟧S = Semantics2Eq.⟦_⟧S T
                    ; π = Semantics2Eq.π T
                      ; ⟦_⟧C-β1 = refl
                      ; ⟦_⟧C-β2 = refl
                      ; semSb-T = Semantics2Eq.semSb-T T
                      ; semSb-tm = Semantics2Eq.semSb-tm T
                      ; semSb-S = Semantics2Eq.semSb-S T
                      ; ⟦_⟧tm-β1 = refl
                      ; ⟦_⟧S-β1 = refl
                      ; ⟦_⟧S-β2 = refl
                      ; semWk-T = λ {Γ} {A} {B} → Semantics2Eq.semWk-T' T A B
                      ; semWk-S = Semantics2Eq.semWk-S T
                      ; semWk-tm =  λ {Γ} {A} {B} → Semantics2Eq.semWk-tm T {A = A} {B = B} 
                      ; π-β1 = λ {Γ} {A} → Semantics2Eq.π-β1 T {A = A}
                      ; π-β2 = λ {Γ} {A} → Semantics2Eq.π-β2 T {A = A}
                      ; ⟦coh⟧ = Semantics2Eq.⟦coh⟧ T 
                      }
