{-# OPTIONS --without-K --rewriting #-}

-- !!! PAS BESOIn DE REWRITE RULLES !!! DANS 2TT !!
-- ici c'est pour l'égalité homotopique
module libhomot where

open import Agda.Primitive
open import lib

postulate
  Fib : ∀ {i} → Set i → Set i
  instance ⊤-Fib : Fib ⊤
  instance Π-Fib : ∀ {i}{j}{A : Set i} {B : A → Set j} → ⦃ fibA : Fib A ⦄ → ⦃ fibB : {a : A} → Fib (B a) ⦄ → Fib ((a : A) → B a)

  instance Σ-Fib : ∀ {i}{j}{A : Set i}{B : A → Set j} → ⦃ fibA : Fib A ⦄ → ⦃ fibB : {a : A} → Fib (B a) ⦄ → Fib (Σ A B)

postulate
  _≡T_ : ∀{ℓ}{A : Set ℓ} (x : A) → A → Set ℓ
  reflT' : ∀{ℓ}{A : Set ℓ} (x : A) → x ≡T x

  JFib : ∀{ℓ ℓ'}{A : Set ℓ} ⦃ fibA : Fib A ⦄
     {x : A}
     (P : {y : A} → x ≡T y → Set ℓ') →
     ⦃ fibP : {y : A} {w : x ≡T y} → Fib (P w) ⦄ →
       P (reflT' _) → {y : A} → (w : x ≡T y) → P w

  -- JT : ∀{ℓ ℓ'}{A : Set ℓ} {x : A} (P : {y : A} → x ≡T y → Set ℓ') → P (reflT' _) → {y : A} → (w : x ≡T y) → P w
  -- βJT : ∀{ℓ ℓ'}{A : Set ℓ} {x : A} (P : {y : A} → x ≡T y → Set ℓ') → (x : P (reflT' _)) →  
  --     JT P x (reflT' _) ≡ x
  βJFib : ∀{ℓ ℓ'}{A : Set ℓ}⦃ fibA : Fib A ⦄ {x : A} (P : {y : A} → x ≡T y → Set ℓ')    ⦃ fibP : {y : A} {w : x ≡T y} → Fib (P w) ⦄ →  (x : P (reflT' _)) →  
      JFib P ⦃ fibP = fibP ⦄  x (reflT' _) ≡ x
  -- reflT : x ≡T x

-- {-# REWRITE βJT #-}
-- {-# REWRITE βJFib #-}

postulate
   instance eq-Fib : ∀{ℓ}{A : Set ℓ} ⦃ fibA : Fib A ⦄ {x y : A} → Fib (x ≡T y)


reflT : {l  : _}{A : Set l} {x : A} → x ≡T x
reflT {x = a} = reflT' a


-- version argument explicite. Malheureusement, je ne sais pas rendre
-- reflT explicite
-- reflT' : {l  : _}{A : Set l} (a : A) → a ≡T a
-- reflT' a = reflT

{-
_◾T_ : ∀{ℓ}{A : Set ℓ}{x y z : A} → x ≡T y → y ≡T z → x ≡T z
reflT ◾T reflT = reflT

infixl 4 _◾T_

_⁻¹T : ∀{ℓ}{A : Set ℓ}{x y : A} → x ≡T y → y ≡T x
reflT ⁻¹T = reflT

infix 5 _⁻¹T

-}

-- JT : ∀{ℓ ℓ'}{A : Set ℓ} {x : A} (P : {y : A} → x ≡T y → Set ℓ') → P reflT → {y : A} → (w : x ≡T y) → P w
-- JT P pr reflT = pr


-- aucune condition : se fait par elimination sur une égalité stricte
coe-cancel' : ∀{ℓ}{A B : Set ℓ} → (p : A ≡ B) → {a : A}{b : A} →
  (coe p a ≡T coe p b) → a ≡T b

coe-cancel' refl q = q




coh-degueu5 :
  {A : Set} {P : A → Set}
  -- P joue le roel de A[σ]
  -- B joue le role de Δ
  -- Q le role de A 
  {B : Set} {Q : B → Set}
  (σ : A → B)
  {id-B : B}
  {id-A : A}
  {i-A : P id-A}
  {i-B : Q id-B}
  (s-idA : σ id-A ≡ id-B)
  (sb-T : P id-A ≡ Q (σ id-A) )
  (sb-iA : coe (ap Q s-idA) (subst idfun sb-T i-A) ≡ i-B)

  →
  -- reflT'  (iA isCΓ a A)
  reflT  {x = i-B}
  ≡
  coe
  (Eq2G _≡T_
     (sb-T
      ◾
        ap Q s-idA )
  (coh4 sb-T (ap Q s-idA) i-A ◾ sb-iA)
   (coh4 sb-T (ap Q s-idA) i-A ◾ sb-iA)
  )
  (reflT {x = i-A})

coh-degueu5 {P = P} σ {id-A = id-A} {i-A} refl sb-T refl =
 J (λ {y} e → (i-A : P id-A) →
  reflT ≡
  coe
  (Eq2G _≡T_ (e ◾ refl) (coh4 e refl i-A ◾ refl)
  (coh4 e refl i-A ◾ refl))
  reflT
  )
  (λ e → refl)
  sb-T
  i-A
 
