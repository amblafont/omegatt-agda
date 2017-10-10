{-# OPTIONS --without-K --rewriting #-}

-- ici c'est pour l'égalité homotopique
module libhomot where

open import Agda.Primitive
open import lib


data _≡T_ {ℓ}{A : Set ℓ} (x : A) : A → Set ℓ where
  reflT : x ≡T x

-- version argument explicite. Malheureusement, je ne sais pas rendre
-- reflT explicite
reflT' : {l  : _}{A : Set l} (a : A) → a ≡T a
reflT' a = reflT

_◾T_ : ∀{ℓ}{A : Set ℓ}{x y z : A} → x ≡T y → y ≡T z → x ≡T z
reflT ◾T reflT = reflT

infixl 4 _◾T_

_⁻¹T : ∀{ℓ}{A : Set ℓ}{x y : A} → x ≡T y → y ≡T x
reflT ⁻¹T = reflT

infix 5 _⁻¹T

JT : ∀{ℓ ℓ'}{A : Set ℓ} {x : A} (P : {y : A} → x ≡T y → Set ℓ') → P reflT → {y : A} → (w : x ≡T y) → P w
JT P pr reflT = pr

coeT : ∀{ℓ}{A B : Set ℓ} → A ≡T B → A → B
coeT reflT a = a

-- il faut que B soit fibrant
apT : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'}(f : A → B){a₀ a₁ : A}(a₂ : a₀ ≡T a₁)
  → f a₀ ≡T f a₁
apT f reflT = reflT

substT : ∀{ℓ ℓ'}{A : Set ℓ}(P : A → Set ℓ'){x y : A}(p : x ≡T y) → P x → P y
substT P p = coeT (apT P p)

apdT : ∀{ℓ ℓ'}{A : Set ℓ}{B : A → Set ℓ'}(f : (x : A) → B x){a₀ a₁ : A}(a₂ : a₀ ≡T a₁)
  → coeT (apT B a₂) (f a₀) ≡T f a₁
apdT f reflT = reflT
-- aucune condition : se fait par elimination sur une égalité stricte
coe-cancel' : ∀{ℓ}{A B : Set ℓ} → (p : A ≡ B) → {a : A}{b : A} →
  (coe p a ≡T coe p b) → a ≡T b

coe-cancel' refl q = q

-- Déjà pour la définition, il faut que le type de
--    (coe p a) soit fibrant
-- Donc que B soit fibrant.
-- et comme on fait aussi par idnuction sur q, il faut que A soit fibrant aussi
ap-coe-cancel' : ∀{ℓ}{A B : Set ℓ} → (p : A ≡ B) → {a : A}{b : A} →
  (q : coe p a ≡T coe p b) → apT (λ x → coe p x) (coe-cancel' p q) ≡T q

ap-coe-cancel' refl reflT = reflT

{-
-- cohérence pour semSb-iA
coh-degueu2T : {A : Set} {P : A → Set}
    -- P joue le roel de A[σ]
   -- B joue le role de Δ
   -- Q le role de A 
   {B : Set} {Q : B → Set}
   -- x[σ]
   (fx : (a : A) → P a)
-- y[σ]
    (fy : (a : A) → P a)
    -- x
    (gx : (b : B) → Q b)
    -- y
    (gy : (b : B) → Q b)
    (σ : A → B)
    {id-B : B}
    {id-A : A}
    -- iA A
    {i-A : P id-A}
    {i-B : Q id-B}
    (eixQ : gx id-B ≡ i-B)
    (eiyQ : gy id-B ≡ i-B)
    -- (eixP : fx id-B ≡ i-A)
    -- (eiyP : fy id-B ≡ i-A)
    -- subst-idA
    (s-idA : σ id-A ≡ id-B)
    -- semSb-T idA
    (sb-T : P id-A ≡ Q (σ id-A) )
    (sb-tm-x : subst idfun (sb-T) (fx id-A) ≡ gx (σ id-A))
    (sb-tm-y : subst idfun (sb-T) (fy id-A) ≡ gy (σ id-A))
    -- semSb-iA
    (sb-iA : subst Q s-idA (subst idfun sb-T i-A) ≡ i-B)
    →
  coe (ap (λ v₁ → gx v₁ ≡ gy v₁) s-idA)
  (coe
    (ap (λ x₁ → x₁)
      (Eq2G _≡T_ sb-T sb-tm-x
        sb-tm-y))

   (coe
      (ap2 _≡T_
        (coe2r sb-T sb-tm-x ◾
        )
   )

    (coe2r sb-T sb-tm-x ◾
  ap (coe (ap (λ x₁ → x₁) (sb-T ⁻¹)))
  (coe2r s-idA
   (apd gx s-idA)
   ◾
   ap (coe (ap Q (s-idA ⁻¹)))
   eixQ)
  ◾
  coe2r sb-T
  (coe2r s-idA sb-iA)
  ⁻¹
  ◾
  (coe2r sb-T sb-tm-y ◾
   ap (coe (ap (λ x₁ → x₁) (sb-T ⁻¹)))
   (coe2r s-idA
    (apd gy s-idA)
    ◾
    ap (coe (ap Q (s-idA ⁻¹)))
    eiyQ)
   ◾
   coe2r sb-T
   (coe2r s-idA sb-iA)
   ⁻¹)
  ⁻¹))
  ≡ (eixQ ◾ eiyQ  ⁻¹)

-- cohérence pour semSb-iA
coh-degueu2T {A} {P} {B} {Q} fx fy gx gy σ {id-A = id-A} {i-A} eixQ eiyQ refl sb-T sb-tm-x sb-tm-y refl
  =
    
   ap2 {A = gx (σ id-A) ≡ coe (ap idfun sb-T) i-A}
     (λ z z' →
        coe (ap (λ x₁ → x₁) (EqEq sb-T sb-tm-x sb-tm-y))
        (coe2r sb-T sb-tm-x ◾ ap (coe (ap (λ x₁ → x₁) (sb-T ⁻¹))) z ◾
         coe2r sb-T refl ⁻¹
         ◾
         (coe2r sb-T sb-tm-y ◾ ap (coe (ap (λ x₁ → x₁) (sb-T ⁻¹))) z' ◾
          coe2r sb-T refl ⁻¹)
         ⁻¹))
         (◾lid _ ◾ apid _) (◾lid _ ◾ apid _)
  ◾
  
    coh-degueu2-auxT sb-T sb-tm-x sb-tm-y eiyQ eixQ
  
  where
  coh-degueu2-auxT : 
      {Pid-A : Set}
      {Qid-B : Set}
      (sb-T : Pid-A ≡ Qid-B )
      {i-A     : Pid-A}
      {xxf : Pid-A}
      {yyf : Pid-A}
      {xx : Qid-B}
      {yy : Qid-B}
      (sb-tm-x : subst idfun (sb-T) xxf ≡ xx )
      (sb-tm-y : subst idfun (sb-T) yyf ≡ yy )
      (eiyQ    : yy ≡ coe (ap idfun sb-T) i-A)
      (eixQ    : xx ≡ coe (ap idfun sb-T) i-A)
      -- semSb-iA
    →  coe (ap (λ x₁ → x₁) (EqEq sb-T sb-tm-x sb-tm-y))
    (coe2r sb-T sb-tm-x ◾ ap (coe (ap (λ x₁ → x₁) (sb-T ⁻¹))) eixQ ◾
    coe2r sb-T refl ⁻¹
    ◾
    (coe2r sb-T sb-tm-y ◾ ap (coe (ap (λ x₁ → x₁) (sb-T ⁻¹))) eiyQ ◾
    coe2r sb-T refl ⁻¹)
    ⁻¹)
    ≡ (eixQ ◾ eiyQ ⁻¹)
  coh-degueu2-auxT refl refl refl refl refl = refl

-}

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
 
  -- J (λ {y} e → (i-A : _) →
  -- reflT ≡
  -- coe
  -- (Eq2G _≡T_ (e ◾ refl) (coh4 e refl i-A ◾ refl)
  -- (coh4 e refl i-A ◾ refl))
  -- reflT
  -- )
