{-# OPTIONS --without-K  --no-termination-check #-}
-- Un ensemble globulaire induit un modèle pour les contextes de niveau 0 (Ambroise))
-- mais ici on se restreint aux contextes PS (on n'a pas besoin de +)

module GlobularModel where

open import BasicSyntax
open import IdentityContextMorphisms
open import Data.Unit renaming (_≤_ to le_unit)
open import Data.Product renaming (_,_ to _,,_)
open import Coinduction
open import Relation.Binary.PropositionalEquality hiding ([_])
open import GroupoidStructure
open import Data.Nat
open import Data.Empty

infix 4 _≤S_ _≤T_ _≤tm_ _≤C_

-- open import Data.Nat.Properties
-- open import Relation.Binary.Lattice

open import GlobularTypes

-- depth
d-T : {Γ : Con} → (A : Ty Γ) → ℕ
d-tm : {Γ : Con} → {A : Ty Γ} → (t : Tm A) → ℕ
d-S : {Γ Δ : Con} → (σ : Γ ⇒ Δ) → ℕ

d-T * = 0
d-T  (_=h_ {A} a b) = (d-T A) ⊔ d-tm a ⊔ d-tm b

d-S • = 0
d-S (σ , a) = (d-S σ) ⊔ (d-tm a)

d-tm (var x) = 0
d-tm (coh x δ A) = (suc (d-T A) ) ⊔ (d-S δ)


d-C : (Γ : Con) → ℕ
d-C ε = 0
d-C (Γ , A) = d-C Γ ⊔ d-T A

-- less than (depth)
_≤T_ : {Γ : Con} → (A : Ty Γ) → ℕ → Set
_≤tm_ : {Γ : Con} → {A : Ty Γ} → (t : Tm A) → ℕ → Set
_≤S_ : {Γ Δ : Con} → (σ : Γ ⇒ Δ) → ℕ → Set

* ≤T n = ⊤
(_=h_ {A} a b) ≤T n = (A ≤T n) × (a ≤tm n) × (b ≤tm n) 

var x ≤tm n = ⊤
coh x δ A ≤tm zero = ⊥
coh x δ A ≤tm suc n = (δ ≤S suc n) × (A ≤T n)


• ≤S n = ⊤
σ , a ≤S n = (σ ≤S n) × (a ≤tm n)

_≤C_ : Con → ℕ → Set

ε ≤C n = ⊤
Γ , A ≤C n = (Γ ≤C n) × A ≤T n

postulate
  ≤T-hset : {Γ : Con} → {A : Ty Γ} → {n : ℕ} (e e' : A ≤T n) → e ≡ e'
  ≤tm-hset : {Γ : Con} → {A : Ty Γ} → {t : Tm A}  {n : ℕ} (e e' : t ≤tm n) → e ≡ e'

-- ≤S-hset : {Γ Δ : Con} → (σ : Γ ⇒ Δ) → (n : ℕ) (e e' : t ≤σ n) → e ≡ e'

coh≤ : {Γ : Con} {A B : Ty Γ} {t : Tm A}  {n : ℕ} {u : Tm B} (e : t ≅ u)
  (dt : t ≤tm n) → u ≤tm n

coh≤ (refl b) dt = dt


-- il semble que ce sens n'est pas nécessaire.
-- il faut plutôt l'autre : cf +tm≤
{-
≤+tm : {Γ : Con} {A : Ty Γ}  {t : Tm A} {n : ℕ} (dt : t ≤tm n) (B : Ty Γ) → t +tm B ≤tm n
≤+T  : {Γ : Con} {A : Ty Γ} {n : ℕ} (dA : A ≤T n) (B : Ty Γ) → A +T B ≤T n
≤+S  : {Γ Δ : Con} {σ : Γ ⇒ Δ} {n : ℕ} (dσ : σ ≤S n) (B : Ty Γ) → (σ +S B) ≤S n

≤+tm {t = var x} dt B = tt
≤+tm {t = coh x δ A} {zero} () B
≤+tm {t = coh x δ A} {suc n} (dδ ,, dA) B = coh≤ ((cohOp (sym [+S]T)) -¹) (≤+S dδ B ,, dA)
--coh≤ ( (cohOp {sym [+S]T})-¹) {!!}

≤+S {σ = •} dσ B = tt
≤+S {Γ} {σ = σ , a} (dσ ,, da) B = ≤+S dσ B ,, coh≤ {Γ , B} {t = a +tm B} (cohOp (sym [+S]T) -¹) (≤+tm da  B)

≤+T {A = *} dA B = tt
≤+T {A = a =h b} (dA ,, da ,, db) B = ≤+T dA B ,, ≤+tm da B ,, ≤+tm db B
-}
 -- coh≤ {Γ , B} {t = a +tm B} (cohOp (sym [+S]T) -¹) (≤+tm da  B)
-- (cohOp (sym [+S]T) -¹)
-- (≤+tm da  B)
-- (≤+tm da  B)
-- (≤+tm da B)(a +tm B)


-- ce sens la est nécessaire pour définir π vS
+tm≤ : {Γ : Con} {A : Ty Γ}  {t : Tm A} {n : ℕ}  (B : Ty Γ) → t +tm B ≤tm n → t ≤tm n
-- celui la surtout
+T≤  : {Γ : Con} {A : Ty Γ} {n : ℕ}  (B : Ty Γ) → A +T B ≤T n → A ≤T n
+S≤  : {Γ Δ : Con} {σ : Γ ⇒ Δ} {n : ℕ}  (B : Ty Γ) → (σ +S B) ≤S n →  σ ≤S n

+tm≤ {t = var x} B dt = tt
+tm≤ {t = coh x δ A} {n} B dt with coh≤ (cohOp (sym [+S]T)) dt
+tm≤ {_} {_} {coh x δ A} {zero} B dt | dt' = dt'
+tm≤ {_} {_} {coh x δ A} {suc n} B dt | (dδ ,, dA) = +S≤ B dδ  ,, dA

+T≤ {A = *} B dA = tt
+T≤ {A = a =h b} B (dA ,, da ,, db)  =  +T≤ B dA ,, +tm≤ B da  ,, +tm≤ B db

+S≤ {σ = •} B dσ = tt
+S≤ {Γ} {σ = _,_ {Δ = Δ} σ {A} a} B (dσ ,, da) = +S≤ B dσ ,,
  +tm≤ {t = a} B (coh≤ {t = wk-tm+ B (a +tm B)} {u = a +tm B}
  (cohOp {Γ , B} {a = a +tm B} (([+S]T {Γ} {Δ}  {A} {B} {σ} )) ) da)

⟦_⟧C : {Γ : Con} (dΓ : Γ ≤C 0) (G : Glob)  →  Set

⟦_⟧T : {G : Glob} {Γ : Con} {A : Ty Γ} {dΓ : Γ ≤C 0} (dA : A ≤T 0) →
  ⟦ dΓ ⟧C G → Glob


π : {G : Glob} {Γ : Con} {A : Ty Γ} {dΓ : Γ ≤C 0} {dA : A ≤T 0}
  (v : Var A)  (γ : ⟦ dΓ ⟧C G) → ∣  ⟦ dA ⟧T γ ∣

⟦_⟧tm : {G : Glob} {Γ : Con} {A : Ty Γ} {dΓ : Γ ≤C 0} 
  {t : Tm A} (dt : t ≤tm 0) {dA : A ≤T 0} (γ : ⟦ dΓ ⟧C G)  → ∣ ⟦ dA ⟧T γ ∣



-- peut etre on peut s'en inspirer pour coq : il faut d'abord définir l'interprétation
-- des contextes en supposant donné l'interprétations des types

⟦_⟧C {ε} dΓ G = ⊤
⟦_⟧C {Γ , A} (dΓ ,, dA) G = Σ (⟦ dΓ ⟧C G) (λ x → ∣ ⟦ dA ⟧T x ∣)

G-semWk-T : {G : Glob} {Γ : Con} {A B : Ty Γ} {dΓ : Γ ≤C 0} {dA : A ≤T 0}
  -- (dB : B ≤T 0) 
  (dB' : B +T A ≤T 0) (γ :  ⟦_⟧C {Γ , A} (dΓ ,, dA) G) →
    -- ⟦ dB' ⟧T γ ≡ ⟦ dB ⟧T (proj₁ γ)
    ⟦ dB' ⟧T γ ≡ ⟦ +T≤ A dB' ⟧T (proj₁ γ)

-- dB' est redondnas avec dB mais j'espère que l'astuce permet d'éviter des pbs de cohérence
-- TODO essayre de remplacer dB par le truc correspondant +T≤ dB'
-- car la je suis bloqué pour définir sur les variables
G-semWk-tm : {G : Glob} {Γ : Con} {A B : Ty Γ} {t : Tm B} {dΓ : Γ ≤C 0} {dA : A ≤T 0}
  -- (dB : B ≤T 0) 
  (dB' : B +T A ≤T 0)
  -- (dt : t ≤tm 0)
  (dt' : t +tm A ≤tm 0)
  (γ : ⟦_⟧C {Γ , A} (dΓ ,, dA) G) →
  -- subst ∣_∣ (  (G-semWk-T dB dB' γ)) (⟦ dt' ⟧tm γ) ≡  ⟦ dt ⟧tm (proj₁ γ)
  subst ∣_∣ (  (G-semWk-T  dB' γ)) (⟦ dt' ⟧tm γ) ≡  ⟦ +tm≤ A dt' ⟧tm (proj₁ γ)


⟦_⟧T {G} {Γ} {*} {dΓ} dA γ = G
⟦_⟧T {G} {Γ} {_=h_ {A} a b} {dΓ} (dA ,, da ,, db) γ =
  ♭ (hom (⟦ dA ⟧T γ) (⟦ da ⟧tm γ) (⟦ db ⟧tm γ))

-- dB' est redondnas avec dB mais j'espère que l'astuce permet d'éviter des pbs de cohérence

-- G-semWk-T {B = *} dB dB' γ = refl
G-semWk-T {B = *} dB' γ = refl
-- G-semWk-T {A = A} {_=h_ {B} a b} (dB ,, da ,, db) (dB' ,, da' ,, db') γ
--   = EqHom  (G-semWk-T dB dB' γ) (G-semWk-tm dB dB' da da' γ )
--   (G-semWk-tm dB dB' db db' γ )
G-semWk-T {G} {Γ} {A}  {_=h_ {B} a b} {dΓ} {dA} (dB' ,, da' ,, db') γ
  = EqHom
    --{⟦ dB' ⟧T γ} {⟦ +T≤ A dB' ⟧T (proj₁ γ)}
   (G-semWk-T {G} {Γ} {A} {B} {dΓ} {dA} dB' γ)
  -- { ⟦ da' ⟧tm γ } { ⟦ db' ⟧tm γ }
  -- { (⟦ +tm≤ {t = a} A da' ⟧tm   ((proj₁ γ)))} {(⟦ +tm≤ {t = b} A db' ⟧tm (proj₁ γ))}
  (G-semWk-tm {t = a} {dΓ} {dA} dB' da' γ)
  (G-semWk-tm {t = b} {dΓ} {dA} dB'  db' γ) 




π {G} {.(Γ , A)} {.(A +T A)} {dΓ ,, dA} {dA'} (v0 {Γ} {A}) γ =
  subst ∣_∣   (sym (G-semWk-T {G} {Γ} {A}  {A} {dΓ} {dA}
  --   dA
  -- dA'  γ)) (proj₂ γ)
  dA'  γ)) (subst (λ x → ∣ ⟦ x ⟧T (proj₁ γ) ∣ ) (≤T-hset dA (+T≤ A dA')) (proj₂ γ))
  -- (subst (λ x → {!!}) {!!} {!!})
π {G} {.(Γ , B)} {.(A +T B)} {dΓ ,, dB} {dA'} (vS {Γ} {A} {B} v) γ =
  subst ∣_∣   (sym (G-semWk-T {G} {Γ} {B}  {A} {dΓ} {dB}
    -- (+T≤ B dA')
    dA'  γ))
  (π {G} {Γ} {A} {dΓ} {+T≤ B dA'} v (proj₁ γ))


⟦_⟧tm {G} {Γ} {A} {dΓ}  {var x}  dt {dA} γ = π x γ
⟦_⟧tm {G} {Γ} {.(A [ δ ]T)} {dΓ} {coh x δ A} () {dA} γ


G-semWk-tm {t = var x} dB' dt' γ rewrite (G-semWk-T dB' γ) = refl
G-semWk-tm {t = coh x δ A} dB' dt' γ with coh≤ (cohOp (sym [+S]T)) dt'
G-semWk-tm {_} {_} {_} {_} {coh x δ A} dB' dt' γ | ()

_[_]d-T : {Γ Δ : Con} {A : Ty Δ} (dA : A ≤T 0)
    {δ : Γ ⇒ Δ} (dδ : δ ≤S 0) → A [ δ ]T ≤T 0

_[_]d-V : {Γ Δ : Con} {A : Ty Δ} (t : Var A) 
  {δ : Γ ⇒ Δ} (dδ : δ ≤S 0)  → t [ δ ]V ≤tm 0

_[_]d-tm : {Γ Δ : Con} {A : Ty Δ} {t : Tm A} (dt : t ≤tm 0)
  {δ : Γ ⇒ Δ} (dδ : δ ≤S 0)  → t [ δ ]tm ≤tm 0


_[_]d-V v0 {δ , a} (dδ ,, da) = coh≤ ((cohOp +T[,]T) -¹) da
_[_]d-V (vS x) {δ , a} (dδ ,, da) = coh≤ ((cohOp +T[,]T) -¹) (x [ dδ ]d-V)


_[_]d-tm {t = var x} dt dδ = x [ dδ ]d-V
-- x [ dδ ]d-V
_[_]d-tm {t = coh x δ A} () dδ

_[_]d-T {A = *} dA dδ = tt
_[_]d-T {A = a =h b} (dA ,, da ,, db) dδ =  dA [ dδ ]d-T ,, da [ dδ ]d-tm ,, db [ dδ ]d-tm
  

⟦_⟧S : {G : Glob} {Γ Δ : Con} {σ : Γ ⇒ Δ} (dσ : σ ≤S 0) { dΓ : Γ ≤C 0 } { dΔ  : Δ ≤C 0}
  → ⟦ dΓ ⟧C G → ⟦ dΔ ⟧C G

G-semSb-T : {G : Glob} {Γ Δ : Con} {A : Ty Δ} {δ : Γ ⇒ Δ} {dΓ : Γ ≤C 0} {dΔ : Δ ≤C 0}
   (dA : A ≤T 0) (dδ : δ ≤S 0) (γ : ⟦ dΓ ⟧C G) → ⟦ dA [ dδ ]d-T ⟧T γ ≡ ⟦ dA ⟧T (⟦ dδ ⟧S {dΓ} {dΔ} γ)

G-semSb-tm : {G : Glob} {Γ Δ : Con} {A : Ty Δ} {dΓ : Γ ≤C 0} {dΔ : Δ ≤C 0}
   {a : Tm A}{δ : Γ ⇒ Δ}
  (da : a ≤tm 0) (dδ : δ ≤S 0) {dA : A ≤T 0}  (γ : ⟦ dΓ ⟧C G) →
    subst ∣_∣ (G-semSb-T dA dδ γ) (⟦ da [ dδ ]d-tm ⟧tm γ) ≡ ⟦_⟧tm {dΓ = dΔ} da {dA} (⟦ dδ ⟧S γ)

G-semSb-V : {G : Glob} {Γ Δ : Con} {A : Ty Δ} {dΓ : Γ ≤C 0} {dΔ : Δ ≤C 0}
  (x : Var A){δ : Γ ⇒ Δ}
   (dδ : δ ≤S 0) {dA : A ≤T 0}  (γ : ⟦ dΓ ⟧C G) → 
    subst ∣_∣ (G-semSb-T {dΔ = dΔ} dA dδ γ) (⟦ x [ dδ ]d-V ⟧tm γ) ≡ π x (⟦ dδ ⟧S γ)

G-semSb-V' : {G : Glob} {Γ Δ : Con} {A : Ty Δ} {dΓ : Γ ≤C 0} {dΔ : Δ ≤C 0}
  (x : Var A){δ : Γ ⇒ Δ}
  (dδ : δ ≤S 0) {dA : A ≤T 0}  (γ : ⟦ dΓ ⟧C G) → 
  subst ∣_∣ (G-semSb-T {dΔ = dΔ} dA dδ γ) (⟦ x [ dδ ]d-V ⟧tm γ) ≡ π x (⟦ dδ ⟧S γ)
-- G-semSb-S   : ∀ {Γ Δ Θ}(γ : ⟦ Γ ⟧C)(δ : Γ ⇒ Δ)
-- (θ : Δ ⇒ Θ) → ⟦ θ ⊚ δ ⟧S γ ≡ 
-- ⟦ θ ⟧S (⟦ δ ⟧S γ)


⟦_⟧S {σ = •} dσ γ = tt
⟦_⟧S {σ = σ , a} (dσ ,, da) {dΓ} {dΔ ,, dA} γ = (⟦ dσ ⟧S {dΓ} {dΔ} γ) ,,
  subst ∣_∣ (G-semSb-T dA dσ γ) (⟦_⟧tm {dΓ = dΓ} da {dA = dA [ dσ ]d-T} γ)

G-semSb-T {A = *} dA dδ γ = refl
G-semSb-T {A = a =h b} (dA ,, da ,, db) dδ γ = EqHom (G-semSb-T dA dδ γ)
  (G-semSb-tm da dδ γ)(G-semSb-tm db dδ γ)

infix 4 _G-≅_

data _G-≅_ {G : Glob} {Γ : Con} {A : Ty Γ} {dΓ : Γ ≤C 0} {γ : ⟦ dΓ ⟧C G} {dA : A ≤T 0 }   :
  {B : Ty Γ} {dB : B ≤T 0} → ∣ ⟦ dA ⟧T γ ∣ → ∣ ⟦ dB ⟧T γ ∣  →  Set where
  G-refl : (st : ∣ ⟦ dA ⟧T γ ∣ ) → _G-≅_ {dA = dA} {A} {dA} st st
    
-- ce n'était pas dans Semantics !!!!
-- le dA ou le dB est redondant : il faut enlever l'un des deux. A voir selon l'utilisation
G-coh≤ : {G : Glob} {Γ : Con} {A B : Ty Γ} {t : Tm A}  {u : Tm B} (e : t ≅ u)
  (dB : B ≤T 0) (dA : A ≤T 0)
  (dt : t ≤tm 0) {dΓ : Γ ≤C 0} (γ : ⟦ dΓ ⟧C G  ) →
  _G-≅_  {dA = dA} {dB = dB} (⟦ dt ⟧tm {dA = dA} γ)  (⟦ coh≤ {Γ} {A} {B} {n = 0}  e dt ⟧tm {dA = dB} γ)

G-coh≤ {Γ = Γ} {A} {.A} (refl b) dB dA dt {dΓ} γ rewrite ≤T-hset dA dB = G-refl (⟦ dt ⟧tm γ)
-- {!⟦ dt ⟧tm {dA = dA} γ!}
-- !⟦ coh≤ {Γ} {A} {B} {n = 0}  e dt ⟧tm {dA = dB} γ!
--         ∣ ⟦ dB ⟧T γ ∣
-- !⟦ dt ⟧tm {dA = dA} γ!
--         ∣ ⟦ dA ⟧T γ ∣



-- le but est
--  subst ∣_∣ (G-semSb-T dA dδ γ) (⟦ x [ dδ ]d-V ⟧tm γ) ≡
--    π x (⟦ dδ ⟧S γ)


-- G-semSb-T dA dδ γ :
--       ⟦ dA [ dδ ]d-T ⟧T γ ≡ ⟦ dA ⟧T (⟦ dδ ⟧S γ)

--  ⟦ x [ dδ ]d-V ⟧tm γ :
--       ∣ ⟦ dA [ dδ ]d-T ⟧T γ ∣

--    π x (⟦ dδ ⟧S γ) :
--       ∣ ⟦ dA ⟧T (⟦ dδ ⟧S γ) ∣




-- G-semSb-V x dδ {dA} γ = {!!}

G-semSb-V-helper0 : {G : Glob} {Γ Δ : Con} {A : Ty Δ} {dΓ : Γ ≤C 0} {dΔ : Δ ≤C 0}
  {δ : Γ ⇒ Δ}
  (a : Tm (A [ δ ]T))
   (da  : a ≤tm 0)
   (dA' : A +T A ≤T 0)
  (dδ : δ ≤S 0)
  {dA : A ≤T 0}
  (γ : ⟦ dΓ ⟧C G)
  ( e4  : dA ≡ +T≤ A dA')
 ( e5  : a ≅ (a ⟦ +T[,]T ⟫))
 ( e1  : ⟦ dA [ dδ ]d-T ⟧T γ ≡ ⟦ dA ⟧T (⟦ dδ ⟧S γ))
 ( e3  : ⟦ dA' ⟧T (⟦ dδ ⟧S γ ,, subst ∣_∣ e1 (⟦ da ⟧tm γ)) ≡ ( ⟦ +T≤ A dA' ⟧T (⟦ dδ ⟧S {dΔ = dΔ} γ)))
 ( e2  : ⟦ dA' [ dδ ,, da ]d-T ⟧T γ ≡ ( ⟦ dA' ⟧T (⟦ dδ ⟧S γ ,, subst ∣_∣ e1 (⟦ da ⟧tm γ))))
   →
  subst ∣_∣ e2 (⟦ coh≤ e5 da ⟧tm γ) ≡
  subst ∣_∣ (sym e3)
   (subst (λ x → ∣ ⟦ x ⟧T (⟦ dδ ⟧S {dΔ = dΔ} γ) ∣) e4
  (subst ∣_∣ e1 (⟦ da ⟧tm γ)))


G-semSb-V-helper0 a da dA' dδ γ refl e2 e3 e4 e5 rewrite subst-p2 (⟦ da ⟧tm γ) (sym e4) e3 with trans e3 (sym e4)
...    | e7 = {!!}

-- e2 e3 e4 e5 = {!!}

G-semSb-V' {dΓ = dΔ} {dΓ ,, dA} (v0 {A = A}) {δ , a} (dδ ,, da) {dA'} γ
   with  (≤T-hset dA (+T≤ _ dA'))
...   | refl = g dA dA' da
   where
   g : {A : Ty _} (dA : A ≤T 0) (dA' : A +T A ≤T 0) {a : Tm (A [ δ ]T)}
     (da : a ≤tm 0) → subst ∣_∣ (G-semSb-T dA' (dδ ,, da) γ) (⟦ coh≤ (cohOp +T[,]T -¹) da ⟧tm γ)
      ≡ subst ∣_∣ (sym (G-semWk-T {dΓ = dΓ} dA' (⟦ dδ ⟧S γ ,,
      subst ∣_∣ (G-semSb-T (+T≤ _ dA') dδ γ) (⟦ da ⟧tm γ))))
      (subst ∣_∣ (G-semSb-T (+T≤ _ dA') dδ γ) (⟦ da ⟧tm γ))
   g {*} dA dA'' {a₁} da₁ = refl
   g {a₁ =h b} dA dA'' {a₂} da₁ = {!!}

G-semSb-V' {dΔ = dΓ ,, dB} (vS {B = B} x) {δ , a} (dδ ,, da) {dA} γ 
-- subt imbriqué de ⟦ x [ dδ ]d-V ⟧tm γ
   rewrite sym (G-semSb-V' {dΔ = dΓ} x dδ {dA = +T≤ B dA} γ) = {!!}

-- subst-cancel : ∀ {A B}  (a : A) (b : B) {A : Set a} → subst (trans (sym q) p) a ≡ b →
--            subst p e1 a ≡ subst q e2 b

-- ce ne sont que des subst imbriqué de da.
G-semSb-V {dΓ = dΔ} {dΓ ,, dA} v0 {δ , a} (dδ ,, da) {dA'} γ with  (≤T-hset dA (+T≤ _ dA'))
-- | (G-semSb-T {dΔ = dΓ} (+T≤ _ dA') dδ γ)
...   | refl = g
   where
   g : subst ∣_∣ (G-semSb-T dA' (dδ ,, da) γ) (⟦ coh≤ (cohOp +T[,]T -¹) da ⟧tm γ)
      ≡ subst ∣_∣ (sym (G-semWk-T {dΓ = dΓ} dA' (⟦ dδ ⟧S γ ,,
      subst ∣_∣ (G-semSb-T (+T≤ _ dA') dδ γ) (⟦ da ⟧tm γ))))
      (subst ∣_∣ (G-semSb-T (+T≤ _ dA') dδ γ) (⟦ da ⟧tm γ))
   f : 
      (e   : ⟦ +T≤ _ dA' ⟧T (⟦ dδ ⟧S {dΔ = dΓ} γ) ≡
      ⟦ dA' ⟧T
      (⟦ dδ ⟧S γ ,, subst ∣_∣ (G-semSb-T (+T≤ _ dA') dδ γ) (⟦ da ⟧tm γ)))
      → subst ∣_∣ (G-semSb-T {dΔ = dΓ ,, dA} dA' (dδ ,, da) γ)
     (⟦ coh≤ (cohOp +T[,]T -¹) da ⟧tm γ) ≡ subst ∣_∣ (trans (G-semSb-T (+T≤ _ dA') dδ γ) e) (⟦ da ⟧tm γ)
   g with (sym
      (G-semWk-T {dΓ = dΓ} dA' (⟦ dδ ⟧S γ ,, subst ∣_∣ (G-semSb-T (+T≤ _ dA') dδ γ) (⟦ da ⟧tm γ))))
   ... | e rewrite subst-p2 (⟦ da ⟧tm γ) e (G-semSb-T (+T≤ _ dA') dδ γ) = {!(G-semSb-T (+T≤ _ dA') dδ γ)!}
      -- {!(⟦ coh≤ (cohOp +T[,]T -¹) da ⟧tm γ)!}
   f e with (G-semSb-T  {dΔ = dΓ ,, dA} dA' (dδ ,, da) γ)
   ...  | e2 with (trans (G-semSb-T (+T≤ _ dA') dδ γ) e)
   ...   | e3 with G-coh≤ (cohOp {a = a} (+T[,]T {δ = δ} {a}) -¹)
            (dA' [ dδ ,, da ]d-T )
            (  +T≤ _ dA' [ dδ ]d-T ) 
            da γ
   ...   | e4 = {!cohOp {a = a} (+T[,]T {δ = δ} {a})!}
   -- {!cohOp {a = a} (+T[,]T {δ = δ} {a})!}


-- Notons que coh≤ (cohOp +T[,]T -¹) da := subst _ e0 da 
--   avec e0 := ≅≡ (cohOp +T[,]T -¹)

--  p = (G-semSb-T dA' (dδ ,, da) γ) :
--     ⟦ dA' [ dδ ,, da ]d-T ⟧T γ ≡ ⟦ dA' ⟧T
--       (⟦ dδ ⟧S γ ,, subst ∣_∣ (G-semSb-T (proj₂ (_dΔ_1500 dΓ δ a dδ da γ e)) dδ γ)
--          (⟦ da ⟧tm γ))

-- q1 = (G-semSb-T (+T≤ _ dA') dδ γ) :
--     ⟦ +T≤ .A dA' [ dδ ]d-T ⟧T γ ≡ ⟦ +T≤ .A dA' ⟧T (⟦ dδ ⟧S γ)


-- (q2 = (sym (G-semWk-T {dΓ = dΓ} dA' (⟦ dδ ⟧S γ ,, subst ∣_∣ (G-semSb-T (+T≤ _ dA') dδ γ) (⟦ da ⟧tm γ)))))
-- : ⟦ +T≤ .A dA' ⟧T (⟦ dδ ⟧S γ) ≡
--     ⟦ dA' ⟧T (⟦ dδ ⟧S γ ,, subst ∣_∣ (G-semSb-T (+T≤ .A dA') dδ γ) (⟦ da ⟧tm γ)) 

-- Goal: subst ∣_∣ p (⟦ coh≤ (cohOp +T[,]T -¹) da ⟧tm γ)
--     ≡ subst ∣_∣ (trans q1 q2 ) (⟦ da ⟧tm γ)

-- ce qui est équivalent à

-- subst ∣_∣ (p @ !q2 @ !q1) (⟦ coh≤ (cohOp +T[,]T -¹) da ⟧tm γ)
--   = (⟦ da ⟧tm γ)
-- où !p :=  sym p et p @ q := trans p q

-- Etudions p @ !q2 : 


G-semSb-V {dΔ = dΓ ,, dB} (vS {B = B} x) {δ , a} (dδ ,, da) {dA} γ 
-- subt imbriqué de ⟦ x [ dδ ]d-V ⟧tm γ
 rewrite sym (G-semSb-V {dΔ = dΓ} x dδ {dA = +T≤ B dA} γ) = {!!}

  --{!G-semSb-V {dΔ = dΓ} x dδ {dA = +T≤ B dA} γ!}
  -- {!G-semSb-V {dΔ = dΓ} x dδ {dA = +T≤ B dA} γ!}
  --{!G-semSb-V {dΔ = dΓ} x dδ {dA = +T≤ B dA} γ!}


G-semSb-tm {dΔ = dΔ} {var x} da dδ {dA} γ = G-semSb-V x dδ {dA} γ

-- with (G-semSb-T {dΔ = dΔ} dA dδ γ)
--- ...   | e  = {!!}
G-semSb-tm {a = coh x δ A} () dδ γ
--
-- (⟦ dσ ⟧S {dΓ} {dΔ} γ)

{-
record ModelAt (Γ : Con) (n : ℕ) : Set₁ where
  field
    base-C   : Set
    ⟦_⟧T   : (A : Ty Γ) (dA : (d-T A) ≤ n) → base-C → Glob
    ⟦_⟧tm  : ∀{A dA} (t : Tm A) (dt : d-tm t ≤ n) (γ : base-C) → ∣ ⟦ A ⟧T dA γ ∣

open ModelAt public
    
{-
    ⟦_⟧C   : (Γ : Con) → (d-C Γ) ≤ 0 → Set
    ⟦_⟧T   : ∀{Γ}  {dΓ : (d-C Γ) ≤ 0} (A : Ty Γ) (dA : (d-T A) ≤ n) → ⟦ Γ ⟧C dΓ
      → Glob
    ⟦_⟧tm  : ∀{Γ dΓ A dA} (t : Tm A) (dt : d-tm t ≤ n) → (γ : ⟦ Γ ⟧C dΓ) 
      → ∣ ⟦ A ⟧T dA γ ∣
      -}
    -- ⟦_⟧S   : ∀{Γ Δ} {dΓ dΔ} → Γ ⇒ Δ → ⟦ Γ ⟧C dΓ → ⟦ Δ ⟧C dΔ
    {-
    ⟦_⟧tm  : ∀{Γ A} → Tm A → (γ : ⟦ Γ ⟧C) 
        → ∣ ⟦ A ⟧T γ ∣
    ⟦_⟧S   : ∀{Γ Δ} → Γ ⇒ Δ → ⟦ Γ ⟧C → ⟦ Δ ⟧C
    -}




-- le seul type dans le contexte vide est *
-- par contre il n'y a aucun terme
-- le dt n'est pas nécessaire mais puisqu'on se  restreint aux contextes ≤ 0,
-- on l'utilise
Gel-ε-tm : (G : Glob) {A : Ty ε} (t : Tm A) → d-tm t ≤ 0 → ∣ G ∣
Gel-ε-tm G (var ()) dt
Gel-ε-tm G (coh x δ A) dt with (d-S δ)
Gel-ε-tm G (coh x δ A) () | zero
Gel-ε-tm G (coh x δ A) () | suc m

-- le préfixe glob ici est troompeur mais bon..
Gel-ext-base : {Γ : Con} {n : ℕ} (m : ModelAt Γ n) (A : Ty Γ) (dA : d-T A ≤ n) → Set
--                                                          bug  ici que je ne sais pas résoudre
Gel-ext-base {Γ} {n} m A dA = Σ (base-C m) (λ x →  ∣ (⟦ m ⟧T A dA x) ∣) 

-- Gel-ext-T {Γ : Con}  {A : Ty Γ} {B : Ty (Γ, A)} (dA : d-T A ≤ n)
--   (d)
-- Goal: (A₁ : Ty (Γ , A)) →
-- d-T A₁ ≤ 0 → Gel-ext-base (Gel G Γ dΓ) A dA → Glob
-- ————————————————————————————————————————————————————————————
-- G   : Glob
-- dA  : d-T A ≤ 0
-- dΓ  : d-C Γ ≤ 0

-- ce truc devrait se déduire de la structure de lattice définie
-- sur nat dans data.nat.properties
postulate
  truc-lattice1 : {a b c : ℕ} → a ⊔ b ≤ c → a ≤ c × b ≤ c
  -- truc-lattice2 : {a b c : ℕ} → a ⊔ b ≤ c → b ≤ c

Gel : (G : Glob) (Γ : Con) (dΓ : d-C Γ ≤ 0) → ModelAt Γ 0
Gel G ε dΓ = record { base-C = ⊤ ; ⟦_⟧T = λ A dA x → G ;
  ⟦_⟧tm = λ t dt γ → Gel-ε-tm G  t dt  }

Gel G (Γ , A) dΓA with truc-lattice1 {d-C Γ} {d-T A}  dΓA
Gel G (Γ , A) dΓA | dΓ ,, dA =
  record { base-C = Gel-ext-base (Gel G Γ dΓ) A dA;
    ⟦_⟧T = {!!} ; ⟦_⟧tm = {!!} }
   --record { base-C = Σ (base-C (Gel G Γ {!!})) {!!} A; ⟦_⟧T = {!!} ; ⟦_⟧tm = {!!} }
  --{ base-C = ⊤ ; ⟦_⟧T = λ A dA x → G ; ⟦_⟧tm = λ t dt γ → Gel-ε-tm G  t dt }
  --Gel G (Γ , A) dΓ = record { base-C = {! !} ; ⟦_⟧T = {!!} ; ⟦_⟧tm = {!!} }
  --Gel G (Γ , A) dΓ = record { base-C = {!Σ (base-C) (λ γ  → ∣ ⟦ A ⟧T γ ∣) !} ; ⟦_⟧T = {!!} ; ⟦_⟧tm = {!!} }

-}
