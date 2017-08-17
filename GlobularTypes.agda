{-# OPTIONS --without-K  #-}
module GlobularTypes where

open import Data.Product
open import Coinduction
open import Relation.Binary.PropositionalEquality

record Glob : Set₁ where
  inductive
  constructor _∣∣_
  field
    ∣_∣   : Set
    hom  : ∣_∣ → ∣_∣ → ∞ Glob
open Glob public
Idω    : (A : Set) → Glob
Idω A  = A ∣∣ (λ a b → ♯ Idω (a ≡ b))

data _≅'_ {A : Glob} : {B : Glob} → ∣ A ∣ →  ∣ B ∣ → Set where
  refl : (a : ∣ A ∣) → _≅'_ {A} {A} a a


EqGlob : (A B : Glob) → (A ≡ B) → Σ (∣ A ∣ ≡ ∣ B ∣) (λ p → subst (λ x → x → x → ∞ Glob) p (hom A) ≡ hom B)
EqGlob .B B refl = refl , refl

EqHom : {A B : Glob} → (p : A ≡ B) → {x y : ∣ A ∣} → {m n : ∣ B ∣} → (subst ∣_∣ p x ≡ m) → (subst ∣_∣ p y ≡ n) → ♭ (hom A x y) ≡ ♭ (hom B m n)
EqHom {.B} {B} refl {.m} {.n} {m} {n} refl refl = refl

-- subst-p1 : {A B : Glob}(x : ∣ A ∣)(p q : A ≡ B) → subst ∣_∣ p x ≡ subst ∣_∣ q x
-- subst-p1 {.∣_∣ ∣∣ .hom} {∣_∣ ∣∣ hom} x refl refl = refl

subst-p2 : {A B C : Glob}(x : ∣ A ∣)(p : B ≡ C)(q : A ≡ B) → subst ∣_∣ p (subst ∣_∣ q x) ≡ subst ∣_∣ (trans q p) x
subst-p2 {.∣_∣ ∣∣ .hom} {∣_∣ ∣∣ hom} x refl refl = refl

data [_]_≅s_ {A : Glob}
         : (B : Glob) → ∣ A ∣ → ∣ B ∣ → Set where
  refl : (b : ∣ A ∣) → [ A ] b ≅s b

-- universe definition

module UniverseGS (U : Set)(El : U → Set) where

  record uGlob : Set where
    inductive
    field
      ∣_∣u   : U
      uhom : El ∣_∣u → El ∣_∣u → ∞ uGlob
  open uGlob


-- Globular Sets indexed by Types

Π : (A : Set)(B : A → Glob) → Glob
Π A B = 
  record 
  { ∣_∣  = (a : A) → ∣ B a ∣
  ; hom = λ f g → ♯ Π A (λ x → ♭ (hom (B x) (f x) (g x)))
  }

-- Globular Sets indexed by Globular Sets

-- looks good but we may require it covertible to some Glob
record _⇒Glob (A : Glob) : Set₁ where
  inductive
  field
    ∣_∣f   : ∣ A ∣ → Set
    homf : (a a' : ∣ A ∣) → ∣_∣f a → ∣_∣f a' → ♭ (hom A a a') ⇒Glob
open _⇒Glob

