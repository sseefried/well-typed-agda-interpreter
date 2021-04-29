{-# OPTIONS --without-K --safe --overlapping-instances #-}
module Interpreter where

open import Data.Char hiding (_≤_)
open import Data.Bool hiding (_≤_)
open import Data.Nat hiding (_≤_)
open import Data.Unit
import Data.Nat as N
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality as PropEq
open import Relation.Nullary
import Data.String as Str
open import Data.Nat.Show
import Data.List as List
open import Data.Empty

infix 3 _:::_,_
infix 2 _∈_
infix 1 _⊢_

data `Set : Set where
  `Nat  : `Set
  `Bool : `Set
  `_⇨_  : `Set → `Set → `Set
  `⊤    : `Set
  `_×_  : `Set → `Set → `Set
  `_+_  : `Set → `Set → `Set


data Var : Set where
  x' : Var
  y' : Var
  z' : Var

-- Inequality proofs on variables
data _≠_ : Var → Var → Set where
  x≠y : x' ≠ y'
  x≠z : x' ≠ z'
  y≠x : y' ≠ x'
  y≠z : y' ≠ z'
  z≠x : z' ≠ x'
  z≠y : z' ≠ y'


⟦_⟧ : `Set → Set
⟦ `Nat ⟧ = ℕ
⟦ `Bool ⟧ = Bool
⟦ (` t ⇨ s) ⟧ =  ⟦ t ⟧ → ⟦ s ⟧
⟦ `⊤ ⟧ = ⊤
⟦ (` t × s) ⟧ = ⟦ t ⟧ × ⟦ s ⟧
⟦ (` t + s) ⟧ = ⟦ t ⟧ ⊎ ⟦ s ⟧

data Γ : Set where
  ·         : Γ
  _:::_,_   : Var → `Set → Γ → Γ

data _∈_ :  Var → Γ → Set where
  H  : ∀ {x Δ t } → x ∈ x ::: t , Δ
  TH : ∀ {x y Δ t } → ⦃ prf : x ∈ Δ ⦄ → ⦃ neprf : x ≠ y ⦄ → x ∈ y ::: t , Δ

!Γ_[_] : ∀ {x} → (Δ : Γ) → x ∈ Δ → `Set
!Γ_[_] · ()
!Γ _ ::: t , Δ [ H ]     = t
!Γ _ ::: _ , Δ [ TH ⦃ prf = i ⦄ ]  = !Γ Δ [ i ]

data _⊢_ : Γ → `Set → Set where
  `false           : ∀ {Δ} → Δ ⊢ `Bool
  `true            : ∀ {Δ} → Δ ⊢ `Bool
  `n_              : ∀ {Δ} → ℕ → Δ ⊢ `Nat
  `v_              : ∀ {Δ} → (x : Var) → ⦃ i : x ∈ Δ ⦄ → Δ ⊢ !Γ Δ [ i ]
  `_₋_              : ∀ {Δ t s} → Δ ⊢ ` t ⇨ s → Δ ⊢ t → Δ ⊢ s --application
  `λ_`:_⇨_         : ∀ {Δ tr} → (x : Var) → (tx : `Set)
                        → x ::: tx , Δ ⊢ tr → Δ ⊢ ` tx ⇨ tr
  `_+_             : ∀ {Δ} → Δ ⊢ `Nat → Δ ⊢ `Nat → Δ ⊢ `Nat
  `_*_             : ∀ {Δ} → Δ ⊢ `Nat →  Δ ⊢ `Nat → Δ ⊢ `Nat
  `_∧_             : ∀ {Δ} → Δ ⊢ `Bool → Δ ⊢ `Bool → Δ ⊢ `Bool
  `_∨_             : ∀ {Δ} → Δ ⊢ `Bool →  Δ ⊢ `Bool → Δ ⊢ `Bool
  `_≤_             : ∀ {Δ} → Δ ⊢ `Nat → Δ ⊢ `Nat →  Δ ⊢ `Bool
  `¬_              : ∀ {Δ} → Δ ⊢ `Bool →  Δ ⊢ `Bool
  `_,_             : ∀ {Δ t s} → Δ ⊢ t →  Δ ⊢ s →  Δ ⊢ ` t × s
  `fst             : ∀ {Δ t s} → Δ ⊢ ` t × s → Δ ⊢ t
  `snd             : ∀ {Δ t s} → Δ ⊢ ` t × s → Δ ⊢ s
  `left            : ∀ {Δ t s} → Δ ⊢ t → Δ ⊢ ` t + s
  `right           : ∀ {Δ t s} → Δ ⊢ s → Δ ⊢ ` t + s
  `case_`of_||_    : ∀ {Δ t s u} → Δ ⊢ ` t + s
                        → Δ ⊢ ` t ⇨ u → Δ ⊢ ` s ⇨ u → Δ ⊢ u
  `tt              : ∀ {Δ} → Δ ⊢ `⊤
  `let_`=_`in_     : ∀ {Δ th tb} → (x : Var)
                       → Δ ⊢ th → x ::: th , Δ ⊢ tb → Δ ⊢ tb
  `if_`then_`else_ : ∀ {Δ t} → Δ ⊢ `Bool → Δ ⊢ t → Δ ⊢ t → Δ ⊢ t


data ⟨_⟩ : Γ → Set₁ where
  []   : ⟨ · ⟩
  _∷_  : ∀ {x t Δ} → ⟦ t ⟧ → ⟨ Δ ⟩ → ⟨ x ::: t , Δ ⟩

!_[_] : ∀ {x Δ} → ⟨ Δ ⟩ → (i : x ∈ Δ) → ⟦ !Γ Δ [ i ] ⟧
!_[_] [] ()
!_[_] (val ∷ env) H      = val
!_[_] (val ∷ env) (TH ⦃ prf = i ⦄) = ! env [ i ]


interpret : ∀ {t} → · ⊢ t → ⟦ t ⟧
interpret = interpret' []
  where interpret' : ∀ {Δ t} → ⟨ Δ ⟩ → Δ ⊢ t → ⟦ t ⟧
        interpret' env `true = true
        interpret' env `false = false
        interpret' env `tt = tt
        interpret' env (`n n) = n
        interpret' env ((`v x) ⦃ i = idx ⦄) = ! env [ idx ]
        interpret' env (` f ₋ x) = (interpret' env f) (interpret' env x)
        interpret' env (`λ _ `: tx ⇨ body) = λ (x : ⟦ tx ⟧) → interpret' (x ∷ env) body
        interpret' env (` l + r) = interpret' env l + interpret' env r
        interpret' env (` l * r) = interpret' env l * interpret' env r
        interpret' env (` l ∧ r) = interpret' env l ∧ interpret' env r
        interpret' env (` l ∨ r) = interpret' env l ∨ interpret' env r
        interpret' env (` l ≤ r) with interpret' env l N.≤? interpret' env r
        ...                             | yes  p = true
        ...                             | no ¬p = false
        interpret' env (`¬ x) = not (interpret' env x)
        interpret' env (` f , s) = interpret' env f ,′ interpret' env s
        interpret' env (`fst p) with interpret' env p
        interpret' env (`fst p) | f , s = f
        interpret' env (`snd p) with interpret' env p
        interpret' env (`snd p) | f , s = s
        interpret' env (`left v) = inj₁ (interpret' env v)
        interpret' env (`right v) = inj₂ (interpret' env v)
        interpret' env (`case s `of le || re) with interpret' env s
        interpret' env (`case s `of le || re) | inj₁ l = (interpret' env le) l
        interpret' env (`case s `of le || re) | inj₂ r = (interpret' env re) r
        interpret' env (`let _ `= h `in b) = let hval = interpret' env h in interpret' (hval ∷ env) b
        interpret' env (`if b `then et `else ef) with interpret' env b
        interpret' env (`if b `then et `else ef) | true = interpret' env et
        interpret' env (`if b `then et `else ef) | false = interpret' env ef


instance
  v_type₁ : ∀ {x Δ t} → x ∈ x ::: t , Δ
  v_type₁ = H

  v_type₂ : ∀ {x y Δ t} → ⦃ prf : x ∈ Δ ⦄ → ⦃ x ≠ y ⦄ → x ∈ y ::: t , Δ
  v_type₂ = TH

instance
  xy : x' ≠ y'
  xy = x≠y

  xz : x' ≠ z'
  xz = x≠z

  yx : y' ≠ x'
  yx = y≠x

  yz : y' ≠ z'
  yz = y≠z

  zx : z' ≠ x'
  zx = z≠x

  zy : z' ≠ y'
  zy = z≠y
