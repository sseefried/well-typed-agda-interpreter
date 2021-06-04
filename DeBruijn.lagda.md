<!-- -*-agda2-*- -->

```
module DeBruijn where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; _≤_; z≤n; s≤s)
open import Data.Bool using (Bool; not; _∧_; _∨_;_xor_; true; false)
open import Data.Product hiding (_,_)
import Data.Product as P
open import Data.Sum
open import Data.Unit hiding (_≟_; _≤?_)
open import Relation.Nullary using (¬_; Dec)
open import Relation.Nullary.Decidable using (True; toWitness)


infix  1 _⊢_
infix  4 _∈_
infixr 5 _,_

infixr 2 _`⇨_

data `Set : Set where
  `Bool : `Set
  _`⇨_  : `Set → `Set → `Set
  `⊤    : `Set
  _`×_  : `Set → `Set → `Set


⟦_⟧ : `Set → Set
⟦ `Bool ⟧ = Bool
⟦ (t `⇨ s) ⟧ =  ⟦ t ⟧ → ⟦ s ⟧
⟦ `⊤ ⟧ = ⊤
⟦ (t `× s) ⟧ = ⟦ t ⟧ × ⟦ s ⟧

data Γ : Set where
  ·     : Γ
  _,_   : `Set → Γ → Γ

data _∈_ : `Set → Γ →  Set where
  Z  : ∀ {Δ t} → t ∈ t , Δ
  S_ : ∀ {Δ t s} → t ∈ Δ → t ∈ s , Δ


data Constant : `Set → Set where
  `not           : Constant (`Bool `⇨ `Bool)
  `∧             : Constant (`Bool `× `Bool `⇨ `Bool)
  `∨             : Constant (`Bool `× `Bool `⇨ `Bool)
  `xor           : Constant (`Bool `× `Bool `⇨ `Bool)

infix 30 `_
infix 30 `c_
infix  25 ƛ_
infix  29 S_
infix  29 #_
infix 24 _`,_
infixl 22 _`₋_

data _⊢_ : Γ → `Set → Set where
  `false           : ∀ {Δ} → Δ ⊢ `Bool
  `true            : ∀ {Δ} → Δ ⊢ `Bool
  `_               : ∀ {Δ t} → t ∈ Δ → Δ ⊢ t
  `c_              : ∀ {Δ t} → Constant t → Δ ⊢ t
  _`₋_             : ∀ {Δ t s} → Δ ⊢ (t `⇨ s) → Δ ⊢ t → Δ ⊢ s --application
  `ƛ_              : ∀ {Δ t s} → t , Δ ⊢ s → Δ ⊢ t `⇨ s
  _`,_             : ∀ {Δ t s} → Δ ⊢ t →  Δ ⊢ s →  Δ ⊢ t `× s
  `fst             : ∀ {Δ t s} → Δ ⊢ t `× s → Δ ⊢ t
  `snd             : ∀ {Δ t s} → Δ ⊢ t `× s → Δ ⊢ s
  `tt              : ∀ {Δ} → Δ ⊢ `⊤


length : Γ → ℕ
length ·        =  zero
length (_ , Δ)  =  suc (length Δ)

lookup : {Δ : Γ} → {n : ℕ} → (p : n < length Δ) → `Set
lookup {(t , _)} {zero}    (s≤s z≤n)  =  t
lookup {(_ , Δ)} {(suc n)} (s≤s p)    =  lookup p

count : ∀ {Δ} → {n : ℕ} → (p : n < length Δ) → lookup p ∈ Δ
count {_ , _} {zero}    (s≤s z≤n)  =  Z
count {_ , Δ} {(suc n)} (s≤s p)    =  S (count p)


--
-- This convenience function lets us use ℕ instead of S_ and Z constructors in lambda terms
--
#_ : ∀ {Δ} → (n : ℕ) → {n∈Δ : True (suc n ≤? length Δ)} → Δ ⊢ lookup (toWitness n∈Δ)
#_ n {n∈Δ}  =  ` count (toWitness n∈Δ)

test : Set -- Dec (2 ≤ length (`Bool , `Bool , ·))
test = {! True (2 ≤? length (`Bool , `Bool , ·)) !}


_ :  `Bool , · ⊢ `Bool
_ =  # 0

_ : · ⊢ (`Bool `⇨ `Bool) `⇨ `Bool `⇨ `Bool
_ = `ƛ (`ƛ (# 1 `₋ (# 1 `₋ # 0)))

```

And now for the interpreter

```
interpretConstant : ∀ {t} → Constant t → ⟦ t ⟧
interpretConstant `not = not
interpretConstant `∧   = uncurry _∧_
interpretConstant `∨   = uncurry _∨_
interpretConstant `xor = uncurry _xor_

data ⟨_⟩ : Γ → Set₁ where
  []   : ⟨ · ⟩
  _∷_  : ∀ {t Δ} → ⟦ t ⟧ → ⟨ Δ ⟩ → ⟨ t , Δ ⟩

!_[_] : ∀ {t Δ} → ⟨ Δ ⟩ → (i : t ∈ Δ) → ⟦ t ⟧
!_[_] [] ()
!_[_] (val ∷ env) Z      = val
!_[_] (val ∷ env) (S i) = ! env [ i ]


interpret : ∀ {t} → · ⊢ t → ⟦ t ⟧
interpret = interpret' []
  where
    interpret' : ∀ {Δ t} → ⟨ Δ ⟩ → Δ ⊢ t → ⟦ t ⟧
    interpret' _ `true                  = true
    interpret' _ `false                 = false
    interpret' env (` i)                = ! env [ i ]
    interpret' env (f `₋ x)             = (interpret' env f) (interpret' env x)
    interpret' env (`ƛ body)            = λ x → interpret' (x ∷ env) body
    interpret' env (`c f)               = interpretConstant f
    interpret' env (f `, s)             = interpret' env f ,′ interpret' env s
    interpret' env (`fst p) with interpret' env p
    interpret' env (`fst p) | f P., s     = f
    interpret' env (`snd p) with interpret' env p
    interpret' env (`snd p) | f P., s     = s
    interpret' env `tt                  = tt

```


Now for some tests:

```

a∧[b∨c] : · ⊢ `Bool `⇨ `Bool `⇨ `Bool `⇨ `Bool
a∧[b∨c] = `ƛ `ƛ `ƛ `c `∧ `₋ (# 2 `, (`c `∨ `₋ (# 1 `, # 0)))

_ : Bool → Bool → Bool → Bool
_ = {! interpret a∧[b∨c] !}
```

Renaming. Might not need this

```
ext : ∀ {Δ Δ′} → (∀ {t} → t ∈ Δ → t ∈ Δ′) → (∀ {t s} → t ∈ s , Δ  → t ∈ s , Δ′)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)
```

Eta-contraction

```
eta-reduce : ∀ {t₁ t₂} → · ⊢ t₁ `⇨ t₂ → · ⊢ t₁ `⇨ t₂
eta-reduce (`c c) = `c c
eta-reduce (f `₋ x) = f `₋ x
eta-reduce (`fst x) = `fst x
eta-reduce (`snd x) = `snd x
eta-reduce lam@(`ƛ (f `₋ ` Z)) = ?
eta-reduce (`ƛ body) = `ƛ body

```
