<!-- -*-agda2-*- -->

```
module EtaReductionDeBruijn where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _>_; _≤?_; _<?_; z≤n; s≤s)
import Data.Nat as N
open import Data.Bool using (Bool; not; _∧_; _∨_;_xor_; true; false)
open import Data.Product hiding (_,_)
import Data.Product as P
open import Data.Sum
open import Data.Unit hiding (_≟_; _≤?_; _≤_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Relation.Unary using (Decidable)
open import Data.Maybe using (Maybe; nothing; just)
open import Level using (0ℓ)
import Level as L
open import Relation.Binary.Core using (REL)


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
infix 21 `ƛ_
infix  29 S_
infix  29 #_
infix 24 _`,_
infixl 22 _`₋_

data _⊢_ : Γ → `Set → Set where
  `false           : ∀ {Δ} → Δ ⊢ `Bool
  `true            : ∀ {Δ} → Δ ⊢ `Bool
  `_               : ∀ {Δ t} → t ∈ Δ → Δ ⊢ t
  `c_              : ∀ {Δ t} → Constant t → Δ ⊢ t
  _`₋_             : ∀ {Δ t s} → Δ ⊢ t `⇨ s → Δ ⊢ t → Δ ⊢ s --application
  `ƛ_              : ∀ {Δ t s} → t , Δ ⊢ s → Δ ⊢ t `⇨ s
  _`,_             : ∀ {Δ t s} → Δ ⊢ t →  Δ ⊢ s →  Δ ⊢ t `× s
  `fst             : ∀ {Δ t s} → Δ ⊢ t `× s → Δ ⊢ t
  `snd             : ∀ {Δ t s} → Δ ⊢ t `× s → Δ ⊢ s
  `tt              : ∀ {Δ} → Δ ⊢ `⊤


length : Γ → ℕ
length ·        =  zero
length (_ , Δ)  =  suc (length Δ)

lookup : {Δ : Γ} → {n : ℕ} → (p : n N.< length Δ) → `Set
lookup {(t , _)} {zero}    (s≤s z≤n)  =  t
lookup {(_ , Δ)} {(suc n)} (s≤s p)    =  lookup p

count : ∀ {Δ} → {n : ℕ} → (p : n N.< length Δ) → lookup p ∈ Δ
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

```
ext : ∀ {Δ Δ′} → (∀ {t} → t ∈ Δ → t ∈ Δ′) → (∀ {t s} → t ∈ s , Δ  → t ∈ s , Δ′)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)
```

```
rename : ∀ {Δ Δ′} → (∀ {t} → t ∈ Δ → t ∈ Δ′) → (∀ {t} → Δ ⊢ t → Δ′ ⊢ t)
rename ρ `true          = `true
rename ρ `false         = `false
rename ρ (`c c)         = `c c
rename ρ (` n)          =  ` (ρ n)
rename ρ (f `₋ a)       = rename ρ f `₋ rename ρ a
rename ρ (e₁ `, e₂)     = rename ρ e₁ `, rename ρ e₂
rename ρ (`ƛ e)         = `ƛ (rename (ext ρ) e)
rename ρ (`fst e)       = `fst (rename ρ e)
rename ρ (`snd e)       = `snd (rename ρ e)
rename ρ `tt             = `tt

insert : {i : ℕ} → `Set → (Δ : Γ) → (i N.≤ length Δ) → Γ
insert {zero}  t      Δ   z≤n    = t , Δ
insert {suc _} t (s , Δ) (s≤s n) = s , insert t Δ n

dropVar : ∀ {i s t Δ p} → t ∈ insert {i} s Δ p → Maybe (t ∈ Δ)
dropVar {zero}  {p = z≤n} Z                    = nothing -- trying to drop the insert variable
dropVar {zero}  {p = z≤n} (S n)                = just n  -- variable is after insertion point
dropVar {suc _} {Δ = _ , Δ} {p = s≤s p} (S n)
  with dropVar n
... | just t∈Δ                                 = just (S t∈Δ)
... | nothing                                  = nothing
dropVar {suc _} {Δ = _ , Δ} {s≤s p} Z          = just Z

drop : ∀ {i s t Δ p} → insert {i} s Δ p ⊢ t → Maybe (Δ ⊢ t)
drop `false = just `false
drop `true = just `true
drop (`c c) = just (`c c)
drop (` n) with dropVar n
... | just n′ = just (` n′)
... | nothing = nothing
drop (f `₋ a) with drop f | drop a
... | just f′ | just a′ = just (f′ `₋ a′)
... | _       | _       = nothing
drop {i = i} {t = t₁ `⇨ _ } {Δ = Δ} {p = p} (`ƛ e) with drop {i = suc i} {Δ = t₁ , Δ} {p = s≤s p} e
... | just e′ = just (`ƛ e′)
... | nothing = nothing
drop (e₁ `, e₂) with drop e₁ | drop e₂
... | just e₁′ | just e₂′ = just (e₁′ `, e₂′)
... |  _ | _ = nothing
drop (`fst e) with drop e
... | just e′ = just (`fst e′)
... | nothing = nothing
drop (`snd e) with drop e
... | just e′ = just (`snd e′)
... | nothing = nothing
drop `tt = just `tt

eta-reduce : ∀ {t₁ t₂ Δ} → Δ ⊢ t₁ `⇨ t₂ → Δ ⊢ t₁ `⇨ t₂
eta-reduce (`c c) = `c c
eta-reduce (` n) = ` n
eta-reduce (f `₋ x) = f `₋ x
eta-reduce (`fst x) = `fst x
eta-reduce (`snd x) = `snd x
eta-reduce lam@(`ƛ (f `₋ (` Z))) with drop {p = z≤n} f
... | just f′ = f′
... | nothing = lam
eta-reduce (`ƛ e) = `ƛ e
```

Now for some tests

```
eta-expanded : · ⊢ `Bool `⇨ `Bool
eta-expanded = `ƛ (`ƛ (`c `not `₋ ` Z)) `₋ ` Z

eta-reduced :  · ⊢ `Bool `⇨ `Bool
eta-reduced = `c `not

pf : eta-reduced ≡ eta-reduce (eta-reduce eta-expanded)
pf = refl

eta-expanded2 : `Bool , `⊤ , · ⊢ `Bool `⇨ `Bool
eta-expanded2 = `ƛ (`c `not `₋ ` Z)

_ : `Bool , `⊤ , · ⊢ `Bool `⇨ `Bool
_ = eta-reduce eta-expanded2
```
