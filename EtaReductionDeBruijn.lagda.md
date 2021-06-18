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

We now present a function to perform eta-reduction (if possible)

First we need a function which can insert a type into an
environment. This is required so that we can write
the type signature for a function which "drops" this
extraneous type.

```
insert : {i : ℕ} → `Set → (Δ : Γ) → (i N.≤ length Δ) → Γ
insert {zero}  t      Δ   z≤n    = t , Δ
insert {suc _} t (s , Δ) (s≤s n) = s , insert t Δ n
```

Consider an environment that has been had an extra type
insert. Function `dropVar` will take an index to a type in the
extended environment and then, if it is not the index of the insert
typed, return an index into the environment that has had the inserted
type "dropped". If the index happens to point to the inserted type
then `nothing` is returned.

```
dropVar : ∀ {i s t Δ p} → t ∈ insert {i} s Δ p → Maybe (t ∈ Δ)
dropVar {zero}  {p = z≤n} Z                    = nothing -- trying to drop the inserted variable
dropVar {zero}  {p = z≤n} (S n)                = just n  -- variable is after insertion point
dropVar {suc _} {Δ = _ , Δ} {p = s≤s p} (S n)
  with dropVar n
... | just t∈Δ                                 = just (S t∈Δ)
... | nothing                                  = nothing
dropVar {suc _} {Δ = _ , Δ} {s≤s p} Z          = just Z
```

Function `drop` now makes use of `dropVar` to re-type a
term whose environment contains an unrequired type.
Returns `nothing` when the inserted type is actually
required.

```
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
```

Finally, we introduce the `eta-reduce` function which looks for terms
of the form `` `ƛ (f `₋ (` Z)) `` and eta-reduces them when variable
`` ` Z `` is not free in `f`. This corresponds to the case where
`drop` returns a `just` value.


```
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

-- eta-reduction in an environment which also has extraneous types
-- Success of this means we could eta-reduce "under a lambda"

_ : `Bool , `⊤ , · ⊢ `Bool `⇨ `Bool
_ = eta-reduce eta-expanded2
```
