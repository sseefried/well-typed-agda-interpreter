{-# OPTIONS --without-K --safe --overlapping-instances #-}


-- Reference to check out
--
-- Simply Typed Lambda Calculus in Agda, without Shortcuts
-- https://gergo.erdi.hu/blog/2013-05-01-simply_typed_lambda_calculus_in_agda,_without_shortcuts/


module InterpreterWithConstants where

open import Data.Char hiding (_≤_)
open import Data.Bool hiding (_≤_)
open import Data.Nat hiding (_≤_)
open import Data.Unit
import Data.Nat as N
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
import Data.String as Str
open import Data.Nat.Show
import Data.List as List
open import Data.Empty

infix 3 _:::_,_
infix 2 _∈_
infix 2 _∉_

infix 1 _⊢_

data `Set : Set where
  `Bool : `Set
  _`⇨_  : `Set → `Set → `Set
  `⊤    : `Set
  _`×_  : `Set → `Set → `Set
infixr 2 _`⇨_

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

⟦_⟧ : `Set → Set
⟦ `Bool ⟧ = Bool
⟦ (t `⇨ s) ⟧ =  ⟦ t ⟧ → ⟦ s ⟧
⟦ `⊤ ⟧ = ⊤
⟦ (t `× s) ⟧ = ⟦ t ⟧ × ⟦ s ⟧

data Γ : Set where
  ·         : Γ
  _:::_,_   : Var → `Set → Γ → Γ

data _∈_ :  Var → Γ → Set where
  H  : ∀ {x Δ t } → x ∈ x ::: t , Δ
  TH : ∀ {x y Δ t} → ⦃ prf : x ∈ Δ ⦄ → ⦃ neprf : x ≠ y ⦄ → x ∈ y ::: t , Δ

instance
  ∈_type₁ : ∀ {x Δ t} → x ∈ x ::: t , Δ
  ∈_type₁ = H

  ∈_type₂ : ∀ {x y Δ t} → ⦃ prf : x ∈ Δ ⦄ → ⦃ x ≠ y ⦄ → x ∈ y ::: t , Δ
  ∈_type₂ = TH

data _∉_ : Var → Γ → Set where
  H : ∀ {x} → x ∉ ·
  TH : ∀ {x y Δ t} → ⦃ prf : x ∉ Δ ⦄ → ⦃ neprf : x ≠ y ⦄ → x ∉ y ::: t , Δ

instance
  ∉_type₁ : ∀ {x} → x ∉ ·
  ∉_type₁ = H

  ∉_type₂ : ∀ {x y Δ t} → ⦃ prf : x ∉ Δ ⦄ → ⦃ x ≠ y ⦄ → x ∉ y ::: t , Δ
  ∉_type₂ = TH

!Γ_[_] : ∀ {x} → (Δ : Γ) → x ∈ Δ → `Set
!Γ_[_] · ()
!Γ _ ::: t , Δ [ H ]     = t
!Γ _ ::: _ , Δ [ TH ⦃ prf = i ⦄ ]  = !Γ Δ [ i ]


infix 30 `v_
infix 30 `c_

infix 24 _`,_
infixl 22 _`₋_

data Constant : `Set → Set where
  `not           : Constant (`Bool `⇨ `Bool)
  `∧             : Constant (`Bool `× `Bool `⇨ `Bool)
  `∨             : Constant (`Bool `× `Bool `⇨ `Bool)
  `xor           : Constant (`Bool `× `Bool `⇨ `Bool)

data _⊢_ : Γ → `Set → Set where
  `false           : ∀ {Δ} → Δ ⊢ `Bool
  `true            : ∀ {Δ} → Δ ⊢ `Bool
  `v_              : ∀ {Δ} → (x : Var) → ⦃ i : x ∈ Δ ⦄ → Δ ⊢ !Γ Δ [ i ]
  `c_              : ∀ {Δ t} → Constant t → Δ ⊢ t
  _`₋_             : ∀ {Δ t s} → Δ ⊢ t `⇨ s → Δ ⊢ t → Δ ⊢ s --application
  `λ_`:_⇨_         : ∀ {Δ tr} → (x : Var) → (tx : `Set)
                        → x ::: tx , Δ ⊢ tr → Δ ⊢ tx `⇨ tr

  _`,_             : ∀ {Δ t s} → Δ ⊢ t →  Δ ⊢ s →  Δ ⊢ t `× s
  `fst             : ∀ {Δ t s} → Δ ⊢ t `× s → Δ ⊢ t
  `snd             : ∀ {Δ t s} → Δ ⊢ t `× s → Δ ⊢ s
  `tt              : ∀ {Δ} → Δ ⊢ `⊤

data ⟨_⟩ : Γ → Set₁ where
  []   : ⟨ · ⟩
  _∷_  : ∀ {x t Δ} → ⟦ t ⟧ → ⟨ Δ ⟩ → ⟨ x ::: t , Δ ⟩

!_[_] : ∀ {x Δ} → ⟨ Δ ⟩ → (i : x ∈ Δ) → ⟦ !Γ Δ [ i ] ⟧
!_[_] [] ()
!_[_] (val ∷ env) H      = val
!_[_] (val ∷ env) (TH ⦃ prf = i ⦄) = ! env [ i ]


interpretConstant : ∀ {t} → Constant t → ⟦ t ⟧
interpretConstant `not = not
interpretConstant `∧   = uncurry _∧_
interpretConstant `∨   = uncurry _∨_
interpretConstant `xor = uncurry _xor_


interpret : ∀ {t} → · ⊢ t → ⟦ t ⟧
interpret = interpret' []
  where interpret' : ∀ {Δ t} → ⟨ Δ ⟩ → Δ ⊢ t → ⟦ t ⟧
        interpret' env `true                = true
        interpret' env `false               = false
        interpret' env `tt                  = tt
        interpret' env ((`v x) ⦃ i = idx ⦄) = ! env [ idx ]
        interpret' env (f `₋ x)             = (interpret' env f) (interpret' env x)
        interpret' env (`λ _ `: tx ⇨ body)  = λ (x : ⟦ tx ⟧) → interpret' (x ∷ env) body
        interpret' env (`c f)               = interpretConstant f
        interpret' env (f `, s)             = interpret' env f ,′ interpret' env s
        interpret' env (`fst p) with interpret' env p
        interpret' env (`fst p) | f , s     = f
        interpret' env (`snd p) with interpret' env p
        interpret' env (`snd p) | f , s     = s

-----

and₁ : · ⊢ `Bool `× `Bool `⇨ `Bool
and₁ = `λ x' `: `Bool `× `Bool ⇨ `c `∧ `₋ `v x'

and₂ : · ⊢ `Bool `× `Bool `⇨ `Bool
and₂ = `c `∧


{-

I want to write a function called eta-reduce that one could prove the following:

pf : eta-reduce and₁ ≡ and₂
pf = refl

This function will eta-reduce when it can, and do nothing when it can't.
For instance the following should be true:

  eta-reduce-constant : ∀ {c} → eta-reduce (`c c) ≡ `c c

However, I get stuck even on this case. Uncomment the definition below and try to 
type check this module:

-}

-- eta-reduce : ∀ {t₁ t₂} → · ⊢ t₁ `⇨ t₂ → · ⊢ t₁ `⇨ t₂
-- eta-reduce (`c c) = ?

{-

You will get the following error message: 

  I'm not sure if there should be a case for the constructor `v_,
  because I get stuck when trying to solve the following unification
  problems (inferred index ≟ expected index):
    Δ ≟ ·
    !Γ Δ [ i ] ≟ t₁ `⇨ t₂
  when checking the definition of eta-reduce

I did a bit of searching on the Internet and the only source I could find
that I could understand was this one: https://doisinkidney.com/posts/2018-09-20-agda-tips.html

It seems to be suggesting that one of the indices for a type is not in constructor form but is,
rather, a function.

Looking at the definition of _⊢_ we see that the `v_` constructor is most likely at fault: 

  `v_ : ∀ {Δ} → (x : Var) → ⦃ i : x ∈ Δ ⦄ → Δ ⊢ !Γ Δ [ i ]

The result type is `Δ ⊢ !Γ Δ [ i ]`. Clearly the index `!Γ Δ [ i ]` is referring to a 
user-defined function.

My question is, "how can I fix this?". How would I modify the _⊢_ data structure 


- I would be open to an alternative interpreter for the Simply Typed Lambda Calculus
- This interpreter is a modified form of this code base. ttps://github.com/ahmadsalim/well-typed-agda-interpreter
  It has had instance declarations added and the syntactic form of terms has changed a little. I pulled out
  the constant functions into their own data structure called `Constant` and changed their types a little to work
  on products (_×_) instead of a curried form.


-}




{-
The instance based searching for _∈_ proofs might be a problem. I'm uncomfortable
with the use of --overlapping-instances




-}

-- eta-reduce : ∀ {t₁ t₂} → · ⊢ t₁ `⇨ t₂ → · ⊢ t₁ `⇨ t₂
-- eta-reduce (`λ x `: _ ⇨ f `₋ y) = {!!}
-- eta-reduce t = t



