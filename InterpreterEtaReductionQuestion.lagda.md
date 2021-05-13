<!-- -*-agda2-*- -->

Hi Dr. Al-Sibahi,

I am writing to you again because I think you might be the only
person who can help me with a problem I've having. I really want
to be able to do eta-reduction on terms. That is I want a function with
the following type signature:

    eta-reduce : ∀ {t₁ t₂} → · ⊢ t₁ `⇨ t₂ → · ⊢ t₁ `⇨ t₂

I want the function to be the identity function on terms that
can't be eta-reduced and to eta-reduce those terms that can be.

Let me start by presenting a modified version of your interpreter.
I have done the following: 

- updated it to work with Agda in 2021
- added some `instance` declarations to resolve `_∈_` proofs.
- added the `--overlapping-instances` option to the `OPTIONS` pragma.
- Pulled out constant functions such as `` `_∧_ `` into their own data structure
  called `Constant` and added a constructor `` `c `` to the `_⊢_` data structure
  to embed them in terms.
- Added a variable type (`Var`), a data structure to prove that two variables are not
  equal and some `instance` declarations so that these can be resolved automatically.
  I've also written a function `_≟_`
- changed the type of `` `v_ `` to `` `v_ : ∀ {Δ t} → (x : Var) → ⦃ i : x ∈ Δ ⦄ → ⦃ eq : t ≡ !Γ Δ [ i ] ⦄ → Δ ⊢ t ``
  The reasons behind this are detailed on the Agda Zulip [here](https://agda.zulipchat.com/#narrow/stream/238741-general/topic/Help.20with.20a.20unification.20error.20in.20an.20interpreter).
  I did this because I wanted to write a data type that captured the essence of the idea of a "x is not free in Δ" 


```
{-# OPTIONS --without-K --safe --overlapping-instances --verbose=9 #-}

module InterpreterEtaReductionQuestion where

open import Data.Char hiding (_≤_ ; _≟_)
open import Data.Bool hiding (_≤_ ;_≟_)
open import Data.Nat hiding (_≤_ ; _≟_)
open import Data.Unit hiding (_≟_)
import Data.Nat as N
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable
import Data.String as Str
open import Data.Nat.Show
import Data.List as List
open import Data.Empty
open import Relation.Binary using (Decidable)

infix 3 _:::_,_
infix 2 _∈_

infix 1 _⊢_

data `Set : Set where
  `Bool : `Set
  _`⇨_  : `Set → `Set → `Set
  `⊤    : `Set
  _`×_  : `Set → `Set → `Set
infixr 2 _`⇨_

-- I realised I needed some way to say that two types (in `` `Set ``) are equal
-- but I don't yet know enough to write such a function. I left some holes
-- and decided I could probably finish it later.


module S where
  h : ∀ {t₀ t₁ s₀ s₁} → t₀ ≡ t₁ → s₀ ≡ s₁ → (t₀ `⇨ s₀) ≡ (t₁ `⇨ s₁)
  h = {!!}

  _≟_ : Decidable {A = `Set} _≡_
  `Bool ≟ `Bool                 = yes refl
  `⊤ ≟ `⊤                       = yes refl
  (t₀ `⇨ s₀) ≟ (t₁ `⇨ s₁) with t₀ ≟ t₁ | s₀ ≟ s₁
  ... | yes p | yes q           = yes (h p  q)
  ... | no  ¬p | no ¬q          = no {!!}


_`=_ : `Set → `Set → Bool
`Bool `= `Bool = true
(t₀ `⇨ s₀) `= (t₁ `⇨ s₁) = t₀ `= t₁ ∧ s₀ `= s₁
`⊤ `= `⊤                 = true
(t₀ `× t₁) `= (s₀ `× s₁) = t₀ `= s₀ ∧ t₁ `= s₁
_ `= _                   = false

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

_≟_ : Decidable {A = Var} _≡_
x' ≟ x' = yes refl
y' ≟ y' = yes refl
z' ≟ z' = yes refl
x' ≟ y' = no λ()
x' ≟ z' = no λ()
y' ≟ x' = no λ()
y' ≟ z' = no λ()
z' ≟ x' = no λ()
z' ≟ y' = no λ()

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
  `v_              : ∀ {Δ t} → (x : Var) → ⦃ i : x ∈ Δ ⦄ → ⦃ eq : t ≡ !Γ Δ [ i ] ⦄ → Δ ⊢ t
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
        interpret' env ((`v x) ⦃ i = idx ⦄ ⦃ refl ⦄ ) = ! env [ idx ]
        interpret' env (f `₋ x)             = (interpret' env f) (interpret' env x)
        interpret' env (`λ _ `: tx ⇨ body)  = λ (x : ⟦ tx ⟧) → interpret' (x ∷ env) body
        interpret' env (`c f)               = interpretConstant f
        interpret' env (f `, s)             = interpret' env f ,′ interpret' env s
        interpret' env (`fst p) with interpret' env p
        interpret' env (`fst p) | f , s     = f
        interpret' env (`snd p) with interpret' env p
        interpret' env (`snd p) | f , s     = s
```

Thanks for reading this far.  You'll notice that it's still very recognisable as the
interpreter you originally wrote.

Below are two versions of a function that does logical and. I would like to be able
to eta-reduce `and₁` to `and₂`

```
and₁ : · ⊢ `Bool `× `Bool `⇨ `Bool
and₁ = `λ x' `: `Bool `× `Bool ⇨ `c `∧ `₋ `v x' 

and₂ : · ⊢ `Bool `× `Bool `⇨ `Bool
and₂ = `c `∧
```

One of the first things I realise I would need is to encode the idea of
"x is not free in Δ". I did this using the following data type. It took
me quite a while to get it to this stage. It might not be correct.
It is not based on any presentation in a textbook or online. I came up
with it myself. If you have any feedback on its definition feel free to
let me know.


```
data _nfi_⊢_∋_ : Var → (Δ : Γ) → (t : `Set) → Δ ⊢ t → Set where
  nfi-true   : ∀ {x Δ} → x nfi Δ ⊢ `Bool ∋ `true
  nfi-false  : ∀ {x Δ} → x nfi Δ ⊢ `Bool ∋ `false
  nfi-var    : ∀ {x y Δ t} → ⦃ i : y ∈ Δ ⦄ → ⦃ eq : t ≡ !Γ Δ [ i ] ⦄ → ⦃ ne : x ≠ y ⦄ → x nfi Δ ⊢ t ∋ (`v y) ⦃ i ⦄ ⦃ eq ⦄
  nfi-const  : ∀ {x Δ t c} → x nfi Δ ⊢ t ∋ `c c
  nfi-app    : ∀ {x Δ t s f arg} → x nfi Δ ⊢ t `⇨ s ∋ f → x nfi Δ ⊢ t ∋ arg → x nfi Δ ⊢ s ∋ f `₋ arg
  nfi-lambda : ∀ {x Δ tx tr body} → x nfi Δ ⊢ tx `⇨ tr ∋ (`λ x `: tx ⇨ body)
  nfi-pair   : ∀ {x Δ t₁ t₂ e₁ e₂} → x nfi Δ ⊢ t₁ ∋ e₁ → x nfi Δ ⊢ t₂ ∋ e₂ → x nfi Δ ⊢ t₁ `× t₂ ∋ e₁ `, e₂
  nfi-fst    : ∀ {x Δ t₁ t₂ e } → x nfi Δ ⊢ t₁ `× t₂ ∋ e → x nfi Δ ⊢ t₁ ∋ `fst e
  nfi-snd    : ∀ {x Δ t₁ t₂ e } → x nfi Δ ⊢ t₁ `× t₂ ∋ e → x nfi Δ ⊢ t₂ ∋ `snd e
  nfi-tt     : ∀ {x Δ} → x nfi Δ ⊢ `⊤ ∋ `tt
```

I then introduced a bunch of instances so that it could be inferred automatically.
I thought this would come in handy below.

```
instance 
  nfi-true-i   : ∀ {x Δ} → x nfi Δ ⊢ `Bool ∋ `true
  nfi-true-i = nfi-true

  nfi-false-i  : ∀ {x Δ} → x nfi Δ ⊢ `Bool ∋ `false
  nfi-false-i = nfi-false

  nfi-var-i    : ∀ {x y Δ t} → ⦃ i : y ∈ Δ ⦄ → ⦃ eq : t ≡ !Γ Δ [ i ] ⦄ → ⦃ ne : x ≠ y ⦄ → x nfi Δ ⊢ t ∋ (`v y) ⦃ i ⦄ ⦃ eq ⦄
  nfi-var-i = nfi-var

  nfi-const-i  : ∀ {x Δ t c} → x nfi Δ ⊢ t ∋ `c c
  nfi-const-i = nfi-const

  nfi-app-i   : ∀ {x Δ t s f arg} → ⦃ x nfi Δ ⊢ t `⇨ s ∋ f ⦄ → ⦃ x nfi Δ ⊢ t ∋ arg ⦄ → x nfi Δ ⊢ s ∋ f `₋ arg
  nfi-app-i ⦃ a ⦄ ⦃ b ⦄ = nfi-app a b

  nfi-lambda-i : ∀ {x Δ tx tr body} → x nfi Δ ⊢ tx `⇨ tr ∋ (`λ x `: tx ⇨ body)
  nfi-lambda-i = nfi-lambda

  nfi-pair-i   : ∀ {x Δ t₁ t₂ e₁ e₂} → ⦃ x nfi Δ ⊢ t₁ ∋ e₁ ⦄  → ⦃ x nfi Δ ⊢ t₂ ∋ e₂ ⦄ → x nfi Δ ⊢ t₁ `× t₂ ∋ e₁ `, e₂
  nfi-pair-i ⦃ a ⦄ ⦃ b ⦄ = nfi-pair a b

  nfi-fst-i    : ∀ {x Δ t₁ t₂ e } → ⦃ x nfi Δ ⊢ t₁ `× t₂ ∋ e ⦄ → x nfi Δ ⊢ t₁ ∋ `fst e
  nfi-fst-i ⦃ a ⦄ = nfi-fst a

  nfi-snd-i    : ∀ {x Δ t₁ t₂ e } → ⦃ x nfi Δ ⊢ t₁ `× t₂ ∋ e ⦄ → x nfi Δ ⊢ t₂ ∋ `snd e
  nfi-snd-i ⦃ a ⦄ = nfi-snd a

  nfi-tt-i     : ∀ {x Δ} → x nfi Δ ⊢ `⊤ ∋ `tt
  nfi-tt-i = nfi-tt
```

We need a function to contract the environment. I use it in `reduceEnv` below.
The fact `redundantX` type checks below shows me that this is not a completely
misguided idea.


```
redundantX : ∀ {t s} → x' ::: t , (x' ::: s , ·) ⊢ t
redundantX = `v x'
```

However, I didn't get too far with this function. I got stuck on the
\`v x case.

```
contract : ∀ {x t₁ t₂ t Δ} → x ::: t₁ , (x ::: t₂ , Δ) ⊢ t → x ::: t₁ , Δ ⊢ t
contract `true = `true
contract `false = `false
-- I have not completed the other cases. I got stuck on `v x
contract _ = {!!}
```

However, assuming that a `contract` function is possible. I did manage to write a
function, called `reduceEnv`, that reduces the environment size given a proof
that x is not free in a term.

One thing that worried me a little is Agda let's me omit the case for
`` reduceEnv (`v y) (nfi-var ⦃ i = H ⦄) ``. I can see that the case is impossible
but when I tried to write a case that contained the absurd pattern that didn't work
either. Why does Agda let me omit the case but I can't write one showing that it's
"impossible" by using an absurd pattern somewhere?

I think the answer might have something to do with the interaction of instance resolution
with Agda. I don't the statement "there is no instance that could fit this case" is good
enough "evidence" for Agda that the case is impossible.

In fact, I think I'm pretty skeptical about using instances the way I have here.
There's probably a better way to encode the idea of "x is not free in term". I just
don't know what that better way is! 

```
-- I'm so happy with the type of this. Dependent types in action! 
reduceEnv : ∀ {x t s Δ} → (e : (x ::: s , Δ ⊢ t)) → ⦃ x nfi x ::: s , Δ ⊢ t ∋ e ⦄ → Δ ⊢ t
reduceEnv `true ⦃ nfi-true ⦄   = `true 
reduceEnv `false ⦃ nfi-false ⦄ = `false
reduceEnv (`v y) ⦃ nfi-var ⦃ i = TH ⦄ ⦄ = `v y
-- somehow Agda let's me omit the LHS: reduceEnv (`v y) (nfi-var ⦃ i = H ⦄). I don't know why. I'd feel more comfortable if it demanded it by asking for an absurd pattern.
reduceEnv (`c c) ⦃ nfi-const ⦄ = `c c
reduceEnv (e₁ `, e₂) ⦃ nfi-pair x-nfi-e₁ x-nfi-e₂ ⦄ = reduceEnv e₁ ⦃ x-nfi-e₁ ⦄ `, reduceEnv e₂ ⦃ x-nfi-e₂ ⦄
reduceEnv (`fst e) ⦃ nfi-fst nfi-t₁×t₂ ⦄ = `fst (reduceEnv e ⦃ nfi-t₁×t₂ ⦄)
reduceEnv (`snd e) ⦃ nfi-snd nfi-t₁×t₂ ⦄ = `snd (reduceEnv e ⦃ nfi-t₁×t₂ ⦄)
reduceEnv .`tt ⦃ nfi-tt ⦄ = `tt
reduceEnv (f `₋ x) ⦃ nfi-app nfi-t⇨s nfi-t ⦄ = (reduceEnv f ⦃ nfi-t⇨s ⦄) `₋ (reduceEnv x ⦃ nfi-t ⦄)
reduceEnv {x = x₀} (`λ x `: u ⇨ e) ⦃ nfi-lambda ⦄ = `λ x `: u ⇨ contract e
```

This final function, `eta-reduce` is a complete mess. I got stuck pretty quickly on this.



I got stuck on the lambda case in the `eta-reduce` function.
If you uncomment the case below and type check you get the error message:


    No instance of type x nfi x ::: t₁ , · ⊢ t₁ `⇨ t₂ ∋ f was found in
    scope.
    when checking that f is a valid argument to a function of type
    {x = x₁ : Var} {t : `Set} {s = s₁ : `Set} {Δ : Γ}
    (e : x₁ ::: s₁ , Δ ⊢ t) ⦃ _ : x₁ nfi x₁ ::: s₁ , Δ ⊢ t ∋ e ⦄ →
    Δ ⊢ t

I can see why this is. We don't know the form of `f` and so instance resolution
can't do anything.


```
eta-reduce : ∀ {t₁ t₂} → · ⊢ t₁ `⇨ t₂ → · ⊢ t₁ `⇨ t₂
eta-reduce (`c c) = `c c
eta-reduce (f `₋ x) = f `₋ x
eta-reduce (`fst x) = `fst x
eta-reduce (`snd x) = `snd x
-- eta-reduce {t₁ = t₁} lam@(`λ_`:_⇨_ x s (f `₋ ((`v_  {t = t₁′} y) ))) with  t₁′ S.≟ t₁ 
-- ... | yes refl = reduceEnv f
-- ... | _ | _ = lam
eta-reduce (`λ x `: _ ⇨ body) = `λ x `: _ ⇨ body
```

So, I think I've pretty comprehensively failed in my endeavour to write this `eta-reduce`
function. I think it's mainly because I am so inexperienced in Agda and don't know the right
techniques yet. I feel like I'm on the right track.

I realise I'm asking a lot of you to have a look over this broken code but I don't know what else
to do. I feel like such a function should be possible to write and I want to know how.

I did a bit of a literature search but I can't a presentation of the Simply Typed Lambda Calculus is that
formalises the idea of "x is not free in term". Also the similar notion of "x is not free in environment"
is also not formalised in many presentations. I tried searching for calculi with "explicit substitution"
in the hope that one of them might help me but they were so different to the simple presentation of
the STLC that I was familiar with.

Anyway, that's enough rambling from me. I hope you can help me with this conundrum.

Sean



