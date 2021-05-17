<!-- -*-agda2-*- -->


```
{-# OPTIONS --without-K --safe --overlapping-instances --verbose=9 #-}

module EtaReductionProgress where

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
  `t⇨s≡t′⇨s′ : ∀ {t t′ s s′} → t ≡ t′ → s ≡ s′ → (t `⇨ s) ≡ (t′ `⇨ s′)
  `t⇨s≡t′⇨s′ refl refl = refl

  -- TODO: Put in your learning Agda repo!

  ¬t⇨s≡t′⇨s′-1 : ∀ {t t′ s s′} → ¬ (t ≡ t′) → ¬ ((t `⇨ s) ≡ (t′ `⇨ s′))
  ¬t⇨s≡t′⇨s′-1 ¬t≡t′ refl = ¬t≡t′ refl -- I really need to grok this before moving on

  ¬t⇨s≡t′⇨s′-2 : ∀ {t t′ s s′} → ¬ (s ≡ s′) → ¬ ((t `⇨ s) ≡ (t′ `⇨ s′))
  ¬t⇨s≡t′⇨s′-2 ¬s≡s′ refl = ¬s≡s′ refl  -- This one too! 

  `t×s≡t′×s′ : ∀ {t t′ s s′} → t ≡ t′ → s ≡ s′ → (t `× s) ≡ (t′ `× s′)
  `t×s≡t′×s′ refl refl = refl

  ¬t×s≡t′×s′-1 : ∀ {t t′ s s′} → ¬ (t ≡ t′) → ¬ ((t `× s) ≡ (t′ `× s′))
  ¬t×s≡t′×s′-1 ¬t≡t′ refl = ¬t≡t′ refl -- This one too! 

  ¬t×s≡t′×s′-2 : ∀ {t t′ s s′} → ¬ (s ≡ s′) → ¬ ((t `× s) ≡ (t′ `× s′))
  ¬t×s≡t′×s′-2 ¬s≡s′ refl = ¬s≡s′ refl  -- This one too! 

  _≟_ : Decidable {A = `Set} _≡_
  `Bool ≟ `Bool                 = yes refl
  `Bool ≟ (t `⇨ s)              = no λ()
  `Bool ≟ `⊤                    = no λ()
  `Bool ≟ (t `× s)              = no λ()
  (t `⇨ s) ≟ `Bool              = no λ()
  (t `⇨ s) ≟ (t′ `⇨ s′) with t ≟ t′ | s ≟ s′
  ... | yes t≡t′ | yes s≡s′     = yes (`t⇨s≡t′⇨s′ t≡t′ s≡s′)
  ... | no ¬t≡t′ | _            = no  (¬t⇨s≡t′⇨s′-1 ¬t≡t′)
  ... | _        | no ¬s≡s′     = no  (¬t⇨s≡t′⇨s′-2 ¬s≡s′)
  (t `⇨ s) ≟ `⊤                 = no λ()
  (t `⇨ s) ≟ (t′ `× s′)         = no λ()
  `⊤ ≟ `Bool                    = no λ()
  `⊤ ≟ (t `⇨ s)                 = no λ()
  `⊤ ≟ `⊤                       = yes refl
  `⊤ ≟ (t `× s)                 = no λ()
  (t `× s) ≟ `Bool              = no λ()
  (t `× s) ≟ (t′ `⇨ s′)         = no λ()
  (t `× s) ≟ `⊤                 = no λ()
  (t `× s) ≟ (t′ `× s′) with t ≟ t′ | s ≟ s′
  ... | yes t≡t′ | yes s≡s′     = yes (`t×s≡t′×s′ t≡t′ s≡s′)
  ... | no ¬t≡t′ | _            = no  (¬t×s≡t′×s′-1 ¬t≡t′)
  ... | _        | no ¬s≡s′     = no  (¬t×s≡t′×s′-2 ¬s≡s′) 

  -- Boolean equality
  _=ᵇ_ : `Set → `Set → Bool
  a =ᵇ b = isYes (a ≟ b)

  -- And here's an example
  -- C-c C-n gives no (¬t⇨s≡t′⇨s′-2 (¬t⇨s≡t′⇨s′-1 (λ ())))
  `SetDecEx1 : Dec ((`Bool `⇨ (`Bool `⇨ `Bool)) ≡ (`Bool `⇨ (`⊤ `⇨ `Bool)))
  `SetDecEx1 = {! (`Bool `⇨ (`Bool `⇨ `Bool)) ≟ (`Bool `⇨ (`⊤ `⇨ `Bool)) !}

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

x≠y→¬x≡y : ∀ {x y} → x ≠ y → ¬ (x ≡ y)
x≠y→¬x≡y x≠y = λ()
x≠y→¬x≡y x≠z = λ()
x≠y→¬x≡y y≠x = λ()
x≠y→¬x≡y y≠z = λ()
x≠y→¬x≡y z≠x = λ()
x≠y→¬x≡y z≠y = λ()

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
  nfi-var    : ∀ {x y Δ t} → ⦃ i : y ∈ Δ ⦄ → ⦃ eq : t ≡ !Γ Δ [ i ] ⦄ → ¬ (x ≡ y) → x nfi Δ ⊢ t ∋ (`v y) ⦃ i ⦄ ⦃ eq ⦄
  nfi-const  : ∀ {x Δ t c} → x nfi Δ ⊢ t ∋ `c c
  nfi-app    : ∀ {x Δ t s f arg} → x nfi Δ ⊢ t `⇨ s ∋ f → x nfi Δ ⊢ t ∋ arg → x nfi Δ ⊢ s ∋ f `₋ arg
  nfi-lambda : ∀ {x y Δ tx tr e} → x ≡ y → x nfi Δ ⊢ tx `⇨ tr ∋ (`λ y `: tx ⇨ e)
  -- FIXME-SS: Perhaps create a second nfi-lambda constructor? 
  -- nfi-lambda2 : ∀ {x Δ tx tr e} → x nfi x ::: tx , Δ ⊢ tr ∋ e → x nfi Δ ⊢ tx `⇨ tr ∋ (`λ x `: tx ⇨ e)
  nfi-pair   : ∀ {x Δ t₁ t₂ e₁ e₂} → x nfi Δ ⊢ t₁ ∋ e₁ → x nfi Δ ⊢ t₂ ∋ e₂ → x nfi Δ ⊢ t₁ `× t₂ ∋ e₁ `, e₂
  nfi-fst    : ∀ {x Δ t₁ t₂ e } → x nfi Δ ⊢ t₁ `× t₂ ∋ e → x nfi Δ ⊢ t₁ ∋ `fst e
  nfi-snd    : ∀ {x Δ t₁ t₂ e } → x nfi Δ ⊢ t₁ `× t₂ ∋ e → x nfi Δ ⊢ t₂ ∋ `snd e
  nfi-tt     : ∀ {x Δ} → x nfi Δ ⊢ `⊤ ∋ `tt
```


I think I need a function `nfi` that _computes_ whether a variable is free or not in a term.
I'll try the boolean version first and then perhaps we can upgrade to Decidability.

```
_nfiᵇ_ : ∀ {Δ t} → Var → Δ ⊢ t → Bool
x nfiᵇ `true                          = false
x nfiᵇ `false                         = false
x nfiᵇ (`v y) with x ≟ y
...            | yes refl             = true
...            | no _                 = false
x nfiᵇ (`c x₁)                        = false 
x nfiᵇ (f `₋ a)                       = x nfiᵇ f ∧ x nfiᵇ a
x nfiᵇ (`λ y `: _ ⇨ body) with x ≟ y
...                        | yes refl = true
...                        | no _     = false
x nfiᵇ (x₁ `, x₂)                     = x nfiᵇ x₁ ∧ x nfiᵇ x₂
x nfiᵇ `fst p                         = x nfiᵇ p
x nfiᵇ `snd p                         = x nfiᵇ p
x nfiᵇ `tt                            = false
```

Here's a type synonym for nfi turning it into a binary relation

```
-- Type synonym 
_nfi_ : ∀ {Δ t} → Var → Δ ⊢ t → Set
_nfi_ {Δ} {t} x e = x nfi Δ ⊢ t ∋ e

```

Now to write the decidable version

```

¬nfi-app-1 : ∀ {x Δ t s f a} → ¬ (x nfi Δ ⊢ t `⇨ s ∋ f) → ¬ (x nfi Δ ⊢ s ∋ f `₋ a)
¬nfi-app-1 ¬x-nfi-Δ⊢t⇨s∋f (nfi-app x-nfi-Δ⊢t⇨s∋f _)  = ¬x-nfi-Δ⊢t⇨s∋f x-nfi-Δ⊢t⇨s∋f

¬nfi-app-2 : ∀ {x Δ t s f a} → ¬ (x nfi Δ ⊢ t ∋ a) → ¬ (x nfi Δ ⊢ s ∋ f `₋ a)
¬nfi-app-2 ¬x-nfi-Δ⊢t∋a (nfi-app _ x-nfi-Δ⊢t∋a)  = ¬x-nfi-Δ⊢t∋a x-nfi-Δ⊢t∋a

¬nfi-pair-1 : ∀ {x Δ t₁ t₂ e₁ e₂} → ¬ (x nfi Δ ⊢ t₁ ∋ e₁) → ¬ (x nfi Δ ⊢ t₁ `× t₂ ∋ e₁ `, e₂)
¬nfi-pair-1 ¬x-nfi-Δ⊢t₁∋e₁ (nfi-pair x-nfi-Δ⊢t₁∋e₁ _) = ¬x-nfi-Δ⊢t₁∋e₁ x-nfi-Δ⊢t₁∋e₁

¬nfi-pair-2 : ∀ {x Δ t₁ t₂ e₁ e₂} → ¬ (x nfi Δ ⊢ t₂ ∋ e₂) → ¬ (x nfi Δ ⊢ t₁ `× t₂ ∋ e₁ `, e₂)
¬nfi-pair-2 ¬x-nfi-Δ⊢t₂∋e₂ (nfi-pair _ x-nfi-Δ⊢t₂∋e₂) = ¬x-nfi-Δ⊢t₂∋e₂ x-nfi-Δ⊢t₂∋e₂

¬nfi-fst : ∀ {x Δ t₁ t₂ e } → ¬ (x nfi Δ ⊢ t₁ `× t₂ ∋ e)  → ¬ (x nfi Δ ⊢ t₁ ∋ `fst e)
¬nfi-fst ¬x-nfi-Δ⊢t₁×t₂∋e (nfi-fst x-nfi-Δ⊢t₁×t₂∋e) = ¬x-nfi-Δ⊢t₁×t₂∋e x-nfi-Δ⊢t₁×t₂∋e

¬nfi-snd : ∀ {x Δ t₁ t₂ e } → ¬ (x nfi Δ ⊢ t₁ `× t₂ ∋ e) → ¬ (x nfi Δ ⊢ t₂ ∋ `snd e)
¬nfi-snd ¬x-nfi-Δ⊢t₁×t₂∋e (nfi-snd x-nfi-Δ⊢t₁×t₂∋e) = ¬x-nfi-Δ⊢t₁×t₂∋e x-nfi-Δ⊢t₁×t₂∋e

foo : ∀ {x y} → x ≡ y → ¬ (x ≠ y)
foo refl () 

¬nfi-var : ∀ {x y Δ t} → ⦃ i : y ∈ Δ ⦄ → ⦃ eq : t ≡ !Γ Δ [ i ] ⦄ → x ≡ y → ¬ (x nfi Δ ⊢ t ∋ (`v y))
¬nfi-var x≡y (nfi-var ¬x≡y) = ¬x≡y x≡y

¬nfi-lambda : ∀ {x y Δ tx tr body} → ¬ (x ≡ y) → ¬ (x nfi Δ ⊢ tx `⇨ tr ∋ (`λ y `: tx ⇨ body))
¬nfi-lambda ¬x≡y (nfi-lambda x≡y) = ¬x≡y x≡y

_nfiD_ : ∀ {Δ t} → Decidable {A = Var} {B = Δ ⊢ t} _nfi_
x nfiD `true                                  = yes nfi-true
x nfiD `false                                 = yes nfi-false
x nfiD (`v y) with x ≟ y
... | yes x≡y                                 = no (¬nfi-var x≡y) 
... | no ¬x≡y                                 = yes (nfi-var ¬x≡y)
x nfiD (`c c)                                 = yes nfi-const
x nfiD (f `₋ a) with x nfiD f | x nfiD a
... | yes x-nfi-Δ⊢t⇨s∋f | yes x-nfi-Δ⊢t∋a     = yes (nfi-app x-nfi-Δ⊢t⇨s∋f x-nfi-Δ⊢t∋a)
... | no ¬x-nfi-Δ⊢t⇨s∋f | _                   = no (¬nfi-app-1 ¬x-nfi-Δ⊢t⇨s∋f)
... | _                 | no ¬x-nfi-Δ⊢t∋a     = no (¬nfi-app-2 ¬x-nfi-Δ⊢t∋a)
x nfiD (`λ y `: _ ⇨ body) with x ≟ y
... | yes refl                                = yes (nfi-lambda refl)
... | no ¬x≡y                                 = no (¬nfi-lambda ¬x≡y)
x nfiD (e₁ `, e₂) with x nfiD e₁ | x nfiD e₂
... | yes x-nfi-Δ⊢t₁∋e₁ | yes x-nfi-Δ⊢t₂∋e₂   = yes (nfi-pair x-nfi-Δ⊢t₁∋e₁ x-nfi-Δ⊢t₂∋e₂)
... | no ¬x-nfi-Δ⊢t₁∋e₁ | _                   = no (¬nfi-pair-1 ¬x-nfi-Δ⊢t₁∋e₁)
... | _                 | no ¬x-nfi-Δ⊢t₂∋e₂   = no (¬nfi-pair-2 ¬x-nfi-Δ⊢t₂∋e₂)

x nfiD `fst e with x nfiD e
... | yes x-nfi-Δ⊢t₁×t₂∋e                    = yes (nfi-fst x-nfi-Δ⊢t₁×t₂∋e)
... | no ¬x-nfi-Δ⊢t₁×t₂∋e                    = no (¬nfi-fst ¬x-nfi-Δ⊢t₁×t₂∋e)
x nfiD `snd e with x nfiD e
... | yes x-nfi-Δ⊢t₁×t₂∋e                    = yes (nfi-snd x-nfi-Δ⊢t₁×t₂∋e)
... | no ¬x-nfi-Δ⊢t₁×t₂∋e                    = no (¬nfi-snd ¬x-nfi-Δ⊢t₁×t₂∋e)
x nfiD `tt                                   = yes nfi-tt

```





I then introduced a bunch of instances so that it could be inferred automatically.
I thought this would come in handy below.

```
{-instance 
  nfi-true-i   : ∀ {x Δ} → x nfi Δ ⊢ `Bool ∋ `true
  nfi-true-i = nfi-true

  nfi-false-i  : ∀ {x Δ} → x nfi Δ ⊢ `Bool ∋ `false
  nfi-false-i = nfi-false

  nfi-var-i    : ∀ {x y Δ t} → ⦃ i : y ∈ Δ ⦄ → ⦃ eq : t ≡ !Γ Δ [ i ] ⦄ → ¬ (x ≡ y)  → x nfi Δ ⊢ t ∋ (`v y) ⦃ i ⦄ ⦃ eq ⦄
  nfi-var-i ¬x≡y = nfi-var ¬x≡y

  nfi-const-i  : ∀ {x Δ t c} → x nfi Δ ⊢ t ∋ `c c
  nfi-const-i = nfi-const

  nfi-app-i   : ∀ {x Δ t s f arg} → ⦃ x nfi Δ ⊢ t `⇨ s ∋ f ⦄ → ⦃ x nfi Δ ⊢ t ∋ arg ⦄ → x nfi Δ ⊢ s ∋ f `₋ arg
  nfi-app-i ⦃ a ⦄ ⦃ b ⦄ = nfi-app a b

  nfi-lambda-i : ∀ {x y Δ tx tr body} → x ≡ y → x nfi Δ ⊢ tx `⇨ tr ∋ (`λ y `: tx ⇨ body)
  nfi-lambda-i x≡y = nfi-lambda x≡y

  nfi-pair-i   : ∀ {x Δ t₁ t₂ e₁ e₂} → ⦃ x nfi Δ ⊢ t₁ ∋ e₁ ⦄  → ⦃ x nfi Δ ⊢ t₂ ∋ e₂ ⦄ → x nfi Δ ⊢ t₁ `× t₂ ∋ e₁ `, e₂
  nfi-pair-i ⦃ a ⦄ ⦃ b ⦄ = nfi-pair a b

  nfi-fst-i    : ∀ {x Δ t₁ t₂ e } → ⦃ x nfi Δ ⊢ t₁ `× t₂ ∋ e ⦄ → x nfi Δ ⊢ t₁ ∋ `fst e
  nfi-fst-i ⦃ a ⦄ = nfi-fst a

  nfi-snd-i    : ∀ {x Δ t₁ t₂ e } → ⦃ x nfi Δ ⊢ t₁ `× t₂ ∋ e ⦄ → x nfi Δ ⊢ t₂ ∋ `snd e
  nfi-snd-i ⦃ a ⦄ = nfi-snd a

  nfi-tt-i     : ∀ {x Δ} → x nfi Δ ⊢ `⊤ ∋ `tt
  nfi-tt-i = nfi-tt
-}
```

We need a function to contract the environment. I use it in `reduceEnv` below.
The fact `redundantX` type checks below shows me that this is not a completely
misguided idea.


```
redundantX : ∀ {t s} → x' ::: t , (x' ::: s , ·) ⊢ t
redundantX = `v x'

redundantX2 : ∀ {t s} → x' ::: t , (x' ::: s , ·) ⊢ t `⇨ t
redundantX2 = `λ x' `: _ ⇨ `v x'
```



However, I didn't get too far with this function. I got stuck on the
\`v x case.

```
contract : ∀ {x t₁ t₂ t Δ} → x ::: t₁ , (x ::: t₂ , Δ) ⊢ t → x ::: t₁ , Δ ⊢ t
contract `true = `true
contract `false = `false
contract ((`v y) ⦃ i = H ⦄ ) = `v y
contract ((`v y) ⦃ i = TH ⦄ ) = {!!}
contract (`c c) = `c c
contract (f `₋ a) = contract f `₋ contract a 
contract {x} {t₁} {t₂} (`λ y `: u ⇨ e) with x nfiD e
... | yes x-nfi-e = {!!}
... | no _ = {!!}
contract (e₁ `, e₂) = contract e₁ `, contract e₂
contract (`fst e) = `fst (contract e)  
contract (`snd e) = `snd (contract e) 
contract `tt = `tt
```

Second contract function

```
contract2 : ∀ {x y t₁ t₂ s} → (e : y ::: t₁ , (x ::: s , ·) ⊢ t₂) → (x nfi (`λ y `: t₁ ⇨ e)) → y ::: t₁ , · ⊢ t₂
contract2 `true _  = `true
contract2 `false _ = `false
contract2 ((`v y) ⦃ i = H ⦄) _ = `v y
contract2 ((`v y) ⦃ i = TH ⦄) _ = {!!}
contract2 (`c c) _ = `c c
-- contract2 (f `₋ a) x-nfi-lam = contract f x-nfi-lam `₋ contract a x-nfi-lam
-- contract2 {x} {t₁} {t₂} (`λ y `: u ⇨ e) with x nfiD e
-- ... | yes x-nfi-e = {!!}
-- contract2 (e₁ `, e₂) x-nfi-lam = contract e₁ x-nfi-lam `, contract e₂ x-nfi-lam
--contract2 (`fst e) x-nfi-lam = `fst (contract e x-nfi-lam)  
--contract2 (`snd e) x-nfi-lam = `snd (contract e x-nfi-lam) 
contract2 `tt _ = `tt

```

```
lam2e : ∀ {x y Δ t s e } → x nfi Δ ⊢ t `⇨ s ∋ (`λ y `: t ⇨ e) → x nfi e
lam2e (nfi-lambda refl) = {!!}
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
{- 
-- I'm so happy with the type of this. Dependent types in action! 
reduceEnv : ∀ {x t s Δ} → (e : (x ::: s , Δ ⊢ t)) → ⦃ x nfi x ::: s , Δ ⊢ t ∋ e ⦄ → Δ ⊢ t
reduceEnv `true ⦃ nfi-true ⦄   = `true 
reduceEnv `false ⦃ nfi-false ⦄ = `false
reduceEnv (`v y) ⦃ nfi-var ⦃ i = TH ⦄ x≡y ⦄ = `v y
-- somehow Agda let's me omit the LHS: reduceEnv (`v y) (nfi-var ⦃ i = H ⦄). I don't know why. I'd feel more comfortable if it demanded it by asking for an absurd pattern.
reduceEnv (`c c) ⦃ nfi-const ⦄ = `c c
reduceEnv (e₁ `, e₂) ⦃ nfi-pair x-nfi-e₁ x-nfi-e₂ ⦄ = reduceEnv e₁ ⦃ x-nfi-e₁ ⦄ `, reduceEnv e₂ ⦃ x-nfi-e₂ ⦄
reduceEnv (`fst e) ⦃ nfi-fst nfi-t₁×t₂ ⦄ = `fst (reduceEnv e ⦃ nfi-t₁×t₂ ⦄)
reduceEnv (`snd e) ⦃ nfi-snd nfi-t₁×t₂ ⦄ = `snd (reduceEnv e ⦃ nfi-t₁×t₂ ⦄)
reduceEnv .`tt ⦃ nfi-tt ⦄ = `tt
reduceEnv (f `₋ x) ⦃ nfi-app nfi-t⇨s nfi-t ⦄ = (reduceEnv f ⦃ nfi-t⇨s ⦄) `₋ (reduceEnv x ⦃ nfi-t ⦄)
reduceEnv {x = x₀} (`λ x `: u ⇨ e) ⦃ nfi-lambda x≡y ⦄ = `λ x `: u ⇨ contract e
-}
```

```
reduceEnv : ∀ {x t s} → (e : (x ::: s , · ⊢ t)) → x nfi e → · ⊢ t
reduceEnv `true nfi-true                               = `true 
reduceEnv `false nfi-false                             = `false
reduceEnv (`v y) (nfi-var ⦃ i = H ⦄ ¬x≡y)              = {!!} -- I don't know how to do this case
reduceEnv (`v y) (nfi-var ⦃ i = TH ⦄ ¬x≡y)             = `v y
reduceEnv (`c c) (nfi-const )                          = `c c
reduceEnv (f `₋ a) (nfi-app x-nfi-f x-nfi-a)           = reduceEnv f x-nfi-f `₋ reduceEnv a x-nfi-a
reduceEnv (`λ y `: u ⇨ e) x-nfi-e                      = `λ y `: u ⇨ contract2 e x-nfi-e
reduceEnv (e₁ `, e₂) (nfi-pair x-nfi-e₁  x-nfi-e₂)     = reduceEnv e₁ x-nfi-e₁ `, reduceEnv e₂ x-nfi-e₂
reduceEnv (`fst e) (nfi-fst x-nfi-e)                   = `fst (reduceEnv e x-nfi-e)
reduceEnv (`snd e) (nfi-snd x-nfi-e)                   = `snd (reduceEnv e x-nfi-e)
reduceEnv `tt nfi-tt                                   = `tt
```

-- `λ x : t ⇨ (λ y : u ⇨ e) `₋ (`v x)

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
eta-reduce {t₁ = t₁} lam@(`λ_`:_⇨_ x s (f `₋ ((`v_  {t = t₁′} y) ))) with  t₁′ S.≟ t₁ | x nfiD f
... | yes refl | yes x-nfi-f = reduceEnv f x-nfi-f
... | _        | _           = lam
eta-reduce (`λ x `: _ ⇨ body) = `λ x `: _ ⇨ body
```

This function seems so specific to be almost useless.



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



