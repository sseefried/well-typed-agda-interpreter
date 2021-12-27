<!-- -*-agda2-*- -->


```
{-# OPTIONS --without-K --safe --overlapping-instances --verbose=9 #-}

module LopX where

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

x≡y→¬x≠y : ∀ {x y} → x ≡ y → ¬ (x ≠ y)
x≡y→¬x≠y refl ()

foo2 : ¬ (x' ≡ y')
foo2 with x' ≟ y'
... | yes ()
... | no ¬x≡y = ¬x≡y

¬x≡y→x≠y : ∀ {x y} → ¬ (x ≡ y) → x ≠ y
¬x≡y→x≠y {x'} {x'} ¬x≡x with ¬x≡x refl
... | () 

¬x≡y→x≠y {x'} {y'} _ with x' ≟ y'
... | yes ()
... | no _ = x≠y

¬x≡y→x≠y {x'} {z'} _ with x' ≟ z'
... | yes ()
... | no _  = x≠z
¬x≡y→x≠y {y'} {y'} ¬x≡x with ¬x≡x refl
... | () 

¬x≡y→x≠y {y'} {x'} _ with y' ≟ x'
... | yes ()
... | no _ = y≠x

¬x≡y→x≠y {y'} {z'} _ with y' ≟ z'
... | yes ()
... | no _ = y≠z
¬x≡y→x≠y {z'} {z'} ¬x≡x with ¬x≡x refl
... | () 

¬x≡y→x≠y {z'} {x'} _ with z' ≟ x'
... | yes ()
... | no _ = z≠x

¬x≡y→x≠y {z'} {y'} _ with z' ≟ y'
... | yes ()
... | no _ = z≠y



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



```
data _nfi_⊢_∋_ : Var → (Δ : Γ) → (t : `Set) → Δ ⊢ t → Set where
  nfi-true   : ∀ {x Δ} → x nfi Δ ⊢ `Bool ∋ `true
  nfi-false  : ∀ {x Δ} → x nfi Δ ⊢ `Bool ∋ `false
  nfi-var    : ∀ {x y Δ t} → ⦃ i : y ∈ Δ ⦄ → ⦃ eq : t ≡ !Γ Δ [ i ] ⦄ → ¬ (x ≡ y) → x nfi Δ ⊢ t ∋ (`v y) ⦃ i ⦄ ⦃ eq ⦄
  nfi-const  : ∀ {x Δ t c} → x nfi Δ ⊢ t ∋ `c c
  nfi-app    : ∀ {x Δ t s f arg} → x nfi Δ ⊢ t `⇨ s ∋ f → x nfi Δ ⊢ t ∋ arg → x nfi Δ ⊢ s ∋ f `₋ arg
--  nfi-lambda : ∀ {x Δ tx tr e} → x nfi Δ ⊢ tx `⇨ tr ∋ (`λ x `: tx ⇨ e)
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

--¬nfi-lambda : ∀ {x y Δ tx tr body} → ¬ (x ≡ y) → ¬ (x nfi Δ ⊢ tx `⇨ tr ∋ (`λ y `: tx ⇨ body))
--¬nfi-lambda {x} {y} ¬x≡x nfi-lambda = ¬x≡x refl

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
x nfiD (`λ y `: _ ⇨ e) = no λ()
--x nfiD (`λ y `: _ ⇨ e) with x ≟ y
--... | yes refl                                = yes nfi-lambda
--... | no ¬x≡y                                 = no (¬nfi-lambda ¬x≡y)
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

```
reduceEnv : ∀ {x t s Δ} → (e : (x ::: s , Δ ⊢ t)) → x nfi e → Δ ⊢ t
reduceEnv `true nfi-true                               = `true 
reduceEnv `false nfi-false                             = `false
reduceEnv (`v y) (nfi-var ⦃ i = H  ⦄ ¬y≡y) with ¬y≡y refl
... | () 
reduceEnv (`v y) (nfi-var ⦃ i = TH ⦄ _)                = `v y
reduceEnv (`c c) (nfi-const )                          = `c c
reduceEnv (f `₋ a) (nfi-app x-nfi-f x-nfi-a)           = reduceEnv f x-nfi-f `₋ reduceEnv a x-nfi-a
reduceEnv (e₁ `, e₂) (nfi-pair x-nfi-e₁  x-nfi-e₂)     = reduceEnv e₁ x-nfi-e₁ `, reduceEnv e₂ x-nfi-e₂
reduceEnv (`fst e) (nfi-fst x-nfi-e)                   = `fst (reduceEnv e x-nfi-e)
reduceEnv (`snd e) (nfi-snd x-nfi-e)                   = `snd (reduceEnv e x-nfi-e)
reduceEnv `tt nfi-tt                                   = `tt

eta-reduce : ∀ {t₁ t₂} → · ⊢ t₁ `⇨ t₂ → · ⊢ t₁ `⇨ t₂
eta-reduce (`c c) = `c c
eta-reduce (f `₋ x) = f `₋ x
eta-reduce (`fst x) = `fst x
eta-reduce (`snd x) = `snd x
eta-reduce {t₁ = t₁} lam@(`λ x `: s ⇨ (f `₋ ((`v_  {t = t₁′} x′) ))) with  t₁′ S.≟ t₁ | x nfiD f | x ≟ x′
... | yes refl | yes x-nfi-f | yes refl = reduceEnv f x-nfi-f
... | _        | _   | _   = lam
eta-reduce (`λ x `: _ ⇨ body) = `λ x `: _ ⇨ body


ex₁ : · ⊢ `Bool `⇨ `Bool
ex₁ =  eta-reduce (`λ x' `: `Bool ⇨ (`c `not) `₋ `v x') 

ex₁′ : · ⊢ `Bool `⇨ `Bool
ex₁′ =  `c `not 

ex₂ : · ⊢ `Bool `⇨ `Bool
ex₂ = `λ x' `: `Bool ⇨ (`λ y' `: `Bool ⇨ (`c `not)) `₋ `true `₋ `v x'

ex₂′ : · ⊢ `Bool `⇨ `Bool
ex₂′ = (`λ y' `: `Bool ⇨ (`c `not)) `₋ `true 

pf₁ : eta-reduce ex₁ ≡ ex₁′
pf₁ = refl

nfi₁ : · ⊢ `Bool `⇨ `Bool
nfi₁ = (`λ y' `: `Bool ⇨ (`c `not)) `₋ `true

nfi₁-extend : x' ::: `⊤ , · ⊢ `Bool `⇨ `Bool
nfi₁-extend = (`λ y' `: `Bool ⇨ `c `not) `₋ `true

nfiD-example-1 : Dec (x' nfi · ⊢ (`Bool `⇨ `Bool) ∋ (`c `not))
nfiD-example-1 =  {! x' nfiD `c `not !}

t₂ : · ⊢ `Bool `⇨ `Bool
t₂ = {! eta-reduce ex₂ !}

i₁ : Bool → Bool
i₁ = {! interpret ex₁ !}

i₂ : Bool → Bool
i₂ = {! interpret ex₂ !}
```


# Exploring how one term can be reconstructed as another.

The following two terms type-check. But how could I
convert `lam-ex-2` into `lam-ex-1`. Let's look at how
`lam-ex-2` gets type checked in the first place.

```
lam-ex-1 : · ⊢ `Bool `⇨ `Bool
lam-ex-1 = (`λ y' `: `Bool ⇨ (`c `not)) `₋ `true

lam-ex-2 : x' ::: `⊤ , · ⊢ `Bool `⇨ `Bool
lam-ex-2 = (`λ y' `: `Bool ⇨ `c `not) `₋ `true

```

Looking at the `` _‵₋_ `` constructor we see that the following two terms
need to type check

```
lam-ex-2-app-fun : x' ::: `⊤ , · ⊢ `Bool `⇨ `Bool `⇨ `Bool
lam-ex-2-app-fun = (`λ y' `: `Bool ⇨ `c `not)

lam-ex-2-app-arg : x' ::: `⊤ , · ⊢ `Bool
lam-ex-2-app-arg = `true
```


Looking at the `` `λ_`:_⇨_ `` constructor we see that `lam-ex-2-app-fun` requires that
the following term type checks:

```
lam-ex-2-app-fun-body : y' ::: `Bool , (x' ::: `⊤ , ·) ⊢ `Bool `⇨ `Bool
lam-ex-2-app-fun-body = `c `not
```

However, if we were to reconstruct `lam-ex-1` we'd have to start with:

```
lam-ex-1-app-fun-body : y' ::: `Bool ,  · ⊢ `Bool `⇨ `Bool
lam-ex-1-app-fun-body = `c `not

lam-ex-1-app-fun : · ⊢ `Bool `⇨ `Bool `⇨ `Bool
lam-ex-1-app-fun = (`λ y' `: `Bool ⇨ lam-ex-1-app-fun-body)
```

Then

```
lam-ex-1-app-arg : · ⊢ `Bool
lam-ex-1-app-arg = `true
```

And the finally we get `lam-ex-1`.

```
lam-ex-1-reconstructed : · ⊢ `Bool `⇨ `Bool
lam-ex-1-reconstructed = lam-ex-1-app-fun `₋ lam-ex-1-app-arg
```

The crucial step seems to be the difference between
`lam-ex-2-app-fun-body` and `lam-ex-1-app-fun-body`.

The `` x' ::: `⊤ `` is not out the front of the environment.
It is at the end. We need to contract from `y' ::: `Bool , (x' ::: `⊤ , ·)`
to `y' ::: `Bool ,  ·`.

However for `lam-ex-2-app-fun` and `lam-ex-2-app-arg` we are just stripping
off the front.

It feels like I'm going to have to come up with a notion of a "environment prefix".

For instance `` x' ::: `⊤ , · `` would be an environment prefix of
`` y' ::: `Bool , (x' ::: `⊤ , ·) `` and also `` y' ::: ‵Bool , (z' ::: `⊤ , (x' ::: `⊤ , ·)) ``


----

The following function _is_ eta-reducible. In fact, it can be eta-reduced
twice.

```
is-eta-reducible : · ⊢ `Bool `⇨ `Bool
is-eta-reducible = `λ x' `: `Bool ⇨ (`λ y' `: `Bool ⇨ `c `not `₋ `v y') `₋ `v x'

is-eta-reducible-nested : · ⊢ `Bool `⇨ `Bool
is-eta-reducible-nested = `λ y' `: `Bool ⇨ `c `not `₋ `v y'

fully-eta-reduced : · ⊢ `Bool `⇨ `Bool
fully-eta-reduced = `c `not
```

Notice how `` x' ::: `Bool `` is not required in the environment for `is-eta-reducible-nested`?
This will be important for later.

Okay, now I want to look at situations where it's important that `x` is not free in an expression.
The function `not-eta-reducible` below is, as its name says, not eta-reducible. The reason
is that `x` is not free in ``λ y' `: `Bool ⇨ `c `not `₋ `v x'`.

```
not-eta-reducible : · ⊢ `Bool `⇨ `Bool
not-eta-reducible = `λ x' `: `Bool ⇨ (`λ y' `: `Bool ⇨ `c `not `₋ `v x') `₋ `v x'

```

The smallest type of the nested lambda is: 

```
not-eta-reducible-nested : x' ::: `Bool , · ⊢ `Bool `⇨ `Bool
not-eta-reducible-nested = `λ y' `: `Bool ⇨ `c `not `₋ `v x'
```

However we cannot remove the `x'` from the environment as it is free in
the expression.

The following just doesn't type check.

```
-- not-eta-reducible-nested-2 : · ⊢ `Bool `⇨ `Bool
-- not-eta-reducible-nested-2 = `λ y' `: `Bool ⇨ `c `not `₋ `v x'
```


Let's see what would happen if we tried to eta-reduce `non-eta-reducible`. Where should
we stop and say "this is wrong"? I think it's clear that as soon as we realise that
`` x' ::: `Bool `` is required in the environment for `not-eta-reducible-nested` we
should stop.

But how do we actually discover this?

Eventually we would get down to the the expression

```
not-eta-reducible-nested-body-app-arg : x' ::: `Bool , · ⊢ `Bool
not-eta-reducible-nested-body-app-arg = `v x'
```

x is free in this expression. It's then free in this expression:

```
not-eta-reducible-nested-body-app : x' ::: `Bool , · ⊢ `Bool
not-eta-reducible-nested-body-app = `c `not `₋ `v x'
```

If the binder was `` `λ x' `: `Bool `` and not `` `λ y' `: `Bool ``
then x' would not be free.

```
not-eta-reducible-nested-body-app--bound-by-λx' : · ⊢ `Bool `⇨ `Bool
not-eta-reducible-nested-body-app--bound-by-λx' = `λ x' `: `Bool ⇨ `c `not `₋ `v x'
```

------

I'd now just like to look at two nested lambdas


```
lam-ex2-1 : x' ::: `⊤ , · ⊢ `Bool `⇨ `Bool
lam-ex2-1 = `λ y' `: `Bool ⇨ (`λ z' `: `Bool ⇨ `c `not `₋ `v z') `₋ `v y'

lam-ex2-1-body : y' ::: `Bool , (x' ::: `⊤ , ·) ⊢ `Bool
lam-ex2-1-body = (`λ z' `: `Bool ⇨ `c `not `₋ `v z') `₋ `v y'

-- neither y' nor x' required in environment
lam-ex2-1-body-appfun : y' ::: `Bool , (x' ::: `⊤ , ·) ⊢ `Bool `⇨ `Bool
lam-ex2-1-body-appfun = (`λ z' `: `Bool ⇨ `c `not `₋ `v z')

-- only x' not required in environment
lam-ex2-1-body-apparg : y' ::: `Bool , (x' ::: `⊤ , ·) ⊢ `Bool
lam-ex2-1-body-apparg = `v y'

lam-ex2-1-body-appfun-body : z' ::: `Bool , (y' ::: `Bool , (x' ::: `⊤ , ·)) ⊢ `Bool
lam-ex2-1-body-appfun-body = `c `not `₋ `v z'

lam-ex2-1-body-appfun-body-appfun : z' ::: `Bool , (y' ::: `Bool , (x' ::: `⊤ , ·)) ⊢ `Bool `⇨ `Bool
lam-ex2-1-body-appfun-body-appfun = `c `not 

lam-ex2-1-body-appfun-body-apparg : z' ::: `Bool , (y' ::: `Bool , (x' ::: `⊤ , ·)) ⊢ `Bool 
lam-ex2-1-body-appfun-body-apparg = `v z'

```


So I do want a function which can just lop off the last `` x' ::: `⊤  ``

Now I want to think about the evidence that would be required to do such a thing.



Let's look at three differnt "lop-x" functions below that remove an x "at the end" of the environment

```
lop-x1 : ∀ {x y t s Δ} → (e : (x ::: t , Δ) ⊢ s) → ⦃ i : y ∈ Δ ⦄ → ⦃ eq : s ≡ !Γ Δ [ i ] ⦄ → ⦃ y-ne-x : y ≠ x ⦄ → ⦃ e ≡ `v y ⦄  → Δ ⊢ s
lop-x1 {x} {y} (`v _) = `v y

lop-x2 : ∀ {x y z t s u Δ} →  (e : (z ::: u , (x ::: t , Δ)) ⊢ s)
                           → ⦃ i : y ∈ (x ::: t , Δ) ⦄
                           → ⦃ eq : s ≡ !Γ (x ::: t , Δ) [ i ] ⦄
                           → ⦃ i2 : y ∈ Δ ⦄
                           → ⦃ eq2 : s ≡ !Γ  Δ [ i2 ] ⦄
                           → ⦃ y-ne-z : y ≠ z ⦄
                           → ⦃ e ≡ `v y ⦄
                           → (z ::: u , Δ) ⊢ s
lop-x2 {x} {y} (`v _) = `v y

lop-x3 : ∀ {x y z w t s u v Δ} →  (e : y ::: s , (z ::: u , (w ::: v , (x ::: t , Δ))) ⊢ s) → ⦃ e ≡ `v y ⦄  → y ::: s , (z ::: u , (w ::: v , Δ)) ⊢ s
lop-x3 {x} {y} (`v _) = `v y

```

They all nicely type-check. But how the hell would I generalise this?


The data type below captures the idea of an environment that has variable `x` of type `t`
"at the end". 

```
data _[_:::_] : Γ → Var → `Set → Set where
  end   : (x : Var) → (t : `Set) →  · [ x ::: t ]
  shift : ∀ {Δ x t} → (y : Var) → (s : `Set) → Δ [ x ::: t ] → (y ::: s , Δ) [ x ::: t ]
```

Here is an example:

```
at-end-ex1 : · [ x' ::: `Bool ]
at-end-ex1 = end x' `Bool

at-end-ex2 : (z' ::: `Bool , (y' ::: `⊤ , ·)) [ x' ::: `Bool ]
at-end-ex2 = shift z' `Bool (shift y' `⊤ (end x' `Bool))

```

```
instance
  end-c : {x : Var} → {t : `Set} →  · [ x ::: t ]
  end-c {x} {t} = end x t

  shift-c : ∀ {Δ x t} → {y : Var} → {s : `Set} → ⦃ prf : Δ [ x ::: t ] ⦄ → (y ::: s , Δ) [ x ::: t ]
  shift-c {y = y} {s = s} ⦃ prf = prf ⦄ = shift y s prf


toΓ : ∀ {Δ x t} → Δ [ x ::: t ] → Γ
toΓ (end x t) = x ::: t , ·
toΓ (shift y s endΓ) = y ::: s , toΓ endΓ


```

I want a function that given a `y ∈ Δ` and `Δ [ x ::: t ]` gives us a `y ∈ toΓ [ x ::: t ]`

```
_y∈Δ→y∈toΓΔ_ : ∀ {x y t Δ} → y ∈ Δ → (Δ′ : Δ [ x ::: t ]) → y ∈ toΓ Δ′
() y∈Δ→y∈toΓΔ (end x t) 
H  y∈Δ→y∈toΓΔ (shift y s Δ) = H
(TH ⦃ prf = y∈Δ ⦄) y∈Δ→y∈toΓΔ (shift y s Δ) = TH ⦃ prf = y∈Δ y∈Δ→y∈toΓΔ Δ ⦄ 
```

Wow, I can't believe I got that proof out. Now to see if I can generalise `lop-x`

```
toExt-Γ : ∀ {x y t s Δ}  → ⦃ Δ′ : Δ [ x ::: t ] ⦄ → ⦃ i : y ∈ Δ ⦄ → (s ≡ !Γ Δ [ i ]) → s ≡ !Γ (toΓ Δ′) [ i y∈Δ→y∈toΓΔ Δ′ ]
toExt-Γ ⦃ end x t ⦄ ⦃ ⦄  refl
toExt-Γ ⦃ shift y s Δ ⦄ ⦃ H ⦄ refl = refl
toExt-Γ ⦃ shift y s Δ ⦄ ⦃ TH ⦃ prf ⦄ ⦄ = toExt-Γ ⦃ Δ ⦄ ⦃ prf ⦄
```

Wow, also can't believe I got that proof out. Woohoo! 

```
lop-x-var : ∀ {x y t s Δ}
      → ⦃ Δ′ : Δ [ x ::: t ] ⦄
      → (e : (toΓ Δ′) ⊢ s)
      → ⦃ i : y ∈ Δ ⦄
      → ⦃ eq : s ≡ !Γ Δ [ i ] ⦄
      → ⦃ eq : s ≡ !Γ (toΓ Δ′) [ i y∈Δ→y∈toΓΔ Δ′ ] ⦄
      -- ^^^ I need this here in order to make the type checker terminate.
      -- but it would be better if I could write ⦃ eq = i y∈Δ→y∈toΓΔ Δ′ ⦄ in
      -- isVar parameter below.
      → ⦃ isVar :  e ≡ (`v y) ⦃ i = i y∈Δ→y∈toΓΔ Δ′ ⦄ ⦃ eq = eq ⦄ ⦄
      → Δ ⊢ s
lop-x-var {x} {y} (`v _) = `v y

test-arg :  z' ::: `Bool , (y' ::: `⊤ , (y' ::: `Bool , ·)) ⊢ `⊤
test-arg = `v y'

test-lop-x : z' ::: `Bool , (y' ::: `⊤ , ·) ⊢ `⊤
test-lop-x = lop-x-var test-arg 

test-arg2 :  z' ::: `Bool , (y' ::: `Bool , ·) ⊢ `Bool
test-arg2 = `v y'

test-lop-x2 : z' ::: `Bool , · ⊢ `Bool
test-lop-x2 = lop-x-var test-arg2

```

I'd have prefered this version here:

lop-x-var : ∀ {x y t s Δ}
      → ⦃ Δ′ : Δ [ x ::: t ] ⦄
      → (e : (toΓ Δ′) ⊢ s)
      → ⦃ i : y ∈ Δ ⦄
      → ⦃ eq : s ≡ !Γ Δ [ i ] ⦄
      → ⦃ isVar :  e ≡ (`v y) ⦃ i = i y∈Δ→y∈toΓΔ Δ′ ⦄ ⦃ eq = toExt-Γ eq ⦄ ⦄
      → Δ ⊢ s
lop-x-var {x} {y} (`v _) = `v y

but it causes Agda to go into a type-check loop.

