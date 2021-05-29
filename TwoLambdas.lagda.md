<!-- -*-agda2-*- -->


```
{-# OPTIONS --without-K --safe --overlapping-instances  #-}

module TwoLambdas where

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

-- infix 2 _∉_
-- data _∉_ : Var → Γ → Set where
--  D : ∀ {x} → x ∉ ·
--  DD : ∀ {x y Δ t} → x ∉ Δ → ¬ (x ≡ y) → x ∉ (y ::: t , Δ)

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
  nfi-true     : ∀ {x Δ} → x nfi Δ ⊢ `Bool ∋ `true
  nfi-false    : ∀ {x Δ} → x nfi Δ ⊢ `Bool ∋ `false
  nfi-var      : ∀ {x y Δ t} → ⦃ i : y ∈ Δ ⦄ → ⦃ eq : t ≡ !Γ Δ [ i ] ⦄ → ¬ (x ≡ y) → x nfi Δ ⊢ t ∋ (`v y) ⦃ i ⦄ ⦃ eq ⦄
  nfi-const    : ∀ {x Δ t c} → x nfi Δ ⊢ t ∋ `c c
  nfi-app      : ∀ {x Δ t s f arg} → x nfi Δ ⊢ t `⇨ s ∋ f → x nfi Δ ⊢ t ∋ arg → x nfi Δ ⊢ s ∋ f `₋ arg
  nfi-lambda-1 : ∀ {x Δ tx tr e}   →                                              x nfi Δ ⊢ tx `⇨ tr ∋ (`λ x `: tx ⇨ e)
  nfi-lambda-2 : ∀ {x y Δ ty tr e} → ¬ (x ≡ y) → x nfi (y ::: ty , Δ) ⊢ tr  ∋ e → x nfi Δ ⊢ ty `⇨ tr ∋ (`λ y `: ty ⇨ e)
  nfi-pair     : ∀ {x Δ t₁ t₂ e₁ e₂} → x nfi Δ ⊢ t₁ ∋ e₁ → x nfi Δ ⊢ t₂ ∋ e₂ → x nfi Δ ⊢ t₁ `× t₂ ∋ e₁ `, e₂
  nfi-fst      : ∀ {x Δ t₁ t₂ e } → x nfi Δ ⊢ t₁ `× t₂ ∋ e → x nfi Δ ⊢ t₁ ∋ `fst e
  nfi-snd      : ∀ {x Δ t₁ t₂ e } → x nfi Δ ⊢ t₁ `× t₂ ∋ e → x nfi Δ ⊢ t₂ ∋ `snd e
  nfi-tt       : ∀ {x Δ} → x nfi Δ ⊢ `⊤ ∋ `tt
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

¬nfi-lambda : ∀ {x y Δ ty tr body} → ¬ (x ≡ y) → ¬ (x nfi (y ::: ty , Δ) ⊢ tr ∋ body) → ¬ (x nfi Δ ⊢ ty `⇨ tr ∋ (`λ y `: ty ⇨ body))
¬nfi-lambda {x} {y} ¬x≡x _                    nfi-lambda-1 = ¬x≡x refl
¬nfi-lambda {x} {y} _    ¬x-nfi-y:::tyΔ⊢tr∋e (nfi-lambda-2 ¬x≡y x-nfi-y:::tyΔ⊢tr∋e) = ¬x-nfi-y:::tyΔ⊢tr∋e x-nfi-y:::tyΔ⊢tr∋e

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
x nfiD (`λ y `: _ ⇨ e) with x ≟ y
... | yes refl                                = yes nfi-lambda-1
... | no ¬x≡y with x nfiD e
...             | yes x-nfi-y:::tyΔ⊢tr∋e      = yes (nfi-lambda-2 ¬x≡y x-nfi-y:::tyΔ⊢tr∋e)
...             | no ¬x-nfi-y:::tyΔ⊢tr∋e      = no (¬nfi-lambda ¬x≡y ¬x-nfi-y:::tyΔ⊢tr∋e)
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
data _[_:::_] : Γ → Var → `Set → Set where
  end   : (x : Var) → (t : `Set) →  · [ x ::: t ]
  shift : ∀ {Δ x t} → (y : Var) → (s : `Set) → Δ [ x ::: t ] → (y ::: s , Δ) [ x ::: t ]

instance
  end-c : {x : Var} → {t : `Set} →  · [ x ::: t ]
  end-c {x} {t} = end x t

  shift-c : ∀ {Δ x t} → {y : Var} → {s : `Set} → ⦃ prf : Δ [ x ::: t ] ⦄ → (y ::: s , Δ) [ x ::: t ]
  shift-c {y = y} {s = s} ⦃ prf = prf ⦄ = shift y s prf

toΓ : ∀ {Δ x t} → Δ [ x ::: t ] → Γ
toΓ (end x t) = x ::: t , ·
toΓ (shift y s endΓ) = y ::: s , toΓ endΓ

_y∈Δ→y∈toΓΔ_ : ∀ {x y t Δ} → y ∈ Δ → (Δ′ : Δ [ x ::: t ]) → y ∈ toΓ Δ′
() y∈Δ→y∈toΓΔ (end x t)  -- y ∈ · → y ∈ x ::: t , ·
H  y∈Δ→y∈toΓΔ (shift y s Δ) = H 
(TH ⦃ prf = y∈Δ ⦄) y∈Δ→y∈toΓΔ (shift y s Δ) = TH ⦃ prf = y∈Δ y∈Δ→y∈toΓΔ Δ ⦄ 


_y∈toΓΔ→y∈Δ1_ : ∀ {x y t Δ} → ¬ (x ≡ y) → (Δ′ : Δ [ x ::: t ]) → y ∈ toΓ Δ′ → y ∈ Δ
_y∈toΓΔ→y∈Δ1_ {x} {y} {t} {Δ = ·} ¬x≡y (end .x .t) H with ¬x≡y refl
... | ()
_y∈toΓΔ→y∈Δ1_ {x} {y} ¬x≡y (shift y s (end x t)) H = H
_y∈toΓΔ→y∈Δ1_ {x} {y} ¬x≡y (shift y′ s (end _ t)) (TH ⦃ H ⦄) with ¬x≡y refl
...|  ()
_y∈toΓΔ→y∈Δ1_ {x} {y} ¬x≡y (shift y′ s (end _ t)) (TH ⦃ TH ⦃ () ⦄ ⦄)
_y∈toΓΔ→y∈Δ1_         ¬x≡y (shift _ _ (shift _ _ _)) H = H
_y∈toΓΔ→y∈Δ1_ {x} {y} ¬x≡y (shift _ _ (shift z u Δ′)) (TH ⦃ y∈Δ ⦄)  = TH ⦃ _y∈toΓΔ→y∈Δ1_ ¬x≡y (shift z u Δ′) y∈Δ ⦄

toExt-Γ : ∀ {x y t s Δ}  → ⦃ Δ′ : Δ [ x ::: t ] ⦄ → ⦃ i : y ∈ Δ ⦄ → ¬ (x ≡ y) → (s ≡ !Γ Δ [ i ]) → s ≡ !Γ (toΓ Δ′) [ i y∈Δ→y∈toΓΔ Δ′ ]
toExt-Γ ⦃ end x t ⦄ ⦃ ⦄  _ refl
toExt-Γ ⦃ shift y s Δ ⦄ ⦃ H ⦄ _ refl = refl
toExt-Γ ⦃ shift y s Δ ⦄ ⦃ TH ⦃ prf ⦄ ⦄ ¬x≡y s≡!ΓΔ[i] = toExt-Γ ⦃ Δ ⦄ ⦃ prf ⦄ ¬x≡y s≡!ΓΔ[i]

fromExt-Γ : ∀ {x y t s Δ} →  ⦃ Δ′ : Δ [ x ::: t ] ⦄ → ⦃ i : y ∈ toΓ Δ′ ⦄ → (¬x≡y : ¬ (x ≡ y)) → s ≡ !Γ (toΓ Δ′) [ i  ] → (s ≡ !Γ Δ [ _y∈toΓΔ→y∈Δ1_ ¬x≡y Δ′  i ])
fromExt-Γ = {!!} 

```

------------------------------

```
reduceEnv : ∀ {x t s Δ Δₓ} → {Δᵉ : Δ [ x ::: s ]} → ⦃ eq : Δₓ ≡ toΓ Δᵉ ⦄ → (e : Δₓ ⊢ t) → x nfi e → Δ ⊢ t
reduceEnv `true nfi-true                               = `true 
reduceEnv `false nfi-false                             = `false
reduceEnv {Δᵉ = Δᵉ} ⦃ eq = refl ⦄ ((`v y) ⦃ i = i ⦄ ⦃ eq = eq′ ⦄) (nfi-var ¬x≡y) = (`v y) ⦃ i = _y∈toΓΔ→y∈Δ1_ ¬x≡y Δᵉ i ⦄  ⦃ eq = fromExt-Γ ⦃ Δ′ = Δᵉ ⦄ ⦃ i = i ⦄ ¬x≡y eq′ ⦄
reduceEnv (`c c) (nfi-const )                          = `c c
reduceEnv {x} {t} {s} {Δ} {Δᵉ = Δᵉ} ⦃ eq = eq ⦄ (`λ _ `: tx ⇨ e) nfi-lambda-1 with x nfiD e
... | yes x-nfi-e = `λ x `: tx ⇨ reduceEnv {Δᵉ = shift x tx Δᵉ} ⦃ eq = cong (λ δ → x ::: tx , δ) eq ⦄ e x-nfi-e
... | no ¬x-nfi-e = `λ x `: tx ⇨ {!!}  -- ?1 : x ::: tx , Δ ⊢ tr 
reduceEnv {Δᵉ = Δᵉ} ⦃ eq = eq ⦄ (`λ y `: t ⇨ e) (nfi-lambda-2 ¬x≡y x-nfi-e)  = `λ y `: t ⇨ reduceEnv {Δᵉ = shift y t Δᵉ } ⦃ eq = cong (λ δ → y ::: t , δ) eq ⦄  e x-nfi-e
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
... | yes refl | yes x-nfi-f | yes refl = reduceEnv { Δᵉ = end x s } f x-nfi-f
... | _        | _   | _   = lam
eta-reduce (`λ x `: _ ⇨ body) = `λ x `: _ ⇨ body
```
