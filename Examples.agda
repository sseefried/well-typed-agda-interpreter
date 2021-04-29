{-# OPTIONS --without-K --safe --overlapping-instances #-}
module Examples where

open import Data.Nat

-- local imports
open import Interpreter


pf : y' ∈ y' ::: `Nat , (x' ::: `Nat , ·)
pf = H

pf2 : x' ∈ y' ::: `Nat , (x' ::: `Nat , ·)
pf2 = TH


testSimpleLambda : · ⊢ `Nat
testSimpleLambda = ` (`λ x' `: `Nat ⇨ ` (`v x') + (`v x')) ₋ `n 10

testSimpleLambda2 : · ⊢ ` `Nat ⇨ `Nat
testSimpleLambda2 = `λ x' `: `Nat ⇨ ` (`v x') + (`v x')

testNestedLambda : · ⊢ `Nat
testNestedLambda = ` ` (`λ x' `: `Nat ⇨ (`λ_`:_⇨_ y' `Nat (` `v x' * `v y'))) ₋ `n 10 ₋ `n 15


testNestedLambda2 : · ⊢  ` `Nat ⇨ (` `Nat ⇨ `Nat)
testNestedLambda2 = (`λ x' `: `Nat ⇨ (`λ_`:_⇨_ y' `Nat (` `v x' * `v y')))

-- The following definitions do not type check. They are a relic from
-- when the interpreter still had some bugs. Uncomment them to verify
-- they don't type check
-- testNamingNotWorking : · ⊢ `Bool
-- testNamingNotWorking = ` ` `λ x' `: `Bool ⇨ (`λ x' `: `⊤ ⇨ `v x') ₋ `true ₋ `tt

--testNamingNotWorking2 : · ⊢ ` `Bool ⇨ ` `⊤ ⇨ `Bool -- incorrect type!
--testNamingNotWorking2 = `λ x' `: `Bool ⇨ (`λ x' `: `⊤ ⇨ `v x')

testNamingWorking : · ⊢ `⊤
testNamingWorking = ` ` `λ x' `: `Bool ⇨ (`λ x' `: `⊤ ⇨ `v x') ₋ `true ₋ `tt

testNamingWorking2 : · ⊢ ` `Bool ⇨ ` `⊤ ⇨ `⊤
testNamingWorking2 = `λ x' `: `Bool ⇨ (`λ x' `: `⊤ ⇨ `v x')

testSum1 : · ⊢ `Nat
testSum1 = `let z' `= `case `left (`n 10) `of
                              `λ z' `: `Nat ⇨ `v z'
                           || `λ x' `: `Bool ⇨ `if `v x' `then `n 1 `else `n 0
           `in `v z'

testSum2 : · ⊢ `Nat
testSum2 = `let z' `= `case `right `true `of
                              `λ z' `: `Nat ⇨ `v z'
                           || `λ x' `: `Bool ⇨ `if `v x' `then `n 1 `else `n 0
           `in `v z'

testProduct1 : · ⊢ `Bool
testProduct1 = `fst (` `true , (` `n 10 , `tt ))

testProduct2 : · ⊢ ` `Nat × `⊤
testProduct2 = `snd (` `true , (` `n 10 , `tt ))

testDeMorganFullOr : · ⊢ `Bool
testDeMorganFullOr = `let z' `= `λ x' `: `Bool ⇨ `λ y' `: `Bool ⇨ `¬ (` `v x' ∨ `v y')
                     `in ` ` `v z' ₋ `true ₋ `true
testDeMorganBrokenAnd : · ⊢ `Bool
testDeMorganBrokenAnd = `let z' `= `λ x' `: `Bool ⇨ `λ y' `: `Bool ⇨ ` `¬ `v x' ∧ `¬ `v y'
                        `in ` ` `v z' ₋ `true ₋ `true

tester : Set
tester = {! interpret testSimpleLambda2 !}
