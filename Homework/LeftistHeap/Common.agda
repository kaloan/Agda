module Homework.LeftistHeap.Common where

open import Lib.Nat
open import Lib.One
open import Lib.Zero
open import Lib.Sum
open import Lib.Eq

Leq : Nat -> Nat -> Set
Leq zero m = One
Leq (suc n) zero = Zero
Leq (suc n) (suc m) = Leq n m

decLeq : (n m : Nat) -> Leq n m + Leq m n
decLeq zero m = inl <>
decLeq (suc n) zero = inr <>
decLeq (suc n) (suc m) = decLeq n m

<=-Leq : {n m : Nat} -> n <= m -> Leq n m
<=-Leq ozero = <>
<=-Leq (osuc p) = <=-Leq p

Leq-refl : (n : Nat) -> Leq n n
Leq-refl n = <=-Leq (<=-refl n)

Leq-trans : (n m k : Nat) -> Leq n m -> Leq m k -> Leq n k
Leq-trans zero m k p q = <>
Leq-trans (suc n) (suc m) (suc k) p q = Leq-trans n m k p q

Priority : Set
Priority = Nat

Rank : Set
Rank = Nat

data Maybe (A : Set) : Set where
  no : Maybe A
  yes : A -> Maybe A

min : Nat -> Nat -> Nat
--min zero zero = zero
--min zero (suc y) = zero
--min (suc x) zero = zero
--min (suc x) (suc y) = suc (min x y)
min n m with (decLeq n m)
... | inl nSmaller = n
... | inr mSmaller = m


_ : min 3 5 == 3
_ = refl

LeqSuc : (n : Nat) -> Leq n (suc n)
LeqSuc zero = <>
LeqSuc (suc n) = LeqSuc n

min-Leq-left : (n m : Nat) -> Leq (min n m) n
min-Leq-left zero zero = <>
min-Leq-left zero (suc m) = <>
min-Leq-left (suc n) zero = <>
--min-Leq-left (suc n) (suc m) = min-Leq-left n m
min-Leq-left (suc n) (suc m) with (decLeq (suc n) (suc m))
... | inl nSmaller = Leq-refl n
... | inr mSmaller = mSmaller

min-right-zero : (m : Nat) -> min m zero == zero
min-right-zero zero = refl
min-right-zero (suc m) = refl 

Leq-both-same : (n m : Nat) -> Leq n m -> Leq m n -> n == m
Leq-both-same zero zero proofL proofR = refl
Leq-both-same (suc n) (suc m) proofL proofR = ap suc (Leq-both-same n m proofL proofR)


min-symm : (n m : Nat) -> min n m == min m n
min-symm zero zero  = refl
min-symm (suc n) zero  = refl
min-symm zero (suc m)  = refl
--min-symm (suc n) (suc m) rewrite (min-symm n m) = refl
min-symm (suc n) (suc m) with (decLeq n m) | (decLeq m n)
... | inl nSmaller1 | inr nSmaller2 = refl
... | inr mSmaller2 | inl mSmaller1 = refl
... | inl nSmaller1 | inl mSmaller2 = ap suc (Leq-both-same n m nSmaller1 mSmaller2)
... | inr mSmaller1 | inr nSmaller2 = {!ap suc (Leq-both-same m n mSmaller1 nSmaller2)!}

min-Leq-right : (n m : Nat) -> Leq (min n m) m
min-Leq-right n m rewrite (min-symm n m) = min-Leq-left m n

leqLeqIsEq : (n m : Nat) -> Leq n m -> Leq m n -> n == m
leqLeqIsEq zero zero nLm mLn = refl
leqLeqIsEq (suc n) (suc m) nLm mLn rewrite (leqLeqIsEq n m nLm mLn) = refl
