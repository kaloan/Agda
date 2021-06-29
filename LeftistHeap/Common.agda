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
min zero zero = zero
min zero (suc y) = zero
min (suc x) zero = zero
min (suc x) (suc y) = min x y

LeqSuc : (n : Nat) -> Leq n (suc n)
LeqSuc zero = <>
LeqSuc (suc n) = LeqSuc n

min-Leq-left : (n m : Nat) -> Leq (min n m) n
min-Leq-left zero zero = <>
min-Leq-left zero (suc m) = <>
min-Leq-left (suc n) zero = <>
min-Leq-left (suc n) (suc m) with (min-Leq-left n m)
... | z with (min n m)
... | minn = Leq-trans minn n (suc n) z (LeqSuc n)

min-right-zero : (m : Nat) -> min m zero == zero
min-right-zero zero = refl
min-right-zero (suc m) = refl 

min-symm : (n m : Nat) -> min n m == min m n
min-symm zero zero  = refl
min-symm (suc n) zero  = refl
min-symm zero (suc m)  = refl
min-symm (suc n) (suc m)  = min-symm n m


min-Leq-right : (n m : Nat) -> Leq (min n m) m
min-Leq-right n m rewrite (min-symm n m) = min-Leq-left m n
