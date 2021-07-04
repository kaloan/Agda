{-# OPTIONS --no-unicode #-}

module Homework.LeftistHeap.FullNoP where

open import Lib.Nat
open import Lib.One
open import Lib.Eq
open import Lib.List
open import Lib.Sum
open import Homework.LeftistHeap.Common

data Heap (lower : Priority) : Rank -> Set where
  empty : Heap lower zero
  node : {r1 r2 : Rank} -> Priority -> Heap lower r1 -> Heap lower r2 -> Heap lower (suc (r1 +N r2))

rank : {r : Rank} {p : Priority} -> Heap p r -> Priority
rank empty = 0
rank {r} {p} (node _ _ _) = r

weakenHeap : {r : Rank} (n m : Priority) -> Leq n m -> Heap m r -> Heap n r
weakenHeap {r} n m proof empty = empty
weakenHeap {r} n m proof (node {rL} {rR} p left right) = node {n} {rL} {rR} p (weakenHeap n m proof left) (weakenHeap n m proof right)

mkNode : {lr rr : Rank} {b : Priority} (p : Priority) -> Leq b p -> Heap p lr -> Heap p rr -> Heap b (suc (lr +N rr))
mkNode {lr} {rr} {b} p proof first second with (decLeq lr rr)
... | inl firstSmallerRank rewrite (+N-commut lr rr)= node b (weakenHeap b p proof second) (weakenHeap b p proof first)
... | inr secondSmallerRank = node b (weakenHeap b p proof first) (weakenHeap b p proof second)

{-# TERMINATING #-}
merge : {lr rr : Rank} {p : Priority} -> Heap p lr -> Heap p rr -> Heap p (lr +N rr)
merge {lr} {rr} {p} empty empty = empty {p}
merge {lr} {rr} {p} first empty rewrite (+N-right-zero lr) = first
merge {lr} {rr} {p} empty second rewrite (+N-commut 0 lr) | (+N-right-zero lr) = second
merge {lr} {rr} {p} first@(node {rLF} {rRF} pF lF rF) second@(node {rLS} {rRS} pS lS rS) with (decLeq pF pS)
... | inl pFSmaller rewrite (+N-assoc rLF rRF (suc (rLS +N rRS))) = mkNode {rLF} {rRF +N rr} {p} p (Leq-refl p) lF (merge rF second) 
... | inr pSSmaller rewrite (+N-right-suc (rLF +N rRF) (rLS +N rRS))
    | (+N-commut (rLF +N rRF) (rLS +N rRS))
    | (+N-assoc rLS rRS (rLF +N rRF))
    | (==-symm (+N-right-suc rLS (rRS +N rLF +N rRF)))
    | (==-symm (+N-right-suc rRS (rLF +N rRF)))
    = mkNode {rLS} {rRS +N lr} {p} p (Leq-refl p) lS (merge rS first)

singleton : (p x : Priority) -> Leq p x -> Heap p 1
singleton p x proof = node {p} x empty empty 

insert : {r : Rank} {p : Priority} (x : Priority) -> Heap p r -> Heap (min p x) (suc r)
insert {r} {p} x given = merge (singleton (min p x) x (min-Leq-right p x)) (weakenHeap (min p x) p (min-Leq-left p x) given)


findMin : {p : Priority} {r : Rank} -> Heap p (suc r) -> Priority
findMin {p} (node {rL} {rR} p2 left right) = p2

delMin : {p : Priority} {r : Rank} -> Heap p (suc r) -> Heap p r
delMin {p} (node {rL} {rR} p2 left right) = merge {rL} {rR} left right

minimum : List Priority -> Priority
minimum [] = zero
minimum (x ,- xs) = min x (minimum xs)

fromList : (xs : List Priority) -> Heap (minimum xs) (length xs)
fromList [] = empty {zero}
fromList (x ,- xs) rewrite (min-symm x (minimum xs)) = insert x (fromList xs)

