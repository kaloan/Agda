{-# OPTIONS --no-unicode #-}

module Homework.LeftistHeap.FullTURNIN where

open import Lib.Nat
open import Lib.One
open import Lib.Eq
open import Lib.List
open import Lib.Sum
open import Homework.LeftistHeap.Common

data Heap (lower : Priority) : Rank -> Set where
  empty : Heap lower zero
  node : {r1 r2 : Rank} -> (p : Priority) -> Leq r2 r1 -> Leq lower p -> Heap p r1 -> Heap p r2 -> Heap lower (suc (r1 +N r2))

rank : {r : Rank} {p : Priority} -> Heap p r -> Priority
rank empty = 0
rank {r} (node p _ _ _ _) = r

weakenHeap : {r : Rank} (n m : Priority) -> Leq n m -> Heap m r -> Heap n r
weakenHeap {r} n m proof empty = empty
weakenHeap {r} n m proof (node {rL} {rR} p proofR proofP left right) = node {n} {rL} {rR} p proofR (Leq-trans n m p proof proofP) left right

mkNode : {lr rr : Rank} {b : Priority} (p : Priority) -> Leq b p -> Heap p lr -> Heap p rr -> Heap b (suc (lr +N rr))
mkNode {lr} {rr} {b} p proof first second with (decLeq lr rr)
... | inl firstSmallerRank rewrite (+N-commut lr rr)= node {b} p firstSmallerRank proof second first
... | inr secondSmallerRank = node {b} p secondSmallerRank proof first second

{-# TERMINATING #-}
merge : {lr rr : Rank} {p : Priority} -> Heap p lr -> Heap p rr -> Heap p (lr +N rr)
merge {lr} {rr} {p} empty empty = empty {p}
merge {lr} {rr} {p} first empty rewrite (+N-right-zero lr) = first
merge {lr} {rr} {p} empty second rewrite (+N-commut 0 lr) | (+N-right-zero lr) = second
merge {lr} {rr} {p} first@(node {rLF} {rRF} pF proofRF proofPF lF rF) second@(node {rLS} {rRS} pS proofRS proofPS lS rS) with (decLeq pF pS)
... | inl pFSmaller rewrite (+N-assoc rLF rRF (suc (rLS +N rRS))) = mkNode {rLF} {rRF +N rr} {p} pF proofPF lF (merge rF (node {pF} {rLS} {rRS} pS proofRS pFSmaller lS rS)) 
... | inr pSSmaller rewrite (+N-right-suc (rLF +N rRF) (rLS +N rRS))
    | (+N-commut (rLF +N rRF) (rLS +N rRS))
    | (+N-assoc rLS rRS (rLF +N rRF))
    | (==-symm (+N-right-suc rLS (rRS +N rLF +N rRF)))
    | (==-symm (+N-right-suc rRS (rLF +N rRF)))
    = mkNode {rLS} {rRS +N lr} {p} pS proofPS lS (merge rS (node {pS} {rLF} {rRF} pF proofRF pSSmaller lF rF))

singleton : (p x : Priority) -> Leq p x -> Heap p 1
singleton p x proof = node {p} x <> proof empty empty 

insert : {r : Rank} {p : Priority} (x : Priority) -> Heap p r -> Heap (min p x) (suc r)
insert {r} {p} x given = merge (singleton (min p x) x (min-Leq-right p x)) (weakenHeap (min p x) p (min-Leq-left p x) given)


findMin : {p : Priority} {r : Rank} -> Heap p (suc r) -> Priority
findMin {p} (node {rL} {rR} p2 _ _ left right) = p2

delMin : {p : Priority} {r : Rank} -> Heap p (suc r) -> Heap p r
delMin {p} (node {rL} {rR} p2 _ proofP left right) = merge {rL} {rR} (weakenHeap p p2 proofP left) (weakenHeap p p2 proofP right)

minimum : List Priority -> Priority
minimum [] = zero
minimum (x ,- xs) = min x (minimum xs)

fromList : (xs : List Priority) -> Heap (minimum xs) (length xs)
fromList [] = empty {zero}
fromList (x ,- xs) rewrite (min-symm x (minimum xs)) = insert x (fromList xs)

