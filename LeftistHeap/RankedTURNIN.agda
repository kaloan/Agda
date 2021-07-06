{-# OPTIONS --no-unicode #-}

module Homework.LeftistHeap.RankedTURNIN where

open import Homework.LeftistHeap.Common
open import Lib.Sum
open import Lib.One
open import Lib.Zero
open import Lib.Nat
open import Lib.Eq

-- type index, since we will need it to vary for the different constructors
data Heap : Rank -> Set where
  empty : Heap 0
  node : {r1 r2 : Rank} -> Leq r2 r1 -> Priority -> Heap r1 -> Heap r2 -> Heap (suc (r1 +N r2)) 

--Долното не работи, както и трябва
--wrongRank : Heap 1337
--wrongRank = node <> 0 empty empty

rightWrongRank : Heap 1
rightWrongRank = node <> 0 empty empty

--Долното не работи, както и трябва
--wrongRankProp : Heap 2
--wrongRankProp = node <> 0 empty (node 5 empty empty)


rightPriority : Heap 3
rightPriority = node <> 5 (node <> 10 empty empty) (node <> 6 empty empty)

wrongPriority : Heap 2
wrongPriority = node <> 5 (node <> 1 empty empty) empty 


rank : {r : Rank} -> Heap r -> Rank
rank {.0} empty = zero 
rank {r} (node p _ left right) = r

mkNode :
  {lr rr : Rank} ->
  Priority -> Heap lr -> Heap rr -> Heap (suc (lr +N rr))
mkNode {lr} {rr} p first second with decLeq lr rr
... | inl firstSmallerRank rewrite (+N-commut lr rr) = node firstSmallerRank p second first
--node p second first
... | inr secondSamllerRank = node secondSamllerRank p first second
--node p first second



{-# TERMINATING #-}
merge :
  {lr rr : Rank} ->
  Heap lr -> Heap rr -> Heap (lr +N rr)
merge {.0} {.0} empty empty = empty
merge {.0} {rr} empty second = second
merge {lr} first empty rewrite (+N-right-zero lr) = first
merge {ll} {rr} first@(node {rLF} {rRF} proofF pF lF rF) second@(node {rLS} {rRS} proofS pS lS rS) with (decLeq pF pS)
... | inl pFSmaller rewrite (+N-assoc rLF rRF (suc (rLS +N rRS))) = mkNode pF lF (merge rF second)
... | inr pSSmaller rewrite (+N-right-suc (rLF +N rRF) (rLS +N rRS))
    | (+N-commut (rLF +N rRF) (rLS +N rRS))
    | (+N-assoc rLS rRS (rLF +N rRF))
    | (==-symm (+N-right-suc rLS (rRS +N rLF +N rRF)))
    | (==-symm (+N-right-suc rRS (rLF +N rRF)))
    = mkNode pS lS (merge rS first)
    


singleton : Priority -> Heap 1
singleton p = node <> p empty empty


insert : {r : Rank} -> Priority -> Heap r -> Heap (suc r)
insert {r} p given = merge (singleton p) given

findMin : {r : Rank} -> Heap (suc r) -> Priority
findMin (node _ p _ _) = p

delMin : {r : Rank} -> Heap (suc r) -> Heap r
delMin (node _ p left right) = merge left right
