{-# OPTIONS --no-unicode #-}

module Homework.LeftistHeap.Ranked where

open import Homework.LeftistHeap.Common
open import Lib.Sum
open import Lib.One
open import Lib.Zero
open import Lib.Nat
open import Lib.Eq

-- type index, since we will need it to vary for the different constructors
data Heap : Rank -> Set where
  empty : Heap 0
  node : {r1 r2 : Rank} -> Priority -> Heap r1 -> Heap r2 -> Heap (suc (r1 +N r2)) 

--Долното не работи, както и трябва
--wrongRank : Heap 1337
--wrongRank = node 0 empty empty

rightWrongRank : Heap 1
rightWrongRank = node 0 empty empty

--Това би трябвало да е така, с mkNode се грижим свойството на ранга да е в сила
wrongRankProp : Heap 2
wrongRankProp = node 0 empty (node 5 empty empty)


rightPriority : Heap 3
rightPriority = node 5 (node 10 empty empty) (node 6 empty empty)

wrongPriority : Heap 2
wrongPriority = node 5 (node 1 empty empty) empty 

rank : {r : Rank} -> Heap r -> Rank
rank {.0} empty = zero 
rank {r} (node p left right) = r
--rank empty = 0
--rank (node p left right) = suc (rank left +N rank right )

rankSame : {r : Rank} -> (given : Heap r) -> rank given == r
rankSame {.0} empty = refl
rankSame (node x given1 given2) = refl

mkNode :
  {lr rr : Rank} ->
  Priority -> Heap lr -> Heap rr -> Heap (suc (lr +N rr))
mkNode {lr} {rr} p first second with decLeq (rank first) (rank second)
... | inl firstSmallerRank rewrite (+N-commut lr rr) = node p second first
... | inr secondSamllerRank = node p first second
--... | inl firstSmallerRank rewrite (+N-commut lr rr)  = {!node p second first!}
--... | inr 
--... | inr 



{-# TERMINATING #-}
merge :
  {lr rr : Rank} ->
  Heap lr -> Heap rr -> Heap (lr +N rr)
merge {rr} empty second = second
merge {lr} first empty rewrite (+N-right-zero lr) = first
--merge first@(node pF lF rF) second@(node pS lS rS) = {!!}
--merge first@(node pF lF rF) second@(node pS lS rS) with (rank lF)
--... | rLF rewrite (rankSame lF) = {!!}

merge {ll} {rr} first@(node {rLF} {rRF} pF lF rF) second@(node {rLS} {rRS} pS lS rS) with (decLeq pF pS)
... | inl pFSmaller rewrite (+N-assoc rLF rRF (suc (rLS +N rRS))) = mkNode pF lF (merge rF second)
--... | inr pSSmaller = {!mkNode pS lS (merge rS first)!}
... | inr pSSmaller rewrite (+N-right-suc (rLF +N rRF) (rLS +N rRS))
    | (+N-commut (rLF +N rRF) (rLS +N rRS))
    | (+N-assoc rLS rRS (rLF +N rRF))
    | (==-symm (+N-right-suc rLS (rRS +N rLF +N rRF)))
    | (==-symm (+N-right-suc rRS (rLF +N rRF)))
    --| (+N-right-suc rRS (rLF +N rRF))
    = mkNode pS lS (merge rS first)
--... | inr pSSmaller rewrite (+N-commut (rLF +N rRF) (rLS +N rRS))
--  | (+N-assoc rLS rRS (rLF +N rRF))
--  | (+N-right-suc rLS (rRS +N (suc (rLF +N rRF))))
--  = {!mkNode pS lS (merge rS first)!}
 
--... | rLF rewrite (rankSame lF) with (rank rF)
--... | rRF rewrite (rankSame rF) with (rank lS)
--... | rLS rewrite (rankSame lS) with (rank rS)
--... | rRS rewrite (rankSame rS) with decLeq pF pS
--merge first@(node pF (Heap r1) (Heap r2)) second@(node pS (Heap r3) (Heap r4)) with decLeq pF pS
--... | inl pFSmaller rewrite (+N-assoc rLF rRF (suc (rLS +N rRS))) | (rankSame lF) = {!mkNode pF lF (merge rF second)!}
--... | inr pSSmaller rewrite (+N-commut (rLF +N rRF) (suc (rLS +N rRS))) | (+N-assoc rLS rRS (suc (rLF +N rRF)))= {!mkNode pS lS (merge rF first)!}


--insert не баца с горното, но е ОК с долното??
--singleton : {r : Rank} -> Priority -> Heap 1
singleton : Priority -> Heap 1
singleton p = node p empty empty

--Безсмислено
--insertSingleton : {r : Rank} -> Heap r -> Heap 1 -> Heap (r +N 1)
--insertSingleton {r} first second = merge first second


insert : {r : Rank} -> Priority -> Heap r -> Heap (suc r)
--insert p given = merge given (singleton p)
insert {r} p given = merge (singleton p) given
--insert {r} p given rewrite (+N-right-suc r 0) | (+N-right-zero r) = merge given (singleton p)


findMin : {r : Rank} -> Heap (suc r) -> Priority
findMin (node p _ _) = p

delMin : {r : Rank} -> Heap (suc r) -> Heap r
delMin (node p left right) = merge left right
