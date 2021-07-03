{-# OPTIONS --no-unicode #-}

module Homework.LeftistHeap.OrderedNoP where

open import Lib.Sum
open import Lib.One
open import Homework.LeftistHeap.Common
open import Lib.Nat

-- parametrised by the lower bound of the heap
data Heap (lower : Priority) : Set where
  empty : Heap lower 
  node : Rank -> Priority -> Heap lower -> Heap lower -> Heap lower   
  --node : {p1 p2 : Priority} -> Rank -> Priority -> (Leq lower p1) -> Heap p1 -> (Leq lower p2) -> Heap p2 -> Heap lower   

rightRankProperty : Heap 0
rightRankProperty = node {0} 2 0 (node {0} 1 2 empty empty) empty

wrongRankProperty : Heap 300
wrongRankProperty = node {300}  2 300 empty (node {300} 1 500 empty empty)

wrongRank : Heap 5
wrongRank = node {5} 4 5 empty empty


--Не е проблем с mkNode се грижим да е изпълнено
wrongPriority : Heap 1
wrongPriority = node {1} 1 9001 empty empty 



rank : {lower : Priority} -> Heap lower -> Rank
rank empty = 0
rank (node r _ _ _) = r

weakenHeap : (n m : Priority) -> Leq n m -> Heap m -> Heap n
weakenHeap n m proof empty = empty {n}
weakenHeap n m proof (node r p left right) = node {n} r p (weakenHeap n m proof left) (weakenHeap n m proof right) 

mkNode :
  {lower : Priority} (x : Priority) ->
  Leq lower x -> Heap x -> Heap x -> Heap lower
mkNode {lower} p proof first second with (decLeq (rank first) (rank second))
... | inl firstSmallerRank = node {lower} (suc (rank first +N rank second)) p (weakenHeap lower p proof second) (weakenHeap lower p proof first)
... | inr secondSmallerRank = node {lower} (suc (rank first +N rank second)) p (weakenHeap lower p proof first) (weakenHeap lower p proof second)

{-# TERMINATING #-}
merge :
  {lower : Priority} ->
  Heap lower -> Heap lower -> Heap lower
merge {lower} empty empty = empty {lower}
merge {lower} first empty = first
merge {lower} empty second = second
--merge {lower} first@(node {pFL} {pFR} rankF pF lF rF) second@(node {pSL} {pSR} rankS pS lS rS) with (decLeq pF pS)
merge {lower} first@(node rankF pF lF rF) second@(node rankS pS lS rS) with (decLeq pF pS)
... | inl pFSmaller = mkNode {lower} lower (Leq-refl lower) lF (merge rF second)
... | inr pSSmaller = mkNode {lower} lower (Leq-refl lower) lS (merge rS first)

singleton : {lower : Priority} (x : Priority) -> Leq lower x -> Heap lower
singleton {lower} x proof = node {lower} 1 x empty empty


insert : {lower : Priority} (x : Priority) -> Heap lower -> Heap (min lower x)
insert {lower} x given
  = merge (singleton {min lower x} x (min-Leq-right lower x)) (weakenHeap (min lower x) lower (min-Leq-left lower x) given)

findMin : {lower : Priority} -> Heap lower -> Maybe Priority
findMin empty = no
findMin (node rankN p left right) = yes p

delMin : {lower : Priority} -> Heap lower -> Maybe (Heap lower)
delMin empty = no
delMin (node rankN p left right) = yes (merge left right)
