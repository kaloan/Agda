{-# OPTIONS --no-unicode #-}

module Homework.LeftistHeap.Ordered where

open import Lib.Sum
open import Lib.One
open import Homework.LeftistHeap.Common
open import Lib.Nat

-- parametrised by the lower bound of the heap
data Heap (lower : Priority) : Set where
  empty : Heap lower 
  node : {p1 p2 : Priority} -> Rank -> Priority -> Heap p1 -> Heap p2 -> Heap lower   
  --node : {p1 p2 : Priority} -> Rank -> Priority -> (Leq lower p1) -> Heap p1 -> (Leq lower p2) -> Heap p2 -> Heap lower   

rightRankProperty : Heap 0
rightRankProperty = node {0} {2} {1} 2 0 (node {2} {15} {17} 1 2 empty empty) empty

wrongRankProperty : Heap 300
wrongRankProperty = node {300} {400} {500} 2 300 empty (node {500} {600} {700} 1 500 empty empty)

wrongRank : Heap 5
wrongRank = node {5} {2} {1} 4 5 empty empty


--Не е проблем с mkNode се грижим да е изпълнено
wrongPriority : Heap 1
wrongPriority = node {1} {0} {0} 1 9001 empty empty 



rank : {lower : Priority} -> Heap lower -> Rank
rank empty = 0
rank (node r _ _ _) = r


mkNode :
  {lower : Priority} (x : Priority) ->
  Leq lower x -> Heap x -> Heap x -> Heap lower
mkNode {lower} p proof first second with (decLeq (rank first) (rank second))
... | inl firstSmallerRank = node {lower} (suc (rank first +N rank second)) lower second first
... | inr secondSmallerRank = node {lower} (suc (rank first +N rank second)) lower first second

{-# TERMINATING #-}
merge :
  {lower : Priority} ->
  Heap lower -> Heap lower -> Heap lower
merge = {!!}

singleton : {lower : Priority} (x : Priority) -> Leq lower x -> Heap lower
singleton {lower} x proof = node {lower} {x} {x} 0 lower empty empty

weakenHeap : (n m : Priority) -> Leq n m -> Heap {!!} -> Heap {!!}
weakenHeap = {!!}

insert : {lower : Priority} (x : Priority) -> Heap lower -> Heap lower
insert {lower} x given = {!merge!}

findMin : {lower : Priority} -> Heap lower -> Maybe Priority
findMin = {!!}

delMin : {lower : Priority} -> Heap lower -> Maybe (Heap lower)
delMin = {!!}
