{-# OPTIONS --no-unicode #-}

module Homework.LeftistHeap.OrderedTURNIN where

open import Lib.Sum
open import Lib.One
open import Homework.LeftistHeap.Common
open import Lib.Nat

-- parametrised by the lower bound of the heap
data Heap (lower : Priority) : Set where
  empty : Heap lower 
  node :  Rank -> (p : Priority) -> Leq lower p -> Heap p -> Heap p -> Heap lower   


rightRankProperty : Heap 0
rightRankProperty = node {0} 2 3 <> (node {3} 1 5 <> empty empty) empty



wrongRankProperty : Heap 300
wrongRankProperty = node {300} 2 400 <> empty (node {400} 1 500 <>  empty empty)

wrongRank : Heap 5
wrongRank = node {5} 4 8 <> empty empty


--Оправено
--wrongPriority : Heap 1
--wrongPriority = node {1} 1 9001 empty empty 



rank : {lower : Priority} -> Heap lower -> Rank
rank empty = 0
rank (node r _ _ _ _) = r 

weakenHeap : (n m : Priority) -> Leq n m -> Heap m -> Heap n
weakenHeap n m proof empty = empty {n}
weakenHeap n m proof (node r p proofNode left right)
  = node {n} r p (Leq-trans n m p proof proofNode) left right

mkNode :
  {lower : Priority} (x : Priority) ->
  Leq lower x -> Heap x -> Heap x -> Heap lower
mkNode {lower} p proof first second with (decLeq (rank first) (rank second))
... | inl firstSmallerRank
  = node {lower} (suc (rank first +N rank second)) p proof second first
... | inr secondSmallerRank
  = node {lower} (suc (rank first +N rank second)) p proof first second

{-# TERMINATING #-}
merge :
  {lower : Priority} ->
  Heap lower -> Heap lower -> Heap lower
merge {lower} empty empty = empty {lower}
merge {lower} first empty = first
merge {lower} empty second = second
--merge {lower} first@(node {pFL} {pFR} rankF pF lF rF) second@(node {pSL} {pSR} rankS pS lS rS) with (decLeq pF pS)
merge {lower} first@(node rankF pF proofF lF rF) second@(node rankS pS proofS lS rS) with (decLeq pF pS)
... | inl pFSmaller = mkNode {lower} pF proofF lF (merge rF (node {pF} rankS pS pFSmaller lS rS))
... | inr pSSmaller = mkNode {lower} pS proofS lS (merge rS (node {pS} rankS pF pSSmaller lF rF))


singleton : {lower : Priority} (x : Priority) -> Leq lower x -> Heap lower
singleton {lower} x proof = node {lower} 1 x proof empty empty


insert : {lower : Priority} (x : Priority) -> Heap lower -> Heap (min lower x)
insert {lower} x given
  = merge (singleton {min lower x} x (min-Leq-right lower x)) (weakenHeap (min lower x) lower (min-Leq-left lower x) given)

findMin : {lower : Priority} -> Heap lower -> Maybe Priority
findMin empty = no
findMin (node rankN p proof left right) = yes p

delMin : {lower : Priority} -> Heap lower -> Maybe (Heap lower)
delMin empty = no
delMin {lower} (node rankN p proof left right) = yes (merge (weakenHeap lower p proof left) (weakenHeap lower p proof right))

