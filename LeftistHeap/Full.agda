{-# OPTIONS --no-unicode #-}

module Homework.LeftistHeap.Full where

open import Lib.Nat
open import Lib.One
open import Lib.Eq
open import Lib.List
open import Lib.Sum
open import Homework.LeftistHeap.Common

data Heap (lower : Priority) : Rank -> Set where
  empty : Heap lower zero
  node : {p1 p2 : Priority} {r1 r2 : Rank} -> Priority -> Heap p1 r1 -> Heap p2 r2 -> Heap lower (suc (r1 +N r2))

mkNode : {lr rr : Rank} {b : Priority} (p : Priority) -> Leq b p -> Heap p lr -> Heap p rr -> Heap b (suc (lr +N rr))
mkNode {lr} {rr} {b} p proof first second with (decLeq lr rr)
... | inl firstSmallerRank rewrite (+N-commut lr rr)= node b second first
... | inr secondSmallerRank = node b first second

{-# TERMINATING #-}
merge : {lr rr : Rank} {p : Priority} -> Heap p lr -> Heap p rr -> Heap p (suc (lr +N rr))
merge = {!!}

weakenHeap : {r : Rank} (n m : Priority) -> Leq n m -> Heap {!!} r -> Heap {!!} r
weakenHeap = {!!}

singleton : (p x : Priority) -> Leq p x -> Heap p 1
singleton p x proof = node {p} {x} {x} p empty empty 

insert : {r : Rank} {p : Priority} (x : Priority) -> Heap p r -> Heap (min p x) (suc r)
insert {p} x given = {!merge (singleton x) given!}

findMin : {p : Priority} {r : Rank} -> Heap p {!!} -> Priority
findMin = {!!}

delMin : {p : Priority} {r : Rank} -> Heap p (suc r) -> Heap p r
delMin {p} (node {pL} {pR} {rL} {rR} p2 left right) = {!merge {rL} {rR} {pR} left right!}

minimum : List Priority -> Priority
minimum [] = zero
minimum (x ,- xs) = min x (minimum xs)

fromList : (xs : List Priority) -> Heap (minimum xs) (length xs)
fromList [] = empty {zero}
fromList (x ,- xs) rewrite (min-symm x (minimum xs)) = insert x (fromList xs)
--fromList (x ,- xs) rewrite (==-symm (min-right-zero x)) | (min-symm x zero) = {!insert x (fromList xs)!}
