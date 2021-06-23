{-# OPTIONS --no-unicode #-}

module Homework.Bin where

import Lib.Nat as Nat
open Nat using (Nat; _+N_)
open import Lib.Eq
open import Lib.Sigma
open import Lib.Zero
open import Lib.One


data Bin : Set where
  end : Bin
  _O : Bin -> Bin
  _I : Bin -> Bin

infixr 12 _O
infixr 12 _I

_ : Bin
_ = end I O I

suc : Bin -> Bin
suc end = end I
suc (x O) = x I
suc (x I) = (suc x) O


_ : suc end == end I
_ = refl

_ : suc (end I I) == end I O O
_ = refl

toNat : Bin -> Nat
toNat end = 0
toNat (x O) = toNat x +N toNat x
--toNat (x I) = (toNat x +N toNat x) +N 1
toNat (x I) = Nat.suc (toNat x +N toNat x)


_ : toNat (end I I I) == 7
_ = refl

_ : toNat (end I I O) == 6
_ = refl

_ : toNat (end O) == 0
_ = refl

_ : toNat end == 0
_ = refl

fromNat : Nat -> Bin
fromNat Nat.zero = end
fromNat (Nat.suc x) = suc (fromNat x)

_ : fromNat 0 == end
_ = refl

_ : fromNat 1 == end I
_ = refl

_ : fromNat 8 == end I O O O
_ = refl



+N-left-suc : (n m : Nat) -> Nat.suc n +N m == Nat.suc(n +N m)
+N-left-suc n Nat.zero = refl
+N-left-suc n (Nat.suc m) = refl


toNat-suc : (b : Bin) -> toNat (suc b) == Nat.suc (toNat b)
toNat-suc end = refl
toNat-suc (b O) = refl
toNat-suc (b I) rewrite (toNat-suc b) = ap Nat.suc (Nat.+N-right-suc (toNat b) (toNat b)) 
--toNat-suc (b I) rewrite (toNat-suc b) = {!subst Nat.suc (Nat.+N-right-suc)!} 

--toNat-suc (b I) = {!toNat-suc b!}
--toNat-suc (b I) = {!ap Nat.+N-right-suc (toNat (suc b)) (toNat (suc b)) !}
--toNat-suc end = toNat(end I) == Nat.suc (0)
--toNat-suc end = toNat(suc end) == Nat.suc (toNat end)
--toNat-suc (b O) = toNat(b I) == Nat.suc ((toNat b +N toNat b) +N 1)
--toNat-suc (b I) = toNat((suc b) 0) == Nat.suc (toNat (suc b) +N toNat (suc b))


to-from-id : (n : Nat) -> toNat (fromNat n) == n
to-from-id Nat.zero = refl
to-from-id (Nat.suc n) rewrite (to-from-id n) | (toNat-suc (fromNat n)) | (to-from-id n) = refl

--С горното показваме, че долното не е вярно
--to-from-counterexample : Nat >< \n -> toNat (fromNat n) == n -> Zero

from-to-counterexample : Bin >< \b -> fromNat (toNat b) == b -> Zero
--from-to-counterexample = {! Lib.Sigma._><_._,_!}
--from-to-counterexample = {!_><_._,_ (end O) (\b -> fromNat (toNat b) == b)!}
--from-to-counterexample = (end O) , \ x -> {!x!}
from-to-counterexample = (end O) , \ ()
--from-to-counterexample = (end O), (\b -> fromNat (toNat b) == b -> Zero)
--from-to-counterexample = (end O),  (fromNat (toNat (end O)) == (end O))

--from-to-counterexample (end O) ()
--free-to-conterexample (freeNat (toNat (end O))) == end O

data LeadingOne : Bin -> Set where
  endI : LeadingOne (end I)
  _O : {b : Bin} -> LeadingOne b -> LeadingOne (b O)
  _I : {b : Bin} -> LeadingOne b -> LeadingOne (b I)

data Can : Bin -> Set where
  end : Can end
  leadingOne : {b : Bin} -> LeadingOne b -> Can b

suc-LeadingOne : (b : Bin) -> LeadingOne b -> LeadingOne (suc b)
suc-LeadingOne .(end I) endI = endI O
suc-LeadingOne .(_ O) (x O) = x I
suc-LeadingOne (b I) (x I) with (suc-LeadingOne b x)
... | z = z O
--suc-LeadingOne (x I) (b I) with LeadingOne (suc (x I))
--... | z = {!z!}
--suc-LeadingONe .(x I) ({x} b I) = ?
--suc-LeadingOne .(b I) ({b} (LeadingOne b) I) = ?
--suc-LeadingOne .(_ I) (b I) = (suc b) O
--suc-LeadingOne .(_ I) (b I) = suc-LeadingOne b O
--suc-LeadingOne .(_ I) (b I) = suc-LeadingOne b O
--suc-LeadingOne .(_ I) (b I) rewrite (LeadingOne b) = ?


suc-Can : (b : Bin) -> Can b -> Can (suc b)
suc-Can .(end) end = leadingOne (endI)
suc-Can (b O) (leadingOne x) with (suc-LeadingOne (b O) x)
... | z = leadingOne z
suc-Can (b I) (leadingOne x) with (suc-LeadingOne (b I) x)
... | z = leadingOne z
--suc-Can (leadingOne (b O))




fromNat-Can : (n : Nat) -> Can (fromNat n)
fromNat-Can Nat.zero = end
--fromNat-Can (Nat.suc n) rewrite (suc-Can (fromNat n) (fromNat-Can n)) = ?
fromNat-Can (Nat.suc n) = suc-Can (fromNat n) (fromNat-Can n) 
--fromNat-Can (Nat.suc n) = {!suc-Can (fromNat n) (leadingOne (LeadingOne (fromNat n)))!}


_+B_ : Bin -> Bin -> Bin
--_+B_ x y = fromNat(toNat x +N toNat y)
x +B end = x
end +B y = y
x O +B y O = (x +B y) O
x I +B y O = (x +B y) I
x O +B y I = (x +B y) I
--Възможна грешка, не работи на някои примери при suc(x +B y) или (suc x +B y). Друг начин?
x I +B y I = (x +B suc y) O



infixr 11 _+B_

_ : end +B end I I I I == end I I I I
_ = refl

_ : end I O O +B end == end I O O
_ = refl

_ : end I I +B end I I I I == end I O O I O
_ = refl

_ : end I I I +B end I O I == end I I O O
_ = refl

--Не е в сила, ако дефинираме чрез fromNat от сумата
+B-right-end : (b : Bin) -> b +B end == b
+B-right-end b = refl

+B-right-suc : (b v : Bin) -> b +B suc v == suc (b +B v)
+B-right-suc end end = refl
+B-right-suc end (v O) = refl
+B-right-suc end (v I) = refl
+B-right-suc (b O) end = refl
+B-right-suc (b I) end rewrite (+B-right-suc b end) = refl
+B-right-suc (b O) (v O) = refl
+B-right-suc (b O) (v I) rewrite (+B-right-suc b v) = refl
+B-right-suc (b I) (v O) rewrite (+B-right-suc b v) = refl
+B-right-suc (b I) (v I) = refl

--Трябва ми за за два случая отдолу
+B-left-end : (b : Bin) -> end +B b == b
+B-left-end end = refl
+B-left-end (b O) = refl
+B-left-end (b I) = refl

+B-left-suc : (b v : Bin) -> (suc b) +B v == suc (b +B v)
+B-left-suc b end = refl
+B-left-suc end (v O) = ap Bin._I (+B-left-end v)
+B-left-suc end (v I) = ap Bin._O (+B-left-end (suc v))
+B-left-suc (b O) (v O) = refl
--+B-left-suc (b O) (v O) = (b I) +B (v O)
+B-left-suc (b I) (v O) rewrite (+B-left-suc b v) = refl
+B-left-suc (b O) (v I) rewrite (+B-right-suc b v) = refl
+B-left-suc (b I) (v I) rewrite (+B-left-suc b v) | (+B-right-suc b v) = refl
--+B-left-suc b (v I) = {!!}
--+B-left-suc = {!x y!}
--+B-left-suc b (y O)



fromNat-+N-+B-commutes : (n m : Nat) -> fromNat (n +N m) == fromNat n +B fromNat m
fromNat-+N-+B-commutes Nat.zero Nat.zero = refl
fromNat-+N-+B-commutes Nat.zero (Nat.suc m) rewrite (+B-left-end (suc (fromNat m))) = refl
fromNat-+N-+B-commutes (Nat.suc n) Nat.zero rewrite (Nat.+N-right-zero n) = refl
fromNat-+N-+B-commutes (Nat.suc n) (Nat.suc m) rewrite (Nat.+N-right-suc n m) | (+B-left-suc (fromNat n) (suc (fromNat m))) | (+B-right-suc (fromNat n) (fromNat m)) | (fromNat-+N-+B-commutes n m) = refl

+B-same-shift : (b : Bin) -> LeadingOne b -> b +B b == b O
+B-same-shift .(end I) endI = refl
+B-same-shift (b O) (x O) = ap _O (+B-same-shift b x)
+B-same-shift (b I) (x I) rewrite (+B-right-suc b b) | (+B-same-shift b x) = refl
--+B-same-shift (b I) (x I) rewrite (+B-right-suc b b) = {!ap Bin._O (+B-same-shift (suc b O) ((suc b) O))!}
--+B-same-shift (b O) = {!ap (Bin._O) (+B-same-shift b == (b O))!}
--+B-same-shift (b O) = {!ap (Bin._O) (+B-same-shift b == (b O))!}
--+B-same-shift (b O) = {!cong Bin._O (+B-same-shift b)!}
--+B-same-shift (b I) = {!+B-same-shift b!}


--revSideLeadingOne : {b : Bin} -> LeadingOne (b O) -> LeadingOne b
--revSideLeadingOne {b} x rewrite (LeadingOne._O ?) = {!!}


from-to-id-Can : (b : Bin) -> Can b -> fromNat (toNat b) == b
from-to-id-Can .(end) end = refl
--from-to-id-Can (b O) (leadingOne x) rewrite (fromNat-+N-+B-commutes (toNat b) (toNat b)) = {!!}
from-to-id-Can (b O) (leadingOne x) rewrite (fromNat-+N-+B-commutes (toNat b) (toNat b)) | (from-to-id-Can b _ ) | (+B-same-shift b _ ) = refl
--from-to-id-Can (b I) (leadingOne x) rewrite (fromNat-+N-+B-commutes (toNat b) (toNat b)) | (from-to-id-Can b _ ) | (+B-same-shift b _ ) = refl
from-to-id-Can (b I) (leadingOne x) rewrite (fromNat-+N-+B-commutes (toNat b) (toNat b)) | (from-to-id-Can b _ ) | (+B-same-shift b _ ) = refl

--from-to-id-Can (b I) (leadingOne x) rewrite (from-to-id-Can b _) = {!!}
--from-to-id-Can (b O)
