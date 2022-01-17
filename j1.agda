{-# OPTIONS --without-K --safe #-}

open import Axiom.UniquenessOfIdentityProofs
open import Data.Bool.Base using (Bool; false; true; not)
open import Data.Bool.Properties using (_≟_)
open import Data.Fin.Base using (Fin; zero; suc; toℕ; fromℕ<)
open import Data.Fin.Properties using (fromℕ<-toℕ; toℕ-fromℕ<; toℕ<n; toℕ-injective)
open import Data.Unit.Base using (⊤; tt)
open import Data.List.Base using (List; map; _++_; []; _∷_; length; lookup)
open import Data.List.Properties using (length-map)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; z≤n; s≤s; _<_; _<ᵇ_)
open import Data.Nat.Properties using (<-irrelevant; ≤-trans; ≤-reflexive; ≡-irrelevant; <-transˡ; ≤-pred)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; cong; trans ; subst; sym)




------ The solution ------
-- The goal is to output the number of times a list "increases", i.e. where two consecutive entries in a list are in increasing order.

biggerThanHead : ℕ -> List ℕ -> Bool
biggerThanHead n [] = false
biggerThanHead n (x ∷ l) = n <ᵇ x

countIncrease : List ℕ  -> ℕ
countIncrease [] = 0
countIncrease (x ∷ l) with (biggerThanHead x l) 
countIncrease (x ∷ l) | true = suc (countIncrease l)
countIncrease (x ∷ l) | false = countIncrease l 


------  Proof that the solution is correct ------

-- First we define what is "an increase" in a list `l`: it is a way to split `l` into `(l1 ++ (a ∷ b ∷ l2))`, with `a < b`. 
-- We denote by `Increase l` the set of all the increases in `l`.
data Increase : List ℕ -> Set where
    inc : (l1 l2 : List ℕ) (a b : ℕ) (Hab : a < b) -> Increase (l1 ++ (a ∷ b ∷ l2))
    


-- The goal is now to prove that there is a bijection between `Increase l` and the set with `countIncrease l` elements, denoted `Fin (countIncrease l)`.
-- We split this  into two parts. First we give an alternative definition of the increases in `l`, denoted `Increases' l`, more adapted to the `List` structure. 
-- Then we show that this set is in bijection with both `Increase l` and `Fin (countIncrease l)`.

data Increase' : List ℕ -> Set where
    bigger : (l : List ℕ) (a : ℕ) (Hal : (biggerThanHead a l) ≡ true) -> Increase' (a ∷ l)
    cons-inc : (l : List ℕ) (a : ℕ) (i : Increase' l) -> Increase' (a ∷ l)


record is-bijection {A B : Set} (f : A -> B) : Set where
    field inv : B -> A 
    field f-inv : (b : B) -> f (inv b) ≡ b 
    field inv-f : (a : A) -> inv (f a) ≡ a

record are-in-bijection (A B : Set) : Set where 
    field f : A -> B 
    field is-bij : is-bijection f

-- This is an idiom which will be useful throughout the proofs.

data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
inspect x = x with≡ refl

-- We start by some useful lemmas about Increase and Increase'.

increase'++ : (l1 l2 : List ℕ) (i : Increase' l1) -> Increase' (l2 ++ l1)
increase'++ l1 [] i = i
increase'++ l1 (x ∷ l2) i = cons-inc (l2 ++ l1) x (increase'++ l1 l2 i)

cons-increase : (n : ℕ) (l : List ℕ) (k : Increase l) -> Increase (n ∷ l)
cons-increase n .(l1 ++ a ∷ b ∷ l2) (inc l1 l2 a b Hab) = inc (n ∷ l1) l2 a b Hab

increase++ : (l1 l2 : List ℕ) (i : Increase l1) -> Increase (l2 ++ l1)
increase++ l1 [] i = i
increase++ l1 (x ∷ l2) i = cons-increase x (l2 ++ l1) (increase++ l1 l2 i)

increase++nil : (a b : ℕ) (l1 l2 : List ℕ) (H : a < b) -> increase++ (a ∷ b ∷ l2) l1 (inc [] l2 a b H) ≡ inc l1 l2 a b H
increase++nil a b [] l2 H = refl
increase++nil a b (x ∷ l1) l2 H = cong (cons-increase x (l1 ++ a ∷ b ∷ l2)) (increase++nil a b l1 l2 H)

<⇒<ᵇ : ∀ {m n} → m < n → (m <ᵇ n) ≡ true
<⇒<ᵇ (s≤s z≤n)       = refl
<⇒<ᵇ (s≤s (s≤s m<n)) = <⇒<ᵇ (s≤s m<n)

<ᵇ⇒< : ∀ {m n} -> (m <ᵇ n) ≡ true -> m < n
<ᵇ⇒< {zero} {suc n} p = s≤s z≤n
<ᵇ⇒< {suc m} {suc n} p = s≤s (<ᵇ⇒< p)


absurd : {A : Set} {u v : Bool} (H1 : u ≡ v) (H2 : u ≡ not v) -> A
absurd {v = false} refl ()
absurd {v = true} refl ()

-- Definition of the two maps which will form the bijection 

inc2inc' : (l : List ℕ) (i : Increase l) -> Increase' l
inc2inc' .(l1 ++ a ∷ b ∷ l2) (inc l1 l2 a b Hab) = increase'++ (a ∷ b ∷ l2) l1 (bigger (b ∷ l2) a (<⇒<ᵇ Hab))

inc'2inc : (l : List ℕ) (i : Increase' l) -> Increase l
inc'2inc .(a ∷ b ∷ l) (bigger (b ∷ l) a Hal) = inc [] l a b (<ᵇ⇒< Hal)
inc'2inc .(a ∷ l) (cons-inc l a i) = cons-increase a l (inc'2inc l i)

-- One last lemma
inc2inc'-cons : (l : List ℕ) (a : ℕ) (i : Increase l) ->  inc2inc' (a ∷ l) (cons-increase a l i) ≡ cons-inc l a (inc2inc' l i)
inc2inc'-cons .(l1 ++ a₁ ∷ b ∷ l2) a (inc l1 l2 a₁ b Hab) = refl


-- We now prove that they are indeed inverses to each other.
isbij-inc2inc' : (l : List ℕ) -> is-bijection (inc2inc' l)
is-bijection.inv (isbij-inc2inc' l) = inc'2inc l
is-bijection.f-inv (isbij-inc2inc' .(a ∷ x ∷ l)) (bigger (x ∷ l) a Hal) = cong (bigger (x ∷ l) a) (Decidable⇒UIP.≡-irrelevant _≟_ _ _)
is-bijection.f-inv (isbij-inc2inc' .(a ∷ x ∷ l)) (cons-inc (x ∷ l) a i) = trans (inc2inc'-cons (x ∷ l) a (inc'2inc (x ∷ l) i)) 
                                                                                (cong (cons-inc (x ∷ l) a) (is-bijection.f-inv (isbij-inc2inc' (x ∷ l)) i))
is-bijection.inv-f (isbij-inc2inc' .([] ++ a ∷ b ∷ l2)) (inc [] l2 a b Hab) = cong (inc [] l2 a b) (<-irrelevant _ _)
is-bijection.inv-f (isbij-inc2inc' .((x ∷ l1) ++ a ∷ b ∷ l2)) (inc (x ∷ l1) l2 a b Hab) = cong (cons-increase x (l1 ++ a ∷ b ∷ l2)) (is-bijection.inv-f (isbij-inc2inc' (l1 ++ a ∷ b ∷ l2)) (inc l1 l2 a b Hab))




--- Now need to find a bijection between `Increase' l` and `Fin (countIncrease l)`. 
--- To do this, we don't proceed directly, we show that for any l, the set `Increase' l' is `listable`.
--- The intuition is that a set is listable if you can put all its elements in a list. More formally:

record listable (A : Set) : Set where -- A set A is listable if 
    field to-list : List A -- there exists a list of elements of A
    field num : A -> ℕ -- and an indexing function taking any element of A to an integer
    field num-<-length : (a : A) -> num a < length to-list -- which is smaller than  the length of the list of elements of A
    field eq1 : (a : A) -> lookup to-list (fromℕ< (num-<-length a)) ≡ a -- the that if the number associated to some `a` is `n`, then the `n`-th element of the list is (equal to) a
    field eq2 : (n : ℕ) (H : n < length to-list) -> num (lookup to-list (fromℕ< H)) ≡ n -- and the number associated to the n-th element of the list is (equal to) n.


-- First we show that our strategy is valid by showing that listable types are in bijection with a finite set.



listable-to-fin : {A : Set} (H : listable A) (a : A) -> Fin (length (listable.to-list H)) 
listable-to-fin H a = fromℕ< {m = listable.num H a} {n = length (listable.to-list H)} (listable.num-<-length H a)

eq-fromℕ : {n : ℕ} (P : Fin n -> Set) (HP : ∀ (i : ℕ) (H : i < n) -> P (fromℕ< H)) -> ∀ (i : Fin n) -> P i
eq-fromℕ {n = suc n} P HP i with fromℕ<-toℕ i (toℕ<n i) 
... | p = subst P p (HP (toℕ i) (toℕ<n i))


listable-to-fin-is-bij : {A : Set} (H : listable A) -> is-bijection (listable-to-fin H)
is-bijection.inv (listable-to-fin-is-bij H) b = lookup (listable.to-list H) b
is-bijection.f-inv (listable-to-fin-is-bij H) b = toℕ-injective (eq-fromℕ (λ b → toℕ (listable-to-fin H (lookup (listable.to-list H) b)) ≡ toℕ b)
 (λ i H₁ -> trans (toℕ-fromℕ< (listable.num-<-length H (lookup (listable.to-list H) (fromℕ< H₁)))) 
            (trans (listable.eq2 H i H₁) 
            (sym (toℕ-fromℕ< H₁)))) b)
is-bijection.inv-f (listable-to-fin-is-bij H) a = listable.eq1 H a

listable-finite : (A : Set) (H : listable A) -> are-in-bijection A (Fin (length (listable.to-list H)))
are-in-bijection.f (listable-finite A H) = listable-to-fin H
are-in-bijection.is-bij (listable-finite A H) = listable-to-fin-is-bij H

-- All that is left now is to show that `Increase' l' is listable, with list length equal to `countIncrease l`

-- Proof that `Increase' l` is listable:


-- Construction of the associated list.

list-increases : (l : List ℕ) -> List (Increase' l)
list-increases [] = []
list-increases (a ∷ l) with inspect (biggerThanHead a l)
... | false with≡ H = map (cons-inc l a) (list-increases l)
... | true with≡ H = bigger l a H ∷ map (cons-inc l a) (list-increases l)

-- and of the index associated to each element of `Increase' l`
num-increase : (l : List ℕ) (i : Increase' l) -> ℕ
num-increase .(a ∷ l) (bigger l a Hal) = 0
num-increase .(a ∷ l) (cons-inc l a i) with inspect (biggerThanHead a l)
... | false with≡ H = num-increase l i
... | true with≡ H = suc (num-increase l i)

-- Before proving the required properties, we prove a number of lemmas

list-increase-smaller : (x : ℕ) (l : List ℕ) (H : biggerThanHead x l ≡ false) -> list-increases (x ∷ l) ≡ map (cons-inc l x) (list-increases l)
list-increase-smaller x l H with inspect (biggerThanHead x l) 
... | false with≡ H2 = refl
... | true with≡ H2 = absurd H2 H

list-increase-bigger : (x : ℕ) (l : List ℕ) (H : biggerThanHead x l ≡ true) -> list-increases (x ∷ l) ≡ (bigger l x H) ∷ map (cons-inc l x) (list-increases l)
list-increase-bigger x l H with inspect (biggerThanHead x l) 
... | false with≡ H2 = absurd H H2
... | true with≡ H2 = cong (λ u -> (bigger l x u) ∷ map (cons-inc l x) (list-increases l)) (Decidable⇒UIP.≡-irrelevant _≟_ H2 H)

num-increase-smaller : (l : List ℕ) (x : ℕ) (i : Increase' l) (H : biggerThanHead x l ≡ false) -> num-increase (x ∷ l) (cons-inc l x i) ≡ num-increase l i
num-increase-smaller l x i H with inspect (biggerThanHead x l) 
... | false with≡ H' = refl
... | true with≡ H' = absurd H H'

num-increase-bigger : (l : List ℕ) (x : ℕ) (i : Increase' l) (H : biggerThanHead x l ≡ true) -> num-increase (x ∷ l) (cons-inc l x i) ≡ suc (num-increase l i)
num-increase-bigger l x i H with inspect (biggerThanHead x l) 
... | false with≡ H' = absurd H H'
... | true with≡ H' = refl

-- we are now ready to prove
--This is just a useful variant of lookup.

lookup' : {A : Set} (l : List A) (k : ℕ) (H : k < length l) -> A 
lookup' l k H = lookup l (fromℕ< H)

lookup-map : {A B : Set} (f : A -> B) (l : List A) (i : ℕ) (H : i < length (map f l)) (H' : i < length l)-> lookup' (map f l) i H ≡ f (lookup' l i H')
lookup-map f (x ∷ l) zero H H' = refl
lookup-map f (x ∷ l) (suc i) H H' = lookup-map f l i _ _

-- We are now ready to prove that the index is smaller than the length of the list.

num-<-len : (l : List ℕ) (i : Increase' l) -> num-increase l i < length (list-increases l)
num-<-len .(a ∷ l) (bigger l a Hal)  = ≤-trans (s≤s z≤n) (≤-reflexive (sym (cong length (list-increase-bigger a l Hal) )))
num-<-len .(a ∷ l) (cons-inc l a i) with inspect (biggerThanHead a l)
... | false with≡ x = ≤-trans ( num-<-len l i  ) (≤-reflexive (sym (length-map (cons-inc l a) (list-increases l))))
... | true with≡ x = s≤s (≤-trans  ( num-<-len l i  ) (≤-reflexive (sym (length-map (cons-inc l a) (list-increases l)))))

-- And the two required equalities.
eq1-inc : (l : List ℕ) (i : Increase' l) (H : num-increase l i < length (list-increases l)) -> lookup' (list-increases l) (num-increase l i) H ≡ i
eq1-inc .(a ∷ l) (bigger l a Hal) H with inspect (biggerThanHead a l)
... | false with≡ H = absurd  Hal H
... | true with≡ H = cong (bigger l a) (Decidable⇒UIP.≡-irrelevant _≟_ H Hal)
eq1-inc .(a ∷ l) (cons-inc l a i) H with inspect (biggerThanHead a l) 
... | false with≡ H' = trans (lookup-map (cons-inc l a) (list-increases l) (num-increase l i) H (<-transˡ H (≤-reflexive (length-map (cons-inc l a) (list-increases l))))) 
                            (cong (cons-inc l a) (eq1-inc l i (<-transˡ H (≤-reflexive (length-map (cons-inc l a) (list-increases l))))))
... | true with≡ H' = trans (lookup-map (cons-inc l a) (list-increases l) (num-increase l i) (≤-pred H) (<-transˡ (≤-pred H) (≤-reflexive (length-map (cons-inc l a) (list-increases l))))) 
                            (cong (cons-inc l a) (eq1-inc l i (<-transˡ (≤-pred H) (≤-reflexive (length-map (cons-inc l a) (list-increases l))))))

eq2-inc : (l : List ℕ) (i : ℕ) (H : i < length (list-increases l)) -> num-increase l (lookup' (list-increases l) i H) ≡ i
eq2-inc (x ∷ l) zero H with inspect (biggerThanHead x l) 
... | false with≡ H' = trans (cong (num-increase (x ∷ l)) (lookup-map (cons-inc l x) (list-increases l) zero H (≤-trans H (≤-reflexive (length-map (cons-inc l x) (list-increases l)))))) 
                        (trans (num-increase-smaller l x (lookup' (list-increases l) zero (≤-trans H (≤-reflexive (length-map (cons-inc l x) (list-increases l))))) H') 
                        (eq2-inc l zero (≤-trans H (≤-reflexive (length-map (cons-inc l x) (list-increases l))))))
... | true with≡ H' = refl
eq2-inc (x ∷ l) (suc i) H with inspect (biggerThanHead x l) 
... | false with≡ H' = trans (cong (num-increase (x ∷ l)) (lookup-map (cons-inc l x) (list-increases l) (suc i) H (≤-trans H (≤-reflexive (length-map (cons-inc l x) (list-increases l)))))) 
                        (trans (num-increase-smaller l x (lookup' (list-increases l) (suc i) (≤-trans H (≤-reflexive (length-map (cons-inc l x) (list-increases l))))) H') 
                        (eq2-inc l (suc i) (≤-trans H (≤-reflexive (length-map (cons-inc l x) (list-increases l))))))
... | true with≡ H' = trans (cong (num-increase (x ∷ l)) (lookup-map (cons-inc l x) (list-increases l) i (≤-pred H) (≤-trans (≤-pred H) (≤-reflexive (length-map (cons-inc l x) (list-increases l)))))) 
                        (trans (num-increase-bigger l x (lookup' (list-increases l) i (≤-trans (≤-pred H) (≤-reflexive (length-map (cons-inc l x) (list-increases l))))) H') 
                        (cong suc (eq2-inc l i (≤-trans (≤-pred H) (≤-reflexive (length-map (cons-inc l x) (list-increases l)))))))

-- The fact that `Increas' l` is listable is can now be stored easily:

is-listable-inc' : (l : List ℕ) -> listable (Increase' l)
listable.to-list (is-listable-inc' l) = list-increases l
listable.num (is-listable-inc' l) a = num-increase l a
listable.num-<-length (is-listable-inc' l) a = num-<-len l a
listable.eq1 (is-listable-inc' l) a = eq1-inc l a (num-<-len l a)
listable.eq2 (is-listable-inc' l) n H = eq2-inc l n H



--- We now know that `Increase l` is in bijection with `Fin (length (list-increases l))`, the only thing left to check is that `length (list-increases l)` is equal
-- to `countIncreases l`. 
-- We start with two lemmas 

count-increase-smaller : (x : ℕ) (l : List ℕ) (H : biggerThanHead x l ≡ false) ->  countIncrease l ≡ countIncrease (x ∷ l) 
count-increase-smaller x l H with (biggerThanHead x l) 
... | false = refl

count-increase-bigger : (x : ℕ) (l : List ℕ) (H : biggerThanHead x l ≡ true) ->  suc (countIncrease l) ≡ countIncrease (x ∷ l) 
count-increase-bigger x l H with (biggerThanHead x l) 
... | true = refl

-- The proposition 
len-list-increases : (l : List ℕ) -> length (list-increases l) ≡ countIncrease l
len-list-increases [] = refl
len-list-increases (x ∷ l) with inspect (biggerThanHead x l) 
... | false with≡ H = trans (length-map ((cons-inc l x)) (list-increases l)) 
                    (trans (len-list-increases l) 
                            (count-increase-smaller x l H))
... | true with≡ H = trans (cong suc (trans (length-map (cons-inc l x) (list-increases l)) (len-list-increases l))) 
                            (count-increase-bigger x l H)