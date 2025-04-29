{-# OPTIONS --allow-unsolved-metas #-}
module Helper where

open import Agda.Builtin.Nat hiding (_<_)
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Char
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality
  using (_≡_; refl)
  
open import Fin

open import CustomData

_%_ : (a b : Nat) -> Nat
-- Return a % (b+1)
a % b = mod-helper 0 b a b

_//_ : (a b : Nat) -> Nat
--  Return a // (b+1)
a // b = div-helper 0 b a b

_||_ : (a b : Bool) -> Bool
-- Boolean OR
false || false = false
_ || _ = true

_&&_ : (a b : Bool) -> Bool
-- Boolean AND
true && true = true
_ && _ = false

not : Bool -> Bool
not true = false
not false = true

data Edge {n : Nat} (g : Graph' n) (u : Fin n) (v : Fin n) : Set where
    mkEdge : Edge g u v


data Walk {n : Nat} (g : Graph' n) (u : Fin n) : Fin n → Set where
    nil : Walk g u u
    cons : ∀ {v w} → Edge g v w → Walk g u v → Walk g u w

Connected : {n : Nat} -> Graph' n → Set
Connected g = ∀ v w -> Walk g v w

len : {A : Set} -> List A -> Nat
len [] = 0
len (x ∷ list) = suc (len list)

is-odd : {A : Set} -> List A -> Bool
is-odd list = ((len list) % 2) == 1

data IsOddEdges {n : Nat} : Node n -> Set where
    isodd : (node : Node n) -> {odd : is-odd (Node.vertice node) ≡ true} -> IsOddEdges node

data OddVertices {n : Nat} : (List (Node n)) -> Nat -> Set where
    nil : OddVertices [] zero
    cons : ∀ {n' ns x} → IsOddEdges n' → OddVertices ns x → OddVertices (n' ∷ ns) (suc x)

data _≤_ : Nat → Nat → Set where
    zero : ∀ {n} → zero ≤ n
    suc : ∀ {m n} → m ≤ n → suc m ≤ suc n

data ImpossibleToTravelAllBrigdeOnce {n : Nat} (g : Graph' n) : Set where
    check : ∀ {m} -> Connected g -> OddVertices g m -> 3 ≤ m -> ImpossibleToTravelAllBrigdeOnce g