module Main where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Char
open import Agda.Builtin.Sigma

open import Helper
open import CustomData
open import Fin

node0 : Node MAX_NODES
node0 = record {id = zero ; vertice = suc (suc (suc zero)) ∷ suc (suc (suc zero)) ∷ suc (suc zero) ∷ []}

node1 : Node MAX_NODES
node1 = record {id = suc zero ; vertice = suc (suc (suc zero)) ∷ suc (suc (suc zero)) ∷ suc (suc zero) ∷ []}

node2 : Node MAX_NODES
node2 = record {id = suc (suc zero) ; vertice = suc (suc (suc zero)) ∷ suc zero ∷ zero ∷ []}

node3 : Node MAX_NODES
node3 = record {id = suc (suc (suc zero)) ; vertice = suc (suc zero) ∷ suc zero ∷ suc zero ∷ zero ∷ zero ∷ []}


g : Graph' MAX_NODES
g = node3 ∷ node2 ∷ node1 ∷ node0 ∷ [] --record {num = MAX_NODES ; nodes = node3 ∷ node2 ∷ node1 ∷ node0 ∷ []}


pattern f0 = zero
pattern f1 = suc zero
pattern f2 = suc (suc zero)
pattern f3 = suc (suc (suc zero))


edge1 : Edge g f0 f2
edge1 = mkEdge

edge2 : Edge g f0 f3
edge2 = mkEdge

edge3 : Edge g f3 f0
edge3 = mkEdge

edge4 : Edge g f3 f1
edge4 = mkEdge

edge5 : Edge g f1 f3
edge5 = mkEdge

edge6 : Edge g f2 f1
edge6 = mkEdge

edge7 : Edge g f3 f2
edge7 = mkEdge

connected_graph : Connected g
connected_graph f0 f0 = nil
connected_graph f0 f1 = cons edge4 (cons edge2 nil)
connected_graph f0 f2 = cons edge1 nil
connected_graph f0 f3 = cons edge2 nil
connected_graph f1 f0 = cons edge3 (cons edge5 nil)
connected_graph f1 f1 = nil
connected_graph f1 f2 = cons edge7 (cons edge5 nil)
connected_graph f1 f3 = cons edge5 nil
connected_graph f2 f0 = cons edge3 (cons edge5 (cons edge6 nil))
connected_graph f2 f1 = cons edge6 nil
connected_graph f2 f2 = nil
connected_graph f2 f3 = cons edge5 (cons edge6 nil)
connected_graph f3 f0 = cons edge3 nil
connected_graph f3 f1 = cons edge4 nil
connected_graph f3 f2 = cons edge7 nil
connected_graph f3 f3 = nil


CountOddVertices-helper : (ns : List (Node MAX_NODES)) → OddVertices ns (len ns)
CountOddVertices-helper [] = nil
CountOddVertices-helper (x ∷ list) = cons (isodd x) (CountOddVertices-helper list) 

CountOddVertices : {x : Nat} -> OddVertices g (len g)
CountOddVertices = CountOddVertices-helper g

ProofPrevLeSuc : (m : Nat) -> m ≤ suc m
ProofPrevLeSuc zero = zero
ProofPrevLeSuc (suc m) = suc (ProofPrevLeSuc m)

IsImpossible : ImpossibleToTravelAllBrigdeOnce g
IsImpossible = check connected_graph CountOddVertices (ProofPrevLeSuc 3)  