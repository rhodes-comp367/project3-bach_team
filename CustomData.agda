{-# OPTIONS --allow-unsolved-metas #-}
module CustomData where

open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Bool

open import Fin

MAX_NODES : Nat 
MAX_NODES = 4

record Node (n : Nat) :  Set where
    constructor
        node 
    field
        id : Fin n
        vertice : List (Fin n)
        
Graph' : Nat → Set
Graph' n = List (Node n)
