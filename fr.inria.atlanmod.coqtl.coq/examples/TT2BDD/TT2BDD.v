Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.utils.Utils.

Require Import core.ConcreteSyntax.
Require Import core.Semantics.
Require Import core.Metamodel.
Require Import core.Expressions.

Require Import TT2BDD.TT.
Require Import TT2BDD.BDDv2.

(* Outline of the transformation
   The TruthTable transforms to a BDD, with the same name and Ports.

   Each InputPort transforms to an InputPort, with the same name.

   Each OutputPort transforms to an OutputPort, with the same name.

   Each Cell for the OutputPorts transform into Assignments.

   Each Row transforms to a Leaf.

   The TruthTable transforms into a subtree for each combination of input values, each subtree is owned by the subtree with iterator = i/2 
*)


(* We want to prove the following equivalence: 
   given an assignment for all input ports, and given an output port, 
   the TT and the BDD give the same value for that output port *)