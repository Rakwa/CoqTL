Require Import String.
Require Import List.      (* sequence *)
Require Import Multiset.  (* bag *)
Require Import ListSet.   (* set *)
Require Import Omega.
Require Import Bool.
Require Import core.Metamodel.
Require Import core.EqDec.

Require Import core.utils.Utils.
Require Import core.Model.

(* Binary Decision Diagram (Tree) *)

Inductive BDD := 
  | BuildBDDNode :
  (* name *) string ->
  BDD
  | BuildBDDEdge :
  (* child *) BDD ->
  (* parent *) BDD ->
  BDD.

Fixpoint BDDEq (a b : BDD) := 
  match a, b with
  | BuildBDDNode n1, BuildBDDNode n2 => String.eqb n1 n2 
  | BuildBDDEdge n1 n3, BuildBDDEdge n2 n4 => andb (BDDEq n1 n2) (BDDEq n3 n4)
  | _, _ => false
  end.

Instance BDDEqDec : EqDec BDD := {
    eq_b := BDDEq
}.

Instance BDDM : Metamodel :=
{
  ModelElement := BDD;
}.