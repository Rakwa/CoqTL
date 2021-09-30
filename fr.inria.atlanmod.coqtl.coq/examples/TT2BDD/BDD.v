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

Inductive BDDNode := 
  BuildBDDNode :
  (* name *) string ->
  BDDNode.

Inductive BDDEdge := 
  BuildBDDEdge :
  (* child *) BDDNode ->
  (* parent *) BDDNode ->
  BDDEdge.

Definition BDDEq (a b : BDDNode) := 
  match a, b with
  | BuildBDDNode n1, BuildBDDNode n2 => String.eqb n1 n2 
  end.

Instance BDDEqDec : EqDec BDDNode := {
    eq_b := BDDEq
}.

Definition source (e: BDDEdge):=
  match e with
  | BuildBDDEdge s t => s
  end.

Definition target (e: BDDEdge):=
  match e with
  | BuildBDDEdge s t => t::nil
  end.

Instance BDDM : Metamodel :=
  Build_Metamodel BDDNode _ BDDEdge source target.
