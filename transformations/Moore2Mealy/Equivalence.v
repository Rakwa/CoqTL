Require Import String.
Require Import Moore.
Require Import MooreSemantics.
Require Import Mealy.
Require Import MealySemantics.
Require Import Moore2Mealy.
Require Import core.Semantics.
Require Import core.utils.CpdtTactics.


Scheme Equality for list.

Theorem Moore2Mealy_equivalence :
    forall (m : MooreModel) (i: list string), 
        Moore_execute m i = Mealy_execute (execute Moore2Mealy m) i.
Proof.
unfold Moore_execute, Mealy_execute. 
induction i.
- simpl.
  destruct (MooreSemantics.initialState m), (initialState (execute Moore2Mealy m)).
  reflexivity. reflexivity. reflexivity. reflexivity.
- destruct (MooreSemantics.initialState m), (initialState (execute Moore2Mealy m)).
  simpl.
Admitted. 
