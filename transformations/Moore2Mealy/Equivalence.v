Require Import String.
Require Import Moore.
Require Import MooreSemantics.
Require Import Mealy.
Require Import MealySemantics.
Require Import Moore2Mealy.
Require Import core.Semantics.
Require Import core.utils.CpdtTactics.
Require Import List.
Scheme Equality for list.




Theorem Moore2Mealy_equivalence :
    forall (m : MooreModel) (i: list string), 
        Moore_execute m i = Mealy_execute (execute Moore2Mealy m) i.
Proof.
intros.
unfold Moore_execute, Mealy_execute.
destruct (MooreSemantics.initialState m) eqn: q0.
+ destruct (initialState (execute Moore2Mealy m)) eqn: q0_tr.
  ++ revert q0. revert s. revert q0_tr. revert s0.
     induction i.
     - intros. simpl. auto.
     - intros.
  ++ (* contradiction *)
     (* need uniqueness on initial state *)
     admit.
+ destruct (initialState (execute Moore2Mealy m)) eqn: q0_tr.
  ++ (* contradiction *)
     admit.
  ++ auto.
Admitted.

