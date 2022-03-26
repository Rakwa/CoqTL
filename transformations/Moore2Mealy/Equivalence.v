Require Import String.
Require Import Moore.
Require Import MooreSemantics.
Require Import Mealy.
Require Import MealySemantics.
Require Import Moore2Mealy.
Require Import core.Semantics.
Require Import core.utils.Utils.
Require Import List.
Scheme Equality for list.




Lemma Moore2Mealy_executeFromState_eq :
forall (m : MooreModel) (sp: list MooreMetamodel_Object) 
(tp: list MealyMetamodel_Object) (i: list string)
(q0: Moore.State) (q0': State), 
instantiatePattern Moore2Mealy m sp = tp ->
[q0] = MooreMetamodel_toStates sp ->
[q0'] = MealyMetamodel_toStates tp ->
MooreSemantics.executeFromState m q0 i =
executeFromState (execute Moore2Mealy m) q0' i.
Proof.
intros m sp tp inputs.
induction inputs.
- intros. simpl. auto.
- intros q0 q0' rel q0_id q0'_id.
  (* main induction step *)
  (* fold mr_execute just once *)
  unfold MooreSemantics.executeFromState; fold MooreSemantics.executeFromState.
  destruct (find
  (fun t : Moore.Transition => (a =? Moore.Transition_getInput t)%string)
  (MooreSemantics.State_outTransitions q0 m)) eqn: mr_s_tr_input.
-- destruct (Moore.Transition_getTarget t m) eqn: mr_t_tr_trg.
    * unfold executeFromState; fold executeFromState.
    destruct (find (fun t0 : Transition => (a =? Transition_getInput t0)%string)
    (State_outTransitions q0' (execute Moore2Mealy m))) eqn: ml_t_tr_input.
    ** destruct (Transition_getTarget t0 (execute Moore2Mealy m)) eqn: ml_t_tr_trg.
        *** (* assert State_getOutput s = Transition_getOutput t0 *)
            (* apply induction step IHinputs *)
            admit.
        *** (* contradiction *) admit.
    ** (* contradiction *) admit.
    * unfold executeFromState; fold executeFromState.
      destruct (find (fun t0 : Transition => (a =? Transition_getInput t0)%string)
      (State_outTransitions q0' (execute Moore2Mealy m))) eqn: ml_t_tr_input.
      ** destruct (Transition_getTarget t0 (execute Moore2Mealy m)) eqn: ml_t_tr_trg.
        *** (* contradiction *) admit.
        *** auto.
      ** auto.
-- unfold executeFromState.
  destruct (find (fun t : Transition => (a =? Transition_getInput t)%string) (State_outTransitions q0' (execute Moore2Mealy m))) eqn: ml_s_tr_input.
  --- (* contradiction *) admit.
  --- auto.
Admitted.

Theorem Moore2Mealy_equivalence :
    forall (m : MooreModel) (i: list string), 
        Moore_execute m i = Mealy_execute (execute Moore2Mealy m) i.
Proof.
intros.
unfold Moore_execute, Mealy_execute.
destruct (MooreSemantics.initialState m) eqn: q0.
+ destruct (initialState (execute Moore2Mealy m)) eqn: q0_tr.
  ++ (* assert instantiatePattern Moore2Mealy m sp = tp /\
        [s0] = MooreMetamodel_toStates sp /\
        [s0'] = MealyMetamodel_toStates tp *)
     (* apply Moore2Mealy_executeFromState_eq *)
     admit.
  ++ (* contradiction *) admit.
+ destruct (initialState (execute Moore2Mealy m)) eqn: q0_tr.
  ++ (* contradiction *) admit.
  ++ auto.
Admitted.

