Require Import String.
Require Import List.

Require Import Moore.
Require Import core.Model.

Fixpoint MooreMetamodel_toStates (m: list MooreMetamodel_Object) : list State :=
    match m with
    | s :: ss => 
        match (MooreMetamodel_toClass StateClass s) with 
        | Some s => s :: (MooreMetamodel_toStates ss) 
        | None => (MooreMetamodel_toStates ss) 
        end
    | _ => nil
    end.

Fixpoint MooreMetamodel_toTransitions (m: list MooreMetamodel_Object) : list Transition :=
    match m with
    | s :: ss => 
        match (MooreMetamodel_toClass TransitionClass s) with 
        | Some s => s :: (MooreMetamodel_toTransitions ss) 
        | None => (MooreMetamodel_toTransitions ss) 
        end
    | _ => nil
    end.

Definition MooreMetamodel_allStates (m: MooreModel) : list State :=
    MooreMetamodel_toStates (allModelElements m).

Definition MooreMetamodel_allTransitions (m: MooreModel) : list Transition :=
    MooreMetamodel_toTransitions (allModelElements m).

Definition initialState (m: MooreModel) : option State :=
    find (fun s => eqb "S0" (State_getName s)) (MooreMetamodel_allStates m).

Definition State_outTransitions (s: State) (m: MooreModel) : list Transition :=
    filter (fun t => 
        match (Transition_getSource t m) with
        | Some s' => beq_State s s'
        | None => false
        end)
        (MooreMetamodel_allTransitions m).
 
Fixpoint executeFromState (m: MooreModel) (current: State) (remainingInput: list string) : list string :=
    match remainingInput with 
    | i :: is => 
        let outTransition := find (fun t => eqb i (Transition_getInput t)) (State_outTransitions current m) in
        let trgState := 
            match outTransition with 
            | Some t =>  Transition_getTarget t m
            | None => None
            end in
        match trgState with
        | Some s => (State_getOutput s) :: (executeFromState m s is)
        | None => nil
        end
    | _ => nil 
    end.

Definition Moore_execute (m: MooreModel) (input: list string) : list string :=
    match (initialState m) with 
    | Some s => executeFromState m s input
    | None => nil
    end.

Require Import tests.sampleMoore.

Compute Moore_execute InputModel ("1"::"0"::"1"::nil).



