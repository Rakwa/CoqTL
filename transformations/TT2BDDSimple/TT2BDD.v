Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.

Require Import core.utils.Utils.

Require Import core.modeling.ConcreteSyntax.
Require Import core.Semantics.
Require Import core.Metamodel.
Require Import core.Expressions.

Require Import TT2BDDSimple.TT.
Require Import TT2BDDSimple.BDD.

Open Scope coqtl.

Check bddleaf.
Check bddnode.

Fixpoint removeFirstColumn(matrice: list (prod (list nat) nat)): list (prod (list nat) nat) := 
    match matrice with
    | nil => nil
    | (nil, _) :: rows => removeFirstColumn(rows)
    | (firstInput::inputsValue, outputValue)::rows => (inputsValue, outputValue) :: removeFirstColumn(rows)
    end.

Definition TT2BDD (t: Table2) := 
    match t with
    | BuildTable2 _ outputName ((_,outputValue)::nil) => bddleaf outputName outputValue
    | BuildTable2 (firstInput::inputs) outputName rows => bddnode firstInput (BuildTable2 inputs outputName removeFirstColumn(rows)) (BuildTable2 inputs outputName removeFirstColumn(rows))
    | BuildTable2 _ _ _ => bddleaf "a" 1
    end.



    (*transformation TTMetamodel bddMetamodel [
        
        (* The TruthTable transforms to a BDD, with the same name and Ports. *)

        (* Each InputPort transforms to an InputPort, with the same name. *)

        (* Each OutputPort transforms to an OutputPort, with the same name. *)
     
        (* Each Cell for the OutputPorts transform into Assignments. *)
     
        (* Each Row transforms to a Leaf. *)
     
        (* The TruthTable transforms into a subtree for each combination of input values, each subtree is owned by the subtree with iterator = i/2  *)
     
    ].*)

    (* 

    example:
    a b c
    f - t
    t t f

              1
   a    2           3 
   b  4   5       6   7
    
    leaf 1: c=t parent:4,5
    leaf 2: c=f parent:7

    (owner_i = i/2 rounded down)
             1
       2           3
     4   5       6   7
    8 9 10 11   12 13 14 15
   f=0 ...
    *)


(* We want to prove the following equivalence: 
   given an assignment for *all* input ports 'ins', and given *an* output port 'out', 
   (valueOf (evalTT TT ins) out) = (valueOf (evalBDD BDD ins) out) 
   
    Theorem TT2BDD_correct: 
     forall (inValues : list bool) (tt: TT) (bdd:BDD),
        bdd = execute TT2BDD tt ->
        evalTT tt inValues = evalBDD bdd inValues.
   *)

Close Scope coqtl.