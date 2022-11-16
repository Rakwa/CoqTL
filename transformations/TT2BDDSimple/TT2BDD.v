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
Check BuildTable2.

Fixpoint removeFirstColumn(matrice: list (prod (list nat) nat)): list (prod (list nat) nat) := 
    match matrice with
    | nil => nil
    | (nil, _) :: rows => removeFirstColumn(rows)
    | (firstInput::inputsValue, outputValue)::rows => (inputsValue, outputValue) :: removeFirstColumn(rows)
    end.

Fixpoint getFalseTableWithoutFirstColumn(matrice: list (prod (list nat) nat)): list (prod (list nat) nat) :=
    match matrice with
    | (0::inputsValue, outputValue)::rows => (inputsValue, outputValue) :: getFalseTableWithoutFirstColumn(rows)
    | (_, _)::rows => getFalseTableWithoutFirstColumn(rows)
    | nil => nil
    end.

Fixpoint getTrueTableWithoutFirstColumn(matrice: list (prod (list nat) nat)): list (prod (list nat) nat) :=
    match matrice with
    | (1::inputsValue, outputValue)::rows => (inputsValue, outputValue) :: getTrueTableWithoutFirstColumn(rows)
    | (_, _)::rows => getTrueTableWithoutFirstColumn(rows)
    | nil => nil
    end.

    
Fixpoint TT2BDD (t: Table2) := 
    match t with
    | BuildTable2 _ outputName ((_,outputValue)::nil) => 
            bddleaf outputName outputValue
    | BuildTable2 (firstInput::inputs) outputName rows => 
            bddnode firstInput 
                    (TT2BDD (BuildTable2 inputs outputName (getFalseTableWithoutFirstColumn rows)))  
                    (TT2BDD (BuildTable2 inputs outputName (getTrueTableWithoutFirstColumn rows)))
    | BuildTable2 _ outputName _ =>
            bddleaf outputName 0
    end.


(* We want to prove the following equivalence: 
   given an assignment for *all* input ports 'ins', and given *an* output port 'out', 
   (valueOf (evalTT TT ins) out) = (valueOf (evalBDD BDD ins) out) 
   
    Theorem TT2BDD_correct: 
     forall (inValues : list bool) (tt: TT) (bdd:BDD),
        bdd = execute TT2BDD tt ->
        evalTT tt inValues = evalBDD bdd inValues.
   *)

Close Scope coqtl.