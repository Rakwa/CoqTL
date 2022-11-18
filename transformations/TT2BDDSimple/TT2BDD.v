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
Check bddnil.
Check BuildTable2.

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

    
Fixpoint getBDDFromTT (inputs: list string) (output: string) (rows: list (prod (list nat) nat)) : BDDTree := 
    match rows with 
    | nil => bddnil
    | ((_,outputValue)::nil) => bddleaf output outputValue
    | rows => 
        match inputs with
        | nil => bddnil
        | (firstInput::otherInputs) => bddnode firstInput 
                                        (getBDDFromTT otherInputs output (getFalseTableWithoutFirstColumn rows))  
                                        (getBDDFromTT otherInputs output (getTrueTableWithoutFirstColumn rows))
        end
    end.


Definition TT2BDD (t: Table2) := 
    match t with 
    | BuildTable2 inputs output rows => getBDDFromTT inputs output rows
    end.


Close Scope coqtl.