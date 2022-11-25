Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Bool.

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


(* Append nat to end of list *)
Fixpoint addToEnd (r: nat) (l: list nat): list nat :=
    match l with
    | h::t => h::(addToEnd r t)
    | nil => r::nil
    end.

(* Append string to end of list *)
Fixpoint addToEndString (r: string) (l: list string): list string :=
    match l with
    | h::t => h::(addToEndString r t)
    | nil => r::nil
    end.

(* Move first column input to end of list *)
Definition moveFirstColumnInput (inputs: list string) := 
    match inputs with
    | nil => nil
    | firstColumn::otherColums => addToEndString firstColumn otherColums
    end.

(*Compute moveFirstColumnInput ("a"::"b"::"c"::nil).*)

(* Move first column of each row to end of list *)
Fixpoint moveFirstColumnRows (rows: list (prod (list nat) nat)) := 
    match rows with
    | nil => nil
    | (nil, output)::otherRows => (nil, output)::otherRows
    | (firstColumn::otherColums, output)::otherRows => ((addToEnd firstColumn otherColums), output) :: moveFirstColumnRows(otherRows)
    end.

(* Compute moveFirstColumnRows (((0::0::nil),1)::((0::1::nil),0)::nil). *)
    
(* check if multiple value in the first column of each row *)
Fixpoint isMultipleValueFirstColumn (rows: list (prod (list nat) nat)) : bool := 
    match rows with 
    | nil => false
    | (nil, _) :: _=> false
    | (firstColumn::otherColums, _)::othersRows => 
        match firstColumn with 
        | 2 => true
        | _ => isMultipleValueFirstColumn(othersRows)
        end 
    end.

(*Compute isMultipleValueFirstColumn (((0::0::nil),1)::((2::1::nil),0)::nil).
Compute isMultipleValueFirstColumn (((0::0::nil),1)::((1::2::nil),0)::nil).*)
 
(* order tt to have multiple value in the last columns *)    
Fixpoint orderTT (inputsSize: nat) (inputs: list string) (rows: list (prod (list nat) nat)) : prod (list string) (list (prod (list nat) nat)) :=
    match inputsSize with
    | 0 => (inputs, rows)
    | (S u) => if (isMultipleValueFirstColumn(rows)) then (orderTT (u) (moveFirstColumnInput inputs) (moveFirstColumnRows rows)) else (inputs, rows)
    end.

(* filter matrice with false value in firstColumn *)
Fixpoint getFalseTableWithoutFirstColumn(matrice: list (prod (list nat) nat)): list (prod (list nat) nat) :=
    match matrice with
    | (0::inputsValue, outputValue)::rows => (inputsValue, outputValue) :: getFalseTableWithoutFirstColumn(rows)
    | (2::inputsValue, outputValue)::rows => (inputsValue, outputValue) :: getFalseTableWithoutFirstColumn(rows)
    | (_, _)::rows => getFalseTableWithoutFirstColumn(rows)
    | nil => nil
    end.

(* filter matrice with true value in firstColumn *)
Fixpoint getTrueTableWithoutFirstColumn(matrice: list (prod (list nat) nat)): list (prod (list nat) nat) :=
    match matrice with
    | (1::inputsValue, outputValue)::rows => (inputsValue, outputValue) :: getTrueTableWithoutFirstColumn(rows)
    | (2::inputsValue, outputValue)::rows => (inputsValue, outputValue) :: getTrueTableWithoutFirstColumn(rows)
    | (_, _)::rows => getTrueTableWithoutFirstColumn(rows)
    | nil => nil
    end.

(* transform tt to bdd *)    
Fixpoint getBDDFromTT (inputsLength: nat)  (inputs: list string) (output: string) (rows: list (prod (list nat) nat)) : BDDTree := 
    match orderTT inputsLength inputs rows with 
    | (orderInputs, orderRows) => 
        match orderRows with 
        | nil => bddnil
        | ((_,outputValue)::nil) => bddleaf output outputValue
        | rows => 
            match orderInputs with
            | nil => bddnil
            | (firstInput::otherInputs) => 
                match inputsLength with 
                | 0 => bddnil
                | (S u) => bddnode firstInput 
                            (getBDDFromTT u otherInputs output (getFalseTableWithoutFirstColumn rows))
                            (getBDDFromTT u otherInputs output (getTrueTableWithoutFirstColumn rows))
                end
            end
        end
    end.

Definition TT2BDD (t: Table2) := 
    match t with 
    | BuildTable2 inputs output rows => getBDDFromTT (length inputs) inputs output rows
    end.


Definition test1: BDDTree :=
    TT2BDD (BuildTable2 
        ("a"::"b"::"c"::"d"::nil) 
        "s"
        (((0::0::2::2::nil),0)::
        ((0::1::0::0::nil),1)::
        ((0::1::0::1::nil),0)::
        ((0::1::1::2::nil),0)::
        ((1::0::0::0::nil),0)::
        ((1::0::1::0::nil),1)::
        ((1::2::2::1::nil),0)::
        ((1::1::0::0::nil),1)::
        ((1::1::1::0::nil),0)::
        nil)
    ).

Compute test1.     
Close Scope coqtl.