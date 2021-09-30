Require Import String.

Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.TransformationConfiguration.
Require Export core.TraceLink.

(** * Syntax

      In this section, we introduce _one possible_ abstract syntax of the CoqTL transformation engine.  
      ---- *)

Section Syntax.

Context {tc: TransformationConfiguration}.

(** ** Syntactic Nodes

        Next, we model syntactic elements of any transformation specification that supported by the CoqTL engine. *)

(** *** OutputPatternLink *)

Inductive OutputPatternLink : Type :=
  buildOutputPatternLink :
    (list TraceLink -> nat -> SourceModel -> (list SourceNode) -> TargetNode -> option nat) 
    -> (nat -> list TraceLink -> nat -> SourceModel -> (list SourceNode) -> TargetNode -> option TargetEdge) 
    -> OutputPatternLink.

Definition OutputPatternLink_getIteratorExpr (o: OutputPatternLink) : 
    list TraceLink -> nat -> SourceModel -> (list SourceNode) -> TargetNode -> option nat :=
    match o with
      buildOutputPatternLink y _ => y
    end.

Definition OutputPatternLink_getLinkExpr (o: OutputPatternLink) : 
    nat -> list TraceLink -> nat -> SourceModel -> (list SourceNode) -> TargetNode -> option TargetEdge :=
    match o with
      buildOutputPatternLink _ y => y
    end.

(** *** OutputPatternNode *)

Inductive OutputPatternNode : Type :=
  buildOutputPatternNode :
    string 
    -> (SourceModel -> (list SourceNode) -> option nat)
    -> (nat -> SourceModel -> (list SourceNode) -> option TargetNode) 
    -> (list OutputPatternLink) -> OutputPatternNode.

Definition OutputPatternNode_getName (o: OutputPatternNode) : string :=
  match o with
    buildOutputPatternNode y _ _ _ => y
  end.

Definition OutputPatternNode_getIteratorExpr (o: OutputPatternNode) :=
  match o with
    buildOutputPatternNode _ y _ _ => y
  end.


Definition OutputPatternNode_getNodeExpr (o: OutputPatternNode) : nat -> SourceModel -> (list SourceNode) -> option TargetNode :=
  match o with
    buildOutputPatternNode _ _ y _ => y
  end.

Definition OutputPatternNode_getOutputLinks (o: OutputPatternNode) :
  list OutputPatternLink :=
  match o with
    buildOutputPatternNode _ _ _ y => y
      end.

(** *** Rule *)

Inductive Rule : Type :=
  buildRule :
    (* name *) string
    (* from *) -> (SourceModel -> (list SourceNode) -> option bool)
    (* to *) -> (list OutputPatternNode)
    -> Rule.

Definition Rule_getName (x : Rule) : string :=
  match x with
    buildRule y _ _ => y
  end.
  
Definition Rule_getGuardExpr (x : Rule) : SourceModel -> (list SourceNode) -> option bool :=
  match x with
    buildRule _ y _ => y
  end.

Definition Rule_getOutputPatternNodes (x : Rule) :
  list OutputPatternNode :=
  match x with
    buildRule _ _ y => y
  end.

(** find an output pattern element in a rule by the given name: *)

Definition Rule_findOutputPatternNode (r: Rule) (name: string) : option OutputPatternNode :=
  find (fun (o:OutputPatternNode) => beq_string name (OutputPatternNode_getName o))
        (Rule_getOutputPatternNodes r).

(** *** Transformation *)

Inductive Transformation : Type :=
  buildTransformation :
    nat
    -> list Rule
    -> Transformation.

Definition Transformation_getArity (x : Transformation) : nat :=
  match x with buildTransformation y _ => y end.

Definition Transformation_getRules (x : Transformation) : list Rule :=
  match x with buildTransformation _ y => y end.

End Syntax.

(* begin hide *)
Arguments Transformation {_}.
Arguments buildTransformation {_}.

Arguments Rule {_}.
Arguments buildRule {_}.

Arguments buildOutputPatternNode {_}.
Arguments buildOutputPatternLink {_}.
(* end hide *)
