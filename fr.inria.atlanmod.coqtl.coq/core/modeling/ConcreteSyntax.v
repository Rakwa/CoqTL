Require Import String.

Require Import core.utils.Utils.
Require Import core.modeling.ModelingSchema.
Require Import core.Graph.
Require Import core.Syntax.
Require Import core.modeling.ConcreteExpressions.
Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingTransformationConfiguration.

Section ConcreteSyntax.

Context {tc: TransformationConfiguration} {mtc: ModelingTransformationConfiguration tc}.

(** ** Syntax **)

Fixpoint denoteFunction (sclasses : list SourceGraphClass) (otype: Type) :=
  match sclasses with
  | nil => otype
  | cons class classes' => (denoteModelClass class) -> denoteFunction classes' otype
  end.

Definition outputPatternEdge
(sclasses : list SourceGraphClass) (tclass: TargetGraphClass)  (tref: TargetGraphReference):=
denoteFunction (sclasses) ((denoteModelClass tclass) -> option (denoteModelReference tref)).

Definition outputPatternNodeTypes
(sclasses : list SourceGraphClass) (tclass: TargetGraphClass) :=
  denoteFunction (sclasses) (denoteModelClass tclass).

Definition iteratedListTypes
(sclasses : list SourceGraphClass) :=
  denoteFunction (sclasses) nat.

Definition guardTypes (sclasses : list SourceGraphClass) :=
  denoteFunction (sclasses) bool.

Inductive ConcreteOutputPatternEdge (InTypes: list SourceGraphClass) (OutType:TargetGraphClass) : Type :=
  link :
  forall (OutRef: TargetGraphReference),
      (list TraceLink -> nat -> SourceGraph -> (outputPatternEdge InTypes OutType OutRef)) ->
      ConcreteOutputPatternEdge InTypes OutType.

Inductive ConcreteOutputPatternNode (InTypes: list SourceGraphClass) : Type :=
  elem :
    forall (OutType:TargetGraphClass),
      string ->
        (nat -> SourceGraph -> (outputPatternNodeTypes InTypes OutType)) 
    -> (list (ConcreteOutputPatternEdge InTypes OutType)) -> ConcreteOutputPatternNode InTypes.

Inductive ConcreteRule : Type :=
  concreteRule :
    (* name *) string
    (* from *) -> forall (InTypes: list SourceGraphClass),
      option (SourceGraph -> (guardTypes InTypes))
    (* for *) -> option (SourceGraph -> (iteratedListTypes InTypes))
    (* to *) -> (list (ConcreteOutputPatternNode InTypes))
    -> ConcreteRule.

Inductive ConcreteTransformation : Type :=
  transformation :
    list ConcreteRule
    -> ConcreteTransformation.

(** ** Accessors **)

Definition ConcreteOutputPatternEdge_getRefType {InElTypes: list SourceGraphClass} {OutType:TargetGraphClass} (o: ConcreteOutputPatternEdge InElTypes OutType) : TargetGraphReference :=
  match o with
    link _ _ y _ => y
  end.

Definition ConcreteOutputPatternEdge_getOutputPatternEdge {InElTypes: list SourceGraphClass} {OutType:TargetGraphClass} (o: ConcreteOutputPatternEdge InElTypes OutType) :
  list TraceLink -> nat -> SourceGraph -> (outputPatternEdge InElTypes OutType (ConcreteOutputPatternEdge_getRefType o)).
Proof.
  destruct o eqn:ho.
  exact o0.
Defined.

Definition ConcreteOutputPatternNode_getName {InElTypes: list SourceGraphClass} (o: ConcreteOutputPatternNode InElTypes) : string :=
  match o with
    elem _ _ y _ _ => y
  end.

Definition ConcreteOutputPatternNode_getOutType {InElTypes: list SourceGraphClass} (o: ConcreteOutputPatternNode InElTypes) : TargetGraphClass :=
  match o with
    elem _ y _ _ _ => y
  end.

Definition ConcreteOutputPatternNode_getOutPatternNode {InElTypes: list SourceGraphClass} (o: ConcreteOutputPatternNode InElTypes) :
  nat -> SourceGraph -> (outputPatternNodeTypes InElTypes (ConcreteOutputPatternNode_getOutType o)) :=
  match o with
    elem _ _ _ y _ => y
  end.

Definition ConcreteOutputPatternNode_getOutputEdges {InElTypes: list SourceGraphClass} (o: ConcreteOutputPatternNode InElTypes) :
  list (ConcreteOutputPatternEdge InElTypes (ConcreteOutputPatternNode_getOutType o)) :=
  match o with
    elem _ _ _ _ y => y
  end.

Definition ConcreteRule_getName (x : ConcreteRule) : string :=
  match x with
    concreteRule y _ _ _ _ => y
  end.

Definition ConcreteRule_getInTypes (x : ConcreteRule) : list SourceGraphClass :=
  match x with
    concreteRule _ y _ _ _ => y
  end.

Definition ConcreteRule_getGuard (x : ConcreteRule) :
  option(SourceGraph -> (guardTypes (ConcreteRule_getInTypes x))).
Proof.
  destruct x eqn:hx.
  assumption.
Defined.

Definition ConcreteRule_getIteratedList (x: ConcreteRule) :
  option (SourceGraph -> (iteratedListTypes (ConcreteRule_getInTypes x))).
Proof.
  destruct x eqn:hx.
  assumption.
Defined.

Definition ConcreteRule_getConcreteOutputPattern (x : ConcreteRule) :
  list (ConcreteOutputPatternNode (ConcreteRule_getInTypes x)) :=
  match x with
    concreteRule _ _ _ _ y => y
  end.

Definition ConcreteRule_findConcreteOutputPatternNode (r: ConcreteRule) (name: string) : option (ConcreteOutputPatternNode (ConcreteRule_getInTypes r)) :=
  find (fun(o:ConcreteOutputPatternNode (ConcreteRule_getInTypes r)) => beq_string name (ConcreteOutputPatternNode_getName o))
        (ConcreteRule_getConcreteOutputPattern r).

Definition ConcreteTransformation_getConcreteRules (x : ConcreteTransformation) : list ConcreteRule :=
  match x with transformation y => y end.

End ConcreteSyntax.

Arguments transformation {_ _}.
Arguments concreteRule {_ _}.
Arguments elem {_ _}.
Arguments link {_ _}.

Declare Scope coqtl.

(* Rule *)
Notation "'rule' rulename 'from' types 'where' guard 'for' iterator 'to' outputpattern " :=
  (concreteRule rulename types (Some guard) (Some iterator) outputpattern)
    (right associativity, at level 60):coqtl.

(* Rule without guard *)
Notation "'rule' rulename 'from' types 'for' iterator 'to' outputpattern " :=
  (concreteRule rulename types (None) (Some iterator) outputpattern)
    (right associativity, at level 60):coqtl.

(* Rule without iterator *)
Notation "'rule' rulename 'from' types 'where' guard 'to' outputpattern " :=
  (concreteRule rulename types (Some guard) (None) outputpattern)
    (right associativity, at level 60):coqtl.

(* Rule without guard and iterator *)
Notation "'rule' rulename 'from' types 'to' outputpattern " :=
  (concreteRule rulename types (None) (None) outputpattern)
    (right associativity, at level 60):coqtl.
