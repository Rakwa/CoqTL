Require Import String.
Require Import Omega.
Require Import Bool.

Require Import core.utils.Utils.
Require Import core.Graph.
Require Import core.modeling.Schema.
Require Import core.modeling.ConcreteExpressions.
Require Import core.Engine.
Require Import core.modeling.ModelingEngine.
Require Import core.Semantics.
Require Import core.modeling.ModelingSemantics.
Require Import core.Certification.
Require Import core.Syntax.

Section IterateTracesCertification.

Context {tc: TransformationConfiguration} {mtc: ModelingTransformationConfiguration tc}. 

(** * Resolve *)

Theorem tr_resolveAll_in:
  forall (tls: list TraceLink) (sm: SourceModel) (name: string)
    (type: TargetModelClass) (sps: list(list SourceNode)),
    resolveAll tls sm name type sps = resolveAllIter tls sm name type sps 0.
Proof.
  crush.
Qed.

Theorem tr_resolveAllIter_in:
  forall (tls: list TraceLink) (sm: SourceModel) (name: string)
    (type: TargetModelClass) (sps: list(list SourceNode)) (iter: nat)
    (te: denoteModelClass type),
    (exists tes: list (denoteModelClass type),
        resolveAllIter tls sm name type sps iter = Some tes /\ In te tes) <->
    (exists (sp: list SourceNode),
        In sp sps /\
        resolveIter tls sm name type sp iter = Some te).
Proof.
  intros.
      intros.
  split.
  - intros.
    destruct H. destruct H.
    unfold resolveAllIter in H.
    inversion H.
    rewrite <- H2 in H0.
    apply in_flat_map in H0.
    destruct H0. destruct H0.
Admitted.
    (* exists sp. split; auto.
    destruct (resolveIter tls sm name type x0 iter).
    -- unfold optionToList in H1. crush.
    -- crush.
  - intros.
    destruct H. destruct H.
    remember (resolveAllIter tls sm name type sps iter) as tes1.
    destruct tes1 eqn: resolveAll.
    -- exists l.
        split. auto.
        unfold resolveAllIter in Heqtes1.
        inversion Heqtes1.
        apply in_flat_map.
        exists x. split. auto.
        destruct (resolveIter tls sm name type x iter).
        --- crush.
        --- crush.
    -- unfold resolveAllIter in Heqtes1.
        crush.
Qed.*)

Theorem tr_resolve_in:
  forall (tls: list TraceLink) (sm: SourceModel) (name: string)
    (type: TargetModelClass) (sp: list SourceNode),
    resolve tls sm name type sp = resolveIter tls sm name type sp 0.
Proof.
  crush.
Qed.

(* this one direction, the other one is not true since exists cannot gurantee uniqueness in find *)
Theorem tr_resolveIter_leaf:
  forall (tls:list TraceLink) (sm : SourceModel) (name: string) (type: TargetModelClass)
    (sp: list SourceNode) (iter: nat) (x: denoteModelClass type),
    resolveIter tls sm name type sp iter = return x ->
      (exists (tl : TraceLink),
        In tl tls /\
        Is_true (list_beq SourceNode core.EqDec.eq_b (TraceLink_getSourcePattern tl) sp) /\
        ((TraceLink_getIterator tl) = iter) /\ 
        ((TraceLink_getName tl) = name)%string /\
        (toModelClass type (TraceLink_getTargetNode tl) = Some x)). 
Proof.
intros.
unfold resolveIter in H.
destruct (find (fun tl: TraceLink => 
(Semantics.list_beq SourceNode core.EqDec.eq_b (TraceLink_getSourcePattern tl) sp) &&
((TraceLink_getIterator tl) =? iter) &&
((TraceLink_getName tl) =? name)%string) tls) eqn: find.
- exists t.
  apply find_some in find.
  destruct find.
  symmetry in H1.
  apply andb_true_eq in H1.
  destruct H1.
  apply andb_true_eq in H1.
  destruct H1.
  crush.
  -- apply beq_nat_true. crush.
  -- apply String.eqb_eq. crush.
  -- Admitted.

Instance ModelingCoqTLEngine :
  ModelingTransformationEngine (@CoqTLEngine SourceNode SourceEdge eqdec_sme TargetNode TargetEdge):=
  {
    SourceModelClass := SourceModelClass;
    SourceModelReference := SourceModelReference;
    TargetModelClass := TargetModelClass;
    TargetModelReference := TargetModelReference;

    resolveAll := resolveAllIter;
    resolve := resolveIter;

    (* lemmas *)

    tr_resolveAll_in := tr_resolveAllIter_in;
    tr_resolve_Leaf := tr_resolveIter_leaf;
  }. 

End IterateTracesCertification.