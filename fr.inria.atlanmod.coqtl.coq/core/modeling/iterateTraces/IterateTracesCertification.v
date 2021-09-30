Require Import String.
Require Import Omega.
Require Import Bool.
Require Import core.utils.Utils.
Require Import core.modeling.Schema.
Require Import core.Graph.
Require Import core.Engine.
Require Import core.Syntax.
Require Import core.Semantics.
Require Import core.Certification.
Require Import core.EqDec.
Require Import core.modeling.iteratetraces.IterateTracesSemantics.
Require Import Coq.Logic.FunctionalExtensionality.


Section IterateTracesCertification.

Context {tc: TransformationConfiguration} {mtc: ModelingTransformationConfiguration tc}. 

(** EXECUTE TRACE *)

Lemma tr_executeTraces_in_elements :
forall (tr: Transformation) (sm : SourceGraph) (te : TargetNode),
      In te (allNodes (executeTraces tr sm)) <->
      (exists (tl : TraceLink) (sp : list SourceNode),
          In sp (allTuples tr sm) /\
          In tl (tracePattern tr sm sp) /\
          te = TraceLink_getTargetNode tl).
Proof.
  intros.
  split.
  + intro. 
    assert (exists (tl : TraceLink),
                In tl (trace tr sm) /\
                te = (TraceLink_getTargetNode tl) ).
    { simpl in H.
          induction (trace tr sm).
          ++ crush.
          ++ intros.
              simpl in H.
              destruct H. 
              +++ exists a.
                  crush.
              +++ specialize (IHl H).
                  destruct IHl.
                  exists x.
                  crush. }
    destruct H0.
    destruct H0.
    assert (exists (sp : list SourceNode),
                In sp (allTuples tr sm) /\
                In x (tracePattern tr sm sp)).
    { apply in_flat_map. crush. }
    destruct H2.
    destruct H2.
    exists x. exists x0.
    crush.
  + intros.
    destruct H. 
    destruct H.
    destruct H.
    destruct H0.
    rewrite H1.
    apply in_map.
    apply in_flat_map.
    exists x0.
    split. 
    ++ exact H.
    ++ exact H0.
Qed. 

(** Instantiate *)

(* Please check the lemma formula *)

(* These lemmas of traces are useful when we get sth like (In e traces) *)

Lemma tr_trace_in:
forall (tr: Transformation) (sm : SourceGraph) (tl : TraceLink),
  In tl (trace tr sm) <->
  (exists (sp : list SourceNode),
      In sp (allTuples tr sm) /\
      In tl (tracePattern tr sm sp)).
Proof.
  intros.
  apply in_flat_map.
Qed.

Lemma tr_tracePattern_in:
forall (tr: Transformation) (sm : SourceGraph) (sp : list SourceNode) (tl : TraceLink),
  In tl (tracePattern tr sm sp) <->
  (exists (r:Rule),
      In r (matchPattern tr sm sp) /\
      In tl (traceRuleOnPattern r sm sp)).
Proof.
  intros.
  apply in_flat_map.
Qed.

Lemma tr_traceRuleOnPattern_in:
forall (r: Rule) (sm : SourceGraph) (sp : list SourceNode) (tl : TraceLink),
  In tl (traceRuleOnPattern r sm sp) <->
  (exists (iter: nat),
      In iter (seq 0 (evalIteratorExpr r sm sp)) /\
      In tl (traceIterationOnPattern r sm sp iter)).
Proof.
  intros.
  apply in_flat_map.
Qed.

Lemma tr_traceIterationOnPattern_in:
forall (r: Rule) (sm : SourceGraph) (sp : list SourceNode) (iter: nat) (tl : TraceLink),
  In tl (traceIterationOnPattern r sm sp iter) <->
  (exists (o: OutputPatternNode),
      In o (Rule_getOutputPatternNodes r) /\
      In tl ((fun o => optionToList (traceNodeOnPattern o sm sp iter)) o)).
Proof.
  intros.
  apply in_flat_map.
Qed.

(* TODO works inside TwoPhaseSemantics.v *)
Lemma tr_traceNodeOnPattern_leaf:
forall (o: OutputPatternNode) (sm : SourceGraph) (sp : list SourceNode) (iter: nat) (o: OutputPatternNode) (tl : TraceLink),
  Some tl = (traceNodeOnPattern o sm sp iter) <->
  (exists (e: TargetNode),
      Some e = (instantiateNodeOnPattern o sm sp iter) /\
      tl = (buildTraceLink (sp, iter, OutputPatternNode_getName o) e)).
Proof.
  intros.
  split.
  - intros. 
    unfold traceNodeOnPattern in H.
    destruct (instantiateNodeOnPattern o0 sm sp iter) eqn: e1.
    -- exists t.
      split. crush. crush.
    -- crush.
  - intros.
    destruct H.
    destruct H.
    unfold traceNodeOnPattern.
    destruct (instantiateNodeOnPattern o0 sm sp iter).
    -- crush.
    -- crush.
Qed.

(** * Apply **)



Lemma tr_applyPatternTraces_in:
forall (tr: Transformation) (sm : SourceGraph) (sp: list SourceNode) (tl : TargetEdge) (tls: list TraceLink),
  In tl (applyPatternTraces tr sm sp tls) <->
  (exists (r : Rule),
          In r (matchPattern tr sm sp) /\
          In tl (applyRuleOnPatternTraces r tr sm sp tls)).
Proof.
  intros.
  apply in_flat_map.
Qed.

Lemma tr_applyRuleOnPatternTraces_in : 
forall (tr: Transformation) (r : Rule) (sm : SourceGraph) (sp: list SourceNode) (tl : TargetEdge) (tls: list TraceLink),
    In tl (applyRuleOnPatternTraces r tr sm sp tls) <->
    (exists (i: nat),
        In i (seq 0 (evalIteratorExpr r sm sp)) /\
        In tl (applyIterationOnPatternTraces r tr sm sp i tls)).
Proof.
  intros.
  apply in_flat_map.
Qed.

Lemma tr_applyIterationOnPatternTraces_in : 
    forall (tr: Transformation) (r : Rule) (sm : SourceGraph) (sp: list SourceNode) (tl : TargetEdge) (i:nat)  (tls: list TraceLink),
      In tl (applyIterationOnPatternTraces r tr sm sp i tls) <->
      (exists (ope: OutputPatternNode),
          In ope (Rule_getOutputPatternNodes r) /\ 
          In tl (applyNodeOnPatternTraces ope tr sm sp i tls)).
Proof.
  intros.
  apply in_flat_map.
Qed.

Lemma tr_applyNodeOnPatternTraces_in : 
    forall (tr: Transformation) (sm : SourceGraph) (sp: list SourceNode) (tl : TargetEdge) 
            (i:nat) (ope: OutputPatternNode)  (tls: list TraceLink),
      In tl (applyNodeOnPatternTraces ope tr sm sp i tls) <->
      (exists (oper: OutputPatternEdge) (te: TargetNode),
          In oper (OutputPatternNode_getOutputEdges ope) /\ 
          (evalOutputPatternNodeExpr sm sp i ope) = Some te /\
          applyEdgeOnPatternTraces oper tr sm sp i te tls = Some tl).
Proof.
  split.
  * intros.
    apply in_flat_map in H.
    destruct H.
    exists x.
    unfold optionToList in H.
    destruct H.
    destruct (evalOutputPatternNodeExpr sm sp i ope) eqn: eval_ca.
    - destruct (applyEdgeOnPatternTraces x tr sm sp i t) eqn: ref_ca.
      -- eexists t.
          split; crush.
      -- contradiction.
    - contradiction.
  * intros.
    apply in_flat_map.
    destruct H.
    exists x.
    unfold optionToList.
    destruct H.
    destruct H.
    destruct H0.
    split.
    - assumption.
    - crush.
Qed.

Lemma tr_applyEdgeOnPatternTraces_leaf : 
    forall (oper: OutputPatternEdge)
            (tr: Transformation)
            (sm: SourceGraph)
            (sp: list SourceNode) (iter: nat) (te: TargetNode) (tls: list TraceLink),
      applyEdgeOnPatternTraces oper tr sm sp iter te tls  = evalOutputPatternEdgeExpr sm sp te iter tls oper.
Proof.
  crush.
Qed.

Lemma tr_applyTraces_in :
forall (tr: Transformation) (sm : SourceGraph) (tl : TargetEdge),
  In tl (applyTraces tr sm (trace tr sm)) <->
  (exists (sp : list SourceNode),
      In sp (allTuples tr sm) /\
      In tl (applyPatternTraces tr sm sp (trace tr sm))).
Proof.
  split.
  - intros.
    apply in_flat_map in H.
    destruct H.
    exists x.
    crush.
    apply In_noDup_sp in H0.
    unfold trace in H0.
    induction (allTuples tr sm).
    * simpl in H0. contradiction.
    * simpl. simpl in H0. 
      rewrite map_app in H0.
Admitted. (*
      apply in_app_or in H0.
      destruct H0.
      + left.
        unfold tracePattern in H.
        induction (matchPattern tr sm a).
        -- simpl in H. contradiction.
        -- simpl in H.
          rewrite map_app in H.
          apply in_app_or in H.            
          destruct H.
          ** apply in_map_iff in H.
            destruct H. destruct H.
            apply tr_traceRuleOnPattern_in in H0.
            destruct H0. destruct H0.
            apply tr_traceIterationOnPattern_in in H2.
            destruct H2. destruct H2.
            unfold traceNodeOnPattern in H3.
            destruct (instantiateNodeOnPattern x2 sm a x1) eqn:inst.
            simpl in H3.
            destruct H3.
            *** rewrite <- H3 in H. simpl in H. 
                assumption.
            *** contradiction.
            *** contradiction.
          ** apply IHl0 in H. assumption.
      + auto.
    - intros.
      destruct H. destruct H.
      unfold applyTraces.
      apply in_flat_map.
      exists x.
      crush.
      unfold trace.
      unfold tracePattern.

      apply tr_applyPatternTraces_in in H0.
      repeat destruct H0.
      apply tr_matchPattern_in in H0.
      repeat destruct H0.
      induction (allTuples tr sm).
      + contradiction.
      + simpl in H. simpl.
Admitted.*)

Lemma tr_executeTraces_in_links :
forall (tr: Transformation) (sm : SourceGraph) (tl : TargetEdge),
      In tl (allEdges (executeTraces tr sm)) <->
          (exists (sp : list SourceNode),
          In sp (allTuples tr sm) /\
          In tl (applyPatternTraces tr sm sp (trace tr sm))).
Proof.
  apply tr_applyTraces_in.
Qed.

Theorem exe_preserv : 
  forall (tr: Transformation) (sm : SourceGraph),
    core.modeling.iteratetraces.IterateTracesSemantics.executeTraces tr sm = core.Semantics.execute tr sm.
Proof.
  intros.
  unfold core.Semantics.execute, executeTraces. simpl.
  f_equal.

  unfold trace.
  rewrite flat_map_concat_map. rewrite flat_map_concat_map.
  rewrite concat_map. f_equal.
  rewrite map_map. f_equal.

  unfold tracePattern, Semantics.instantiatePattern.
  apply functional_extensionality. intros.
  rewrite flat_map_concat_map. rewrite flat_map_concat_map.
  rewrite concat_map. f_equal.
  rewrite map_map. f_equal.

  unfold traceRuleOnPattern, Semantics.instantiateRuleOnPattern.
  apply functional_extensionality. intros.
  rewrite flat_map_concat_map. rewrite flat_map_concat_map.
  rewrite concat_map. f_equal.
  rewrite map_map. f_equal.

  unfold traceIterationOnPattern, Semantics.instantiateIterationOnPattern.
  apply functional_extensionality. intros.
  rewrite flat_map_concat_map. rewrite flat_map_concat_map.
  rewrite concat_map. f_equal.
  rewrite map_map. f_equal.

  unfold traceNodeOnPattern.
  apply functional_extensionality. intros.
  (* TODO FACTOR OUT *)
  assert ((Semantics.instantiateNodeOnPattern x2 sm x x1) = (instantiateNodeOnPattern x2 sm x x1)).
  { crush. }
  destruct (instantiateNodeOnPattern x2 sm x x1). 
  reflexivity. reflexivity.  
Admitted. 

Lemma tr_execute_in_elements' :
forall (tr: Transformation) (sm : SourceGraph) (te : TargetNode),
  In te (allNodes (executeTraces tr sm)) <->
  (exists (sp : list SourceNode),
      In sp (allTuples tr sm) /\
      In te (instantiatePattern tr sm sp)).
Proof.
  intros.
  assert ((executeTraces tr sm) = (execute tr sm)). { apply exe_preserv. }
  rewrite H.
  specialize (Certification.tr_execute_in_elements tr sm te).
  crush.
Qed.

Lemma tr_execute_in_links' :
forall (tr: Transformation) (sm : SourceGraph) (tl : TargetEdge),
  In tl (allEdges (executeTraces tr sm)) <->
  (exists (sp : list SourceNode),
      In sp (allTuples tr sm) /\
      In tl (applyPattern tr sm sp)).
Proof.
  intros.
  assert ((executeTraces tr sm) = (execute tr sm)). { apply exe_preserv. }
  rewrite H.
  specialize (Certification.tr_execute_in_links tr sm tl).
  crush.
Qed.
(*
Instance CoqTLEngine :
  TransformationEngine :=
  {
    SourceNode := SourceNode;
    SourceGraphClass := SourceGraphClass;
    SourceEdge := SourceEdge;
    SourceGraphReference := SourceGraphReference;
    TargetNode := TargetNode;
    TargetGraphClass := TargetGraphClass;
    TargetEdge := TargetEdge;
    TargetGraphReference := TargetGraphReference;

    (* syntax and accessors *)

    Transformation := Transformation;
    Rule := Rule;
    OutputPatternNode := OutputPatternNode;
    OutputPatternEdge := OutputPatternEdge;

    TraceLink := TraceLink;

    Transformation_getRules := Transformation_getRules;

    Rule_getInTypes := Rule_getInTypes;
    Rule_getOutputPatternNodes := Rule_getOutputPatternNodes;

    OutputPatternNode_getOutputEdges := OutputPatternNode_getOutputEdges;

    TraceLink_getSourcePattern := TraceLink_getSourcePattern;
    TraceLink_getIterator := TraceLink_getIterator;
    TraceLink_getName := TraceLink_getName;
    TraceLink_getTargetNode := TraceLink_getTargetNode;

    (* semantic functions *)

    execute := executeTraces;

    matchPattern := matchPattern;
    matchRuleOnPattern := matchRuleOnPattern;

    instantiatePattern := instantiatePattern;
    instantiateRuleOnPattern := instantiateRuleOnPattern;
    instantiateIterationOnPattern := instantiateIterationOnPattern;
    instantiateNodeOnPattern := instantiateNodeOnPattern;

    applyPattern := applyPattern;
    applyRuleOnPattern := applyRuleOnPattern;
    applyIterationOnPattern := applyIterationOnPattern;
    applyNodeOnPattern := applyNodeOnPattern;
    applyEdgeOnPattern := applyEdgeOnPattern;

    evalOutputPatternNodeExpr := evalOutputPatternNodeExpr;
    evalIteratorExpr := evalIteratorExpr;
    evalOutputPatternEdgeExpr := evalOutputPatternEdgeExpr;
    evalGuardExpr := evalGuardExpr;

    trace := trace;

    resolveAll := resolveAllIter;
    resolve := resolveIter;

    (* lemmas *)

    tr_execute_in_elements := tr_execute_in_elements';
    tr_execute_in_links := tr_execute_in_links';

    tr_matchPattern_in := tr_matchPattern_in;
    tr_matchRuleOnPattern_Leaf := tr_matchRuleOnPattern_Leaf;

    tr_instantiatePattern_in := tr_instantiatePattern_in;
    tr_instantiateRuleOnPattern_in := tr_instantiateRuleOnPattern_in;
    tr_instantiateIterationOnPattern_in := tr_instantiateIterationOnPattern_in;
    tr_instantiateNodeOnPattern_leaf := tr_instantiateNodeOnPattern_leaf;

    tr_applyPattern_in := tr_applyPattern_in;
    tr_applyRuleOnPattern_in := tr_applyRuleOnPattern_in;
    tr_applyIterationOnPattern_in := tr_applyIterationOnPattern_in;
    tr_applyNodeOnPattern_in := tr_applyNodeOnPattern_in;
    tr_applyEdgeOnPatternTraces_leaf := tr_applyEdgeOnPattern_leaf;

    tr_resolveAll_in := tr_resolveAllIter_in;
    tr_resolve_Leaf := tr_resolveIter_leaf;

    (*tr_matchPattern_None := tr_matchPattern_None;

    tr_matchRuleOnPattern_None := tr_matchRuleOnPattern_None;

    tr_instantiatePattern_non_None := tr_instantiatePattern_non_None;
    tr_instantiatePattern_None := tr_instantiatePattern_None;

    tr_instantiateRuleOnPattern_non_None := tr_instantiateRuleOnPattern_non_None;

    tr_instantiateIterationOnPattern_non_None := tr_instantiateIterationOnPattern_non_None;

    tr_instantiateNodeOnPattern_None := tr_instantiateNodeOnPattern_None;
    tr_instantiateNodeOnPattern_None_iterator := tr_instantiateNodeOnPattern_None_iterator;

    tr_applyPattern_non_None := tr_applyPattern_non_None;
    tr_applyPattern_None := tr_applyPattern_None;

    tr_applyRuleOnPattern_non_None := tr_applyRuleOnPattern_non_None;

    tr_applyIterationOnPattern_non_None := tr_applyIterationOnPattern_non_None;

    tr_applyNodeOnPattern_non_None := tr_applyNodeOnPattern_non_None;

    tr_applyEdgeOnPattern_None := tr_applyEdgeOnPattern_None;
    tr_applyEdgeOnPattern_None_iterator := tr_applyEdgeOnPattern_None_iterator;

    tr_maxArity_in := tr_maxArity_in;

    tr_instantiateNodeOnPattern_Leaf := tr_instantiateNodeOnPattern_Leaf;
    tr_applyEdgeOnPattern_Leaf := tr_applyEdgeOnPattern_Leaf;
    tr_matchRuleOnPattern_Leaf := tr_matchRuleOnPattern_Leaf;

    tr_resolveAll_in := tr_resolveAllIter_in;
    tr_resolve_Leaf := tr_resolveIter_Leaf';*)
  }.


Instance CoqTLEngineTrace :
  (TransformationEngineTrace CoqTLEngine).
Proof.
  eexists.
(* tr_executeTraces_in_elements *) exact tr_executeTraces_in_elements.
(* tr_executeTraces_in_links *) exact tr_executeTraces_in_links.

(* tr_tracePattern_in *) exact tr_tracePattern_in.
(* tr_traceRuleOnPattern_in *) exact tr_traceRuleOnPattern_in.
(* tr_traceIterationOnPattern_in *) exact tr_traceIterationOnPattern_in.
(* tr_traceNodeOnPattern_leaf *) exact tr_traceNodeOnPattern_leaf.

(* tr_applyPatternTraces_in  *) exact tr_applyPatternTraces_in.
(* tr_applyRuleOnPattern_in *) exact tr_applyRuleOnPatternTraces_in.
(* tr_applyIterationOnPattern_in *) exact tr_applyIterationOnPatternTraces_in.
(* tr_applyNodeOnPatternTraces_in *) exact tr_applyNodeOnPatternTraces_in.
(* tr_applyEdgeOnPatternTraces_leaf *) exact tr_applyEdgeOnPatternTraces_leaf.

Qed.
*)


End IterateTracesCertification.