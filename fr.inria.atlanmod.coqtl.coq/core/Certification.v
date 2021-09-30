Require Import String.
Require Import Omega.
Require Import Bool.

Require Import core.utils.Utils.
Require Import core.Graph.
Require Import core.Engine.
Require Import core.Syntax.
Require Import core.Semantics.
Require Import core.EqDec.
Require Import core.Schema.
Require Import core.TransformationConfiguration.
Require Import core.SyntaxCertification.
Require Import core.Expressions.

Section Certification.

Context {SourceNode SourceEdge: Type}.
Context {eqdec_sme: EqDec SourceNode}. (* need decidable equality on source model elements *)
Context {TargetNode TargetEdge: Type}.
Context {eqdec_tme: EqDec TargetNode}. (* need decidable equality on source model elements *)

Instance smm : Schema := {
  Node := SourceNode;
  Edge := SourceEdge;
  elements_eqdec := eqdec_sme;
}.

Instance tmm : Schema := {
  Node := TargetNode;
  Edge := TargetEdge;
  elements_eqdec := eqdec_tme;
}.

Instance tc : TransformationConfiguration := {
  SourceSchema := smm;
  TargetSchema := tmm;
}.

Lemma tr_execute_in_elements :
forall (tr: Transformation) (sm : SourceGraph) (te : TargetNode),
  In te (allNodes (execute tr sm)) <->
  (exists (sp : list SourceNode),
      In sp (allTuples tr sm) /\
      In te (instantiatePattern tr sm sp)).
Proof.
  intros.
  apply in_flat_map.
Qed.

Lemma tr_execute_in_links :
forall (tr: Transformation) (sm : SourceGraph) (tl : TargetEdge),
  In tl (allEdges (execute tr sm)) <->
  (exists (sp : list SourceNode),
      In sp (allTuples tr sm) /\
      In tl (applyPattern tr sm sp)).
Proof.
  intros.
  apply in_flat_map.
Qed.

Lemma tr_matchPattern_in :
forall (tr: Transformation) (sm : SourceGraph),
  forall (sp : list SourceNode)(r : Rule),
    In r (matchPattern tr sm sp) <->
      In r (Transformation_getRules tr) /\
      matchRuleOnPattern r sm sp = true.
Proof.
  intros.
  apply filter_In.
Qed.

Lemma tr_matchRuleOnPattern_leaf : 
forall (tr: Transformation) (sm : SourceGraph) (r: Rule) (sp: list SourceNode),
    matchRuleOnPattern r sm sp =
      match evalGuardExpr r sm sp with Some true => true | _ => false end.
Proof.
  crush.
Qed.

Lemma tr_instantiatePattern_in :
forall (tr: Transformation) (sm : SourceGraph) (sp: list SourceNode) (te : TargetNode),
  In te (instantiatePattern tr sm sp) <->
  (exists (r : Rule),
      In r (matchPattern tr sm sp) /\
      In te (instantiateRuleOnPattern r sm sp)).
Proof.
  intros.
  apply in_flat_map.
Qed.

Lemma tr_instantiateRuleOnPattern_in :
forall (tr: Transformation) (r : Rule) (sm : SourceGraph) (sp: list SourceNode) (te : TargetNode),
  In te (instantiateRuleOnPattern r sm sp) <->
  (exists (i: nat),
      In i (seq 0 (evalIteratorExpr r sm sp)) /\
      In te (instantiateIterationOnPattern r sm sp i)).
Proof.
  intros.
  apply in_flat_map.
Qed.

Lemma tr_instantiateIterationOnPattern_in : 
forall (r : Rule) (sm : SourceGraph) (sp: list SourceNode) (te : TargetNode) (i:nat),
  In te (instantiateIterationOnPattern r sm sp i)
  <->
  (exists (ope: OutputPatternNode),
      In ope (Rule_getOutputPatternNodes r) /\ 
      instantiateNodeOnPattern ope sm sp i = Some te).
Proof.
  split.
  * intros.
    apply in_flat_map in H.
    destruct H.
    exists x.
    unfold optionToList in H.
    destruct H.
    split. 
    - assumption.
    - destruct (instantiateNodeOnPattern x sm sp i).
      ** crush.
      ** contradiction.
  * intros.
    apply in_flat_map.
    destruct H.
    exists x.
    unfold optionToList.
    destruct H.
    split.
    - assumption.
    - crush.
Qed.

Lemma  tr_instantiateNodeOnPattern_leaf:
      forall (o: OutputPatternNode) (sm: SourceGraph) (sp: list SourceNode) (iter: nat),
        instantiateNodeOnPattern o sm sp iter = evalOutputPatternNodeExpr sm sp iter o.
Proof.
  crush.
Qed.

Lemma tr_applyPattern_in :
    forall (tr: Transformation) (sm : SourceGraph) (sp: list SourceNode) (tl : TargetEdge),
      In tl (applyPattern tr sm sp) <->
      (exists (r : Rule),
          In r (matchPattern tr sm sp) /\
          In tl (applyRuleOnPattern r tr sm sp)).
Proof.
  intros.
  apply in_flat_map.
Qed.

Lemma tr_applyRuleOnPattern_in : 
    forall (tr: Transformation) (r : Rule) (sm : SourceGraph) (sp: list SourceNode) (tl : TargetEdge),
      In tl (applyRuleOnPattern r tr sm sp) <->
      (exists (i: nat),
          In i (seq 0 (evalIteratorExpr r sm sp)) /\
          In tl (applyIterationOnPattern r tr sm sp i)).
Proof.
  intros.
  apply in_flat_map.
Qed.

Lemma tr_applyIterationOnPattern_in : 
    forall (tr: Transformation) (r : Rule) (sm : SourceGraph) (sp: list SourceNode) (tl : TargetEdge) (i:nat),
      In tl (applyIterationOnPattern r tr sm sp i) <->
      (exists (ope: OutputPatternNode),
          In ope (Rule_getOutputPatternNodes r) /\ 
          In tl (applyNodeOnPattern ope tr sm sp i)).
Proof.
  intros.
  apply in_flat_map.
Qed.

Lemma tr_applyNodeOnPattern_in : 
    forall (tr: Transformation) (sm : SourceGraph) (sp: list SourceNode) (tl : TargetEdge) 
            (i:nat) (ope: OutputPatternNode),
      In tl (applyNodeOnPattern ope tr sm sp i ) <->
      (exists (oper: OutputPatternEdge) (te: TargetNode),
          In oper (OutputPatternNode_getOutputEdges ope) /\ 
          (evalOutputPatternNodeExpr sm sp i ope) = Some te /\
          applyEdgeOnPattern oper tr sm sp i te = Some tl).
Proof.
  split.
  * intros.
    apply in_flat_map in H.
    destruct H.
    exists x.
    unfold optionToList in H.
    destruct H.
    destruct (evalOutputPatternNodeExpr sm sp i ope) eqn: eval_ca.
    - destruct (applyEdgeOnPattern x tr sm sp i t) eqn: ref_ca.
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

Lemma tr_applyEdgeOnPattern_leaf : 
        forall (oper: OutputPatternEdge)
                (tr: Transformation)
                (sm: SourceGraph)
                (sp: list SourceNode) (iter: nat) (te: TargetNode) (tls: list TraceLink),
          applyEdgeOnPattern oper tr sm sp iter te  = evalOutputPatternEdgeExpr sm sp te iter (trace tr sm) oper.
Proof.
  crush.
Qed.


(*TODO
Lemma maxArity_length:
  forall (sp : list SourceNode) (tr: Transformation) (sm: SourceGraph), 
  gt (length sp) (maxArity tr) -> In sp (allTuples tr sm) -> False.
*)


Lemma allTuples_incl:
  forall (sp : list SourceNode) (tr: Transformation) (sm: SourceGraph), 
  In sp (allTuples tr sm) -> incl sp (allNodes sm).
Proof.
  intros.
  unfold allTuples in H. simpl in H. 
  apply tuples_up_to_n_incl in H.
  assumption.
Qed.

Lemma allTuples_incl_length:
  forall (sp : list SourceNode) (tr: Transformation) (sm: SourceGraph), 
  incl sp (allNodes sm) -> length sp <= maxArity tr -> In sp (allTuples tr sm).
Proof.
  intros.
  unfold allTuples.
  apply tuples_up_to_n_incl_length with (n:=maxArity tr) in H.
  - assumption.
  - assumption.
Qed.

(** * Resolve *)

Theorem tr_resolveAll_in:
  forall (tls: list TraceLink) (sm: SourceGraph) (name: string)
    (sps: list(list SourceNode)),
    resolveAll tls sm name sps = resolveAllIter tls sm name sps 0.
Proof.
  crush.
Qed.

Theorem tr_resolveAllIter_in:
  forall (tls: list TraceLink) (sm: SourceGraph) (name: string)
          (sps: list(list SourceNode)) (iter: nat)
    (te: TargetNode),
    (exists tes: list TargetNode,
        resolveAllIter tls sm name sps iter = Some tes /\ In te tes) <->
    (exists (sp: list SourceNode),
        In sp sps /\
        resolveIter tls sm name sp iter = Some te).
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
    exists x0. split; auto.
    destruct (resolveIter tls sm name x0 iter).
    -- unfold optionToList in H1. crush.
    -- crush.
  - intros.
    destruct H. destruct H.
    remember (resolveAllIter tls sm name sps iter) as tes1.
    destruct tes1 eqn: resolveAll.
    -- exists l.
        split. auto.
        unfold resolveAllIter in Heqtes1.
        inversion Heqtes1.
        apply in_flat_map.
        exists x. split. auto.
        destruct (resolveIter tls sm name x iter).
        --- crush.
        --- crush.
    -- unfold resolveAllIter in Heqtes1.
        crush.
Qed.

(* this one direction, the other one is not true since exists cannot gurantee uniqueness in find *)
Theorem tr_resolveIter_leaf: 
  forall (tls:list TraceLink) (sm : SourceGraph) (name: string)
    (sp: list SourceNode) (iter: nat) (x: TargetNode),
    resolveIter tls sm name sp iter = return x ->
      (exists (tl : TraceLink),
        In tl tls /\
        Is_true (list_beq SourceNode (@elements_eqb smm) (TraceLink_getSourcePattern tl) sp) /\
        ((TraceLink_getIterator tl) = iter) /\ 
        ((TraceLink_getName tl) = name)%string /\
        (TraceLink_getTargetNode tl) = x).
Proof.
intros.
unfold resolveIter in H.
destruct (find (fun tl: TraceLink => 
(list_beq SourceNode (@elements_eqb smm) (@TraceLink_getSourcePattern tc tl) sp) &&
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
Admitted.
(**- crush.
Qed.**)

Instance CoqTLEngine :
  TransformationEngine CoqTLSyntax :=
  {

    (* semantic functions *)

    execute := execute;

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

    trace := trace;

    resolveAll := resolveAllIter;
    resolve := resolveIter;

    (* lemmas *)

    tr_execute_in_elements := tr_execute_in_elements;
    tr_execute_in_links := tr_execute_in_links;

    tr_matchPattern_in := tr_matchPattern_in;
    tr_matchRuleOnPattern_leaf := tr_matchRuleOnPattern_leaf;

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
    tr_resolve_leaf := tr_resolveIter_leaf;

    allTuples_incl := allTuples_incl;
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



(* matched sp must produce matched rule's output element 
  genearlization of lemma such as: Attribute_name_preservation
*)

Lemma tr_match_injective :
forall (sm : SourceGraph)(sp : list SourceNode)(r : Rule)(iter: nat),
    In iter (seq 0 (evalIteratorExpr r sm sp)) /\ 
    (exists ope, In ope (Rule_getOutputPatternNodes r) /\  (evalOutputPatternNodeExpr sm sp iter ope) <> None ) ->
      (exists (te: TargetNode),  In te (instantiateRuleOnPattern r sm sp) ).
Proof.
intros.
destruct H as [Hiter Hope].
destruct Hope as [ope HopeIn].
destruct HopeIn as [HopeInr HopeEval].
apply option_res_dec in HopeEval.
destruct HopeEval as [te Hte].
exists te.
unfold instantiateRuleOnPattern.
apply in_flat_map.
exists iter.
split.
- exact Hiter.
- unfold instantiateIterationOnPattern.
apply in_flat_map.
exists ope. 
split. 
-- exact HopeInr.
-- unfold instantiateNodeOnPattern.
    rewrite Hte.
    simpl. left. reflexivity.
Qed.

(* if In te (instantiateRuleOnPattern r sm sp) => tr_instantiatePattern_in
    In te (instantiatePattern tr sm sp) => by tr_execute_in_elements
    In te (allNodes (execute tr sm)) 
    *)

Theorem tr_instantiateRuleAndIterationOnPattern_in :
forall (tr: Transformation) (r : Rule) (sm : SourceGraph) (sp: list SourceNode) (te : TargetNode),
  In te (instantiateRuleOnPattern r sm sp) <->
  (exists (i: nat) (ope: OutputPatternNode),
      In i (seq 0 (evalIteratorExpr r sm sp)) /\
      In ope (Rule_getOutputPatternNodes r) /\ 
        instantiateNodeOnPattern ope sm sp i = Some te).
Proof.
  intros.
  split.
  - intros.
    apply tr_instantiateRuleOnPattern_in in H.
    repeat destruct H.
    exists x.
    apply tr_instantiateIterationOnPattern_in in H0.
    repeat destruct H0.
    exists x0.
    auto.
    exact tr.
  - intros.
    repeat destruct H.
    destruct H0.
    apply tr_instantiateRuleOnPattern_in.
    exact tr.
    exists x.
    split.
    + assumption.
    + apply tr_instantiateIterationOnPattern_in.
      exists x0.
      auto. 
Qed.

Theorem tr_instantiateRuleAndIterationOnPattern_in' :
forall (tr: Transformation) (r : Rule) (sm : SourceGraph) (sp: list SourceNode) (te : TargetNode),
  In te (instantiateRuleOnPattern r sm sp) <->
  (exists (i: nat),
      In i (seq 0 (evalIteratorExpr r sm sp)) /\
      (exists (ope: OutputPatternNode),
      In ope (Rule_getOutputPatternNodes r) /\ 
        instantiateNodeOnPattern ope sm sp i = Some te)).
Proof.
  intros.
  specialize (tr_instantiateRuleOnPattern_in tr r sm sp te) as inst.
Admitted. (* 
  rewrite tr_instantiateIterationOnPattern_in with (r:=r) (sp:=sp) (te:=te) (sm:=sm)  in inst.
  assumption. *)

End Certification.