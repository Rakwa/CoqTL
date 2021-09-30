(************************************************************************)
(*         *   The NaoMod Development Team                              *)
(*  v      *   INRIA, CNRS and contributors - Copyright 2017-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(**
 This file is the type class for relational transformation engine.
 
 We give functions signatures that instaniated transformation engines should
    generally have. We also introduce several useful theorems enforced on these 
    functions in order to certify instaniated transformation engines.

 An example instaniated transformation engine is in [core.Certification].        **)


(*********************************************************)
(** * Type Class for relational Transformation Engines   *)
(*********************************************************)

Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.utils.Utils.
Require Import core.Graph.
Require Import core.Engine.
Require Import core.TransformationConfiguration.

Set Implicit Arguments.

Class TransformationEngineTrace (tc: TransformationConfiguration) (ts: TransformationSyntax tc)
 (t: TransformationEngine ts) :=
  {

    (** ** Accessors *)

    OutputPatternNode_getName: OutputPatternNode -> string;

    (* getGuardExpr: Rule -> (SourceGraph -> (list SourceNode) -> option bool); *)

    Trace_buildTraceLink: (list SourceNode * nat * string) -> TargetNode -> TraceLink;


    (** ** Functions *)

    tracePattern: Transformation -> SourceGraph -> list SourceNode -> list TraceLink;
    traceRuleOnPattern: Rule -> SourceGraph -> list SourceNode -> list TraceLink;
    traceIterationOnPattern: Rule -> SourceGraph -> list SourceNode -> nat -> list TraceLink;
    traceNodeOnPattern: OutputPatternNode -> SourceGraph -> list SourceNode -> nat -> option TraceLink;

    applyPatternTraces: Transformation -> SourceGraph -> list SourceNode -> list TraceLink -> list TargetEdge;
    applyRuleOnPatternTraces: Rule -> Transformation -> SourceGraph -> list SourceNode -> list TraceLink -> list TargetEdge;
    applyIterationOnPatternTraces: Rule -> Transformation -> SourceGraph -> list SourceNode -> nat -> list TraceLink -> list TargetEdge;
    applyNodeOnPatternTraces: OutputPatternNode -> Transformation -> SourceGraph -> list SourceNode -> nat -> list TraceLink -> list TargetEdge;
    applyEdgeOnPatternTraces: OutputPatternEdge -> Transformation -> SourceGraph -> list SourceNode -> nat -> TargetNode -> list TraceLink -> option TargetEdge;

    (** ** Theorems *)

    (** ** execute *)

    tr_executeTraces_in_elements :
      forall (tr: Transformation) (sm : SourceGraph) (te : TargetNode),
        In te (allNodes (execute tr sm)) <->
        (exists (tl : TraceLink) (sp : list SourceNode),
            In sp (allTuples tr sm) /\
            In tl (tracePattern tr sm sp) /\
            te = TraceLink_getTargetNode tl);

    tr_executeTraces_in_links :
      forall (tr: Transformation) (sm : SourceGraph) (tl : TargetEdge),
        In tl (allEdges (execute tr sm)) <->
            (exists (sp : list SourceNode),
            In sp (allTuples tr sm) /\
            In tl (applyPatternTraces tr sm sp (trace tr sm)));

    (** ** instantiate *)

    tr_tracePattern_in:
      forall (tr: Transformation) (sm : SourceGraph) (sp : list SourceNode) (tl : TraceLink),
        In tl (tracePattern tr sm sp) <->
        (exists (r:Rule),
            In r (matchPattern tr sm sp) /\
            In tl (traceRuleOnPattern r sm sp));

    tr_traceRuleOnPattern_in:
      forall (r: Rule) (sm : SourceGraph) (sp : list SourceNode) (tl : TraceLink),
        In tl (traceRuleOnPattern r sm sp) <->
        (exists (iter: nat),
            In iter (seq 0 (evalIteratorExpr r sm sp)) /\
            In tl (traceIterationOnPattern r sm sp iter));

    tr_traceIterationOnPattern_in:
      forall (r: Rule) (sm : SourceGraph) (sp : list SourceNode) (iter: nat) (tl : TraceLink),
        In tl (traceIterationOnPattern r sm sp iter) <->
        (exists (o: OutputPatternNode),
            In o (Rule_getOutputPatternNodes r) /\
            In tl ((fun o => optionToList (traceNodeOnPattern o sm sp iter)) o));

    tr_traceNodeOnPattern_leaf:
      forall (o: OutputPatternNode) (sm : SourceGraph) (sp : list SourceNode) (iter: nat) (o: OutputPatternNode) (tl : TraceLink),
        Some tl = (traceNodeOnPattern o sm sp iter) <->
        (exists (e: TargetNode),
           Some e = (instantiateNodeOnPattern o sm sp iter) /\
           tl = (Trace_buildTraceLink (sp, iter, OutputPatternNode_getName o) e));


    (** ** applyPattern *)

    tr_applyPatternTraces_in:
      forall (tr: Transformation) (sm : SourceGraph) (sp: list SourceNode) (tl : TargetEdge) (tls: list TraceLink),
        In tl (applyPatternTraces tr sm sp tls) <->
        (exists (r : Rule),
                In r (matchPattern tr sm sp) /\
                In tl (applyRuleOnPatternTraces r tr sm sp tls));

    tr_applyRuleOnPatternTraces_in : 
      forall (tr: Transformation) (r : Rule) (sm : SourceGraph) (sp: list SourceNode) (tl : TargetEdge) (tls: list TraceLink),
          In tl (applyRuleOnPatternTraces r tr sm sp tls) <->
          (exists (i: nat),
              In i (seq 0 (evalIteratorExpr r sm sp)) /\
              In tl (applyIterationOnPatternTraces r tr sm sp i tls));

    tr_applyIterationOnPatternTraces_in : 
          forall (tr: Transformation) (r : Rule) (sm : SourceGraph) (sp: list SourceNode) (tl : TargetEdge) (i:nat)  (tls: list TraceLink),
            In tl (applyIterationOnPatternTraces r tr sm sp i tls) <->
            (exists (ope: OutputPatternNode),
                In ope (Rule_getOutputPatternNodes r) /\ 
                In tl (applyNodeOnPatternTraces ope tr sm sp i tls));

    tr_applyNodeOnPatternTraces_in : 
          forall (tr: Transformation) (sm : SourceGraph) (sp: list SourceNode) (tl : TargetEdge) 
                 (i:nat) (ope: OutputPatternNode)  (tls: list TraceLink),
            In tl (applyNodeOnPatternTraces ope tr sm sp i tls) <->
            (exists (oper: OutputPatternEdge) (te: TargetNode),
                In oper (OutputPatternNode_getOutputEdges ope) /\ 
                (evalOutputPatternNodeExpr sm sp i ope) = Some te /\
                applyEdgeOnPatternTraces oper tr sm sp i te tls = Some tl);

    tr_applyEdgeOnPatternTraces_leaf : 
          forall (oper: OutputPatternEdge)
                 (tr: Transformation)
                 (sm: SourceGraph)
                 (sp: list SourceNode) (iter: nat) (te: TargetNode) (tls: list TraceLink),
            applyEdgeOnPatternTraces oper tr sm sp iter te tls  = evalOutputPatternEdgeExpr sm sp te iter tls oper;

  }.