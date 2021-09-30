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
Require Import Bool.

Require Import core.utils.Utils.
Require Import core.Graph.
Require Import core.EqDec.
Require Import core.TransformationConfiguration.

Scheme Equality for list.

Set Implicit Arguments.

Class TransformationSyntax (tc: TransformationConfiguration) := {
    (** ** Syntax *)
    Transformation: Type;
    Rule: Type;
    OutputPatternNode: Type;
    OutputPatternEdge: Type;
    TraceLink: Type;

    (** ** Accessors *)

    Transformation_getRules: Transformation -> list Rule;
    Transformation_getArity: Transformation -> nat;
  
    Rule_getOutputPatternNodes: Rule -> list OutputPatternNode;

    OutputPatternNode_getOutputEdges: OutputPatternNode -> list OutputPatternEdge;

    TraceLink_getSourcePattern: TraceLink -> list SourceNode;
    TraceLink_getIterator: TraceLink -> nat;
    TraceLink_getName: TraceLink -> string;
    TraceLink_getTargetNode: TraceLink -> TargetNode;    

    evalOutputPatternNodeExpr: SourceGraph -> list SourceNode -> nat -> OutputPatternNode -> option TargetNode;
    evalIteratorExpr: Rule -> SourceGraph -> list SourceNode -> nat;
    evalOutputPatternEdgeExpr: SourceGraph -> list SourceNode -> TargetNode -> nat -> list TraceLink -> OutputPatternEdge -> option TargetEdge;
    evalGuardExpr: Rule->SourceGraph->list SourceNode->option bool;
}.
  
Class TransformationEngine (tc: TransformationConfiguration) (ts: TransformationSyntax tc) :=
  {
    (** ** allTuples *)

    allTuples (tr: Transformation) (sm : SourceGraph) :list (list SourceNode) :=
      tuples_up_to_n (allNodes sm) (Transformation_getArity tr);

    (** ** Functions *)
    
    execute: Transformation -> SourceGraph -> TargetGraph;
    
    matchPattern: Transformation -> SourceGraph -> list SourceNode -> list Rule;
    matchRuleOnPattern: Rule -> SourceGraph -> list SourceNode -> bool;

    instantiatePattern: Transformation -> SourceGraph -> list SourceNode -> list TargetNode;
    instantiateRuleOnPattern: Rule -> SourceGraph -> list SourceNode -> list TargetNode; 
    instantiateIterationOnPattern: Rule -> SourceGraph -> list SourceNode -> nat -> list TargetNode;
    instantiateNodeOnPattern: OutputPatternNode -> SourceGraph -> list SourceNode -> nat -> option TargetNode;
    
    applyPattern: Transformation -> SourceGraph -> list SourceNode -> list TargetEdge;
    applyRuleOnPattern: Rule -> Transformation -> SourceGraph -> list SourceNode -> list TargetEdge;
    applyIterationOnPattern: Rule -> Transformation -> SourceGraph -> list SourceNode -> nat -> list TargetEdge;
    applyNodeOnPattern: OutputPatternNode -> Transformation -> SourceGraph -> list SourceNode -> nat -> list TargetEdge;
    applyEdgeOnPattern: OutputPatternEdge -> Transformation -> SourceGraph -> list SourceNode -> nat -> TargetNode -> option TargetEdge;
    
    trace: Transformation -> SourceGraph -> list TraceLink; 

    resolveAll: forall (tr: list TraceLink) (sm: SourceGraph) (name: string)
             (sps: list(list SourceNode)) (iter: nat),
        option (list TargetNode);
    resolve: forall (tr: list TraceLink) (sm: SourceGraph) (name: string)
             (sp: list SourceNode) (iter : nat), option TargetNode;

    (** ** Theorems *)

    (** ** allTuples *)

    allTuples_incl:
      forall (sp : list SourceNode) (tr: Transformation) (sm: SourceGraph), 
        In sp (allTuples tr sm) -> incl sp (allNodes sm);

    (** ** execute *)

    tr_execute_in_elements :
      forall (tr: Transformation) (sm : SourceGraph) (te : TargetNode),
      In te (allNodes (execute tr sm)) <->
      (exists (sp : list SourceNode),
          In sp (allTuples tr sm) /\
          In te (instantiatePattern tr sm sp));

    tr_execute_in_links :
      forall (tr: Transformation) (sm : SourceGraph) (tl : TargetEdge),
        In tl (allEdges (execute tr sm)) <->
        (exists (sp : list SourceNode),
            In sp (allTuples tr sm) /\
            In tl (applyPattern tr sm sp));

    (** ** matchPattern *)

    tr_matchPattern_in :
       forall (tr: Transformation) (sm : SourceGraph),
         forall (sp : list SourceNode)(r : Rule),
           In r (matchPattern tr sm sp) <->
             In r (Transformation_getRules tr) /\
             matchRuleOnPattern r sm sp = true;

    (** ** matchRuleOnPattern *)

    tr_matchRuleOnPattern_leaf :
    forall (tr: Transformation) (sm : SourceGraph) (r: Rule) (sp: list SourceNode),
      matchRuleOnPattern r sm sp =
       match evalGuardExpr r sm sp with Some true => true | _ => false end;

    (** ** instantiatePattern *)

    tr_instantiatePattern_in :
      forall (tr: Transformation) (sm : SourceGraph) (sp: list SourceNode) (te : TargetNode),
        In te (instantiatePattern tr sm sp) <->
        (exists (r : Rule),
            In r (matchPattern tr sm sp) /\
            In te (instantiateRuleOnPattern r sm sp));

    (** ** instantiateRuleOnPattern *)

    tr_instantiateRuleOnPattern_in :
    forall (tr: Transformation) (r : Rule) (sm : SourceGraph) (sp: list SourceNode) (te : TargetNode),
      In te (instantiateRuleOnPattern r sm sp) <->
      (exists (i: nat),
          In i (seq 0 (evalIteratorExpr r sm sp)) /\
          In te (instantiateIterationOnPattern r sm sp i));

   (** ** instantiateIterationOnPattern *)

    tr_instantiateIterationOnPattern_in : 
      forall (r : Rule) (sm : SourceGraph) (sp: list SourceNode) (te : TargetNode) (i:nat),
        In te (instantiateIterationOnPattern r sm sp i)
        <->
        (exists (ope: OutputPatternNode),
            In ope (Rule_getOutputPatternNodes r) /\ 
            instantiateNodeOnPattern ope sm sp i = Some te);

    (** ** instantiateNodeOnPattern *)

    tr_instantiateNodeOnPattern_leaf:
        forall (o: OutputPatternNode) (sm: SourceGraph) (sp: list SourceNode) (iter: nat),
          instantiateNodeOnPattern o sm sp iter = evalOutputPatternNodeExpr sm sp iter o;

    (** ** applyPattern *)

    tr_applyPattern_in :
      forall (tr: Transformation) (sm : SourceGraph) (sp: list SourceNode) (tl : TargetEdge),
        In tl (applyPattern tr sm sp) <->
        (exists (r : Rule),
            In r (matchPattern tr sm sp) /\
            In tl (applyRuleOnPattern r tr sm sp));

    (** ** applyRuleOnPattern *)

    tr_applyRuleOnPattern_in : 
      forall (tr: Transformation) (r : Rule) (sm : SourceGraph) (sp: list SourceNode) (tl : TargetEdge),
        In tl (applyRuleOnPattern r tr sm sp) <->
        (exists (i: nat),
            In i (seq 0 (evalIteratorExpr r sm sp)) /\
            In tl (applyIterationOnPattern r tr sm sp i));

    (** ** applyIterationOnPattern *)

    tr_applyIterationOnPattern_in : 
      forall (tr: Transformation) (r : Rule) (sm : SourceGraph) (sp: list SourceNode) (tl : TargetEdge) (i:nat),
        In tl (applyIterationOnPattern r tr sm sp i) <->
        (exists (ope: OutputPatternNode),
            In ope (Rule_getOutputPatternNodes r) /\ 
            In tl (applyNodeOnPattern ope tr sm sp i));

    (** ** applyNodeOnPattern *)

    tr_applyNodeOnPattern_in : 
      forall (tr: Transformation) (sm : SourceGraph) (sp: list SourceNode) (tl : TargetEdge) 
             (i:nat) (ope: OutputPatternNode),
        In tl (applyNodeOnPattern ope tr sm sp i ) <->
        (exists (oper: OutputPatternEdge) (te: TargetNode),
            In oper (OutputPatternNode_getOutputEdges ope) /\ 
            (evalOutputPatternNodeExpr sm sp i ope) = Some te /\
            applyEdgeOnPattern oper tr sm sp i te = Some tl);

    (** ** applyEdgeOnPattern *)

    tr_applyEdgeOnPatternTraces_leaf : 
          forall (oper: OutputPatternEdge)
                 (tr: Transformation)
                 (sm: SourceGraph)
                 (sp: list SourceNode) (iter: nat) (te: TargetNode) (tls: list TraceLink),
            applyEdgeOnPattern oper tr sm sp iter te  = evalOutputPatternEdgeExpr sm sp te iter (trace tr sm) oper;

    (** ** resolve *)

    tr_resolveAll_in:
    forall (tls: list TraceLink) (sm: SourceGraph) (name: string)
           (sps: list(list SourceNode)) (iter: nat)
      (te: TargetNode),
      (exists tes: list TargetNode,
          resolveAll tls sm name sps iter = Some tes /\ In te tes) <->
      (exists (sp: list SourceNode),
          In sp sps /\
          resolve tls sm name sp iter = Some te);

    tr_resolve_leaf:
    forall (tls:list TraceLink) (sm : SourceGraph) (name: string)
      (sp: list SourceNode) (iter: nat) (x: TargetNode),
      resolve tls sm name sp iter = return x ->
       (exists (tl : TraceLink),
         In tl tls /\
         Is_true (list_beq SourceNode SourceNode_eqb (TraceLink_getSourcePattern tl) sp) /\
         ((TraceLink_getIterator tl) = iter) /\ 
         ((TraceLink_getName tl) = name)%string /\
         (TraceLink_getTargetNode tl) = x);
         
  }.
