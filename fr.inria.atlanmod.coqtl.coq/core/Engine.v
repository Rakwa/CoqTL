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
Require Import core.Model.
Require Import core.EqDec.
Require Import core.TransformationConfiguration.

Scheme Equality for list.

Set Implicit Arguments.

Class TransformationSyntax (tc: TransformationConfiguration) := {
    (** ** Syntax *)
    Transformation: Type;
    Rule: Type;
    OutputPatternElement: Type;
    OutputPatternLink: Type;
    TraceLink: Type;

    (** ** Accessors *)

    Transformation_getRules: Transformation -> list Rule;
    Transformation_getArity: Transformation -> nat;
  
    Rule_getOutputPatternElements: Rule -> list OutputPatternElement;

    OutputPatternElement_getOutputLinks: OutputPatternElement -> list OutputPatternLink;

    TraceLink_getSourcePattern: TraceLink -> list SourceNode;
    TraceLink_getIterator: TraceLink -> nat;
    TraceLink_getName: TraceLink -> string;
    TraceLink_getTargetElement: TraceLink -> TargetNode;    

    evalOutputPatternElementExpr: SourceModel -> list SourceNode -> nat -> OutputPatternElement -> option TargetNode;
    evalIteratorExpr: Rule -> SourceModel -> list SourceNode -> nat;
    evalOutputPatternLinkExpr: SourceModel -> list SourceNode -> TargetNode -> nat -> list TraceLink -> OutputPatternLink -> option TargetEdge;
    evalGuardExpr: Rule->SourceModel->list SourceNode->option bool;
}.
  
Class TransformationEngine (tc: TransformationConfiguration) (ts: TransformationSyntax tc) :=
  {
    (** ** allTuples *)

    allTuples (tr: Transformation) (sm : SourceModel) :list (list SourceNode) :=
      tuples_up_to_n (allNodes sm) (Transformation_getArity tr);

    (** ** Functions *)
    
    execute: Transformation -> SourceModel -> TargetModel;
    
    matchPattern: Transformation -> SourceModel -> list SourceNode -> list Rule;
    matchRuleOnPattern: Rule -> SourceModel -> list SourceNode -> bool;

    instantiatePattern: Transformation -> SourceModel -> list SourceNode -> list TargetNode;
    instantiateRuleOnPattern: Rule -> SourceModel -> list SourceNode -> list TargetNode; 
    instantiateIterationOnPattern: Rule -> SourceModel -> list SourceNode -> nat -> list TargetNode;
    instantiateElementOnPattern: OutputPatternElement -> SourceModel -> list SourceNode -> nat -> option TargetNode;
    
    applyPattern: Transformation -> SourceModel -> list SourceNode -> list TargetEdge;
    applyRuleOnPattern: Rule -> Transformation -> SourceModel -> list SourceNode -> list TargetEdge;
    applyIterationOnPattern: Rule -> Transformation -> SourceModel -> list SourceNode -> nat -> list TargetEdge;
    applyElementOnPattern: OutputPatternElement -> Transformation -> SourceModel -> list SourceNode -> nat -> list TargetEdge;
    applyLinkOnPattern: OutputPatternLink -> Transformation -> SourceModel -> list SourceNode -> nat -> TargetNode -> option TargetEdge;
    
    trace: Transformation -> SourceModel -> list TraceLink; 

    resolveAll: forall (tr: list TraceLink) (sm: SourceModel) (name: string)
             (sps: list(list SourceNode)) (iter: nat),
        option (list TargetNode);
    resolve: forall (tr: list TraceLink) (sm: SourceModel) (name: string)
             (sp: list SourceNode) (iter : nat), option TargetNode;

    (** ** Theorems *)

    (** ** allTuples *)

    allTuples_incl:
      forall (sp : list SourceNode) (tr: Transformation) (sm: SourceModel), 
        In sp (allTuples tr sm) -> incl sp (allNodes sm);

    (** ** execute *)

    tr_execute_in_elements :
      forall (tr: Transformation) (sm : SourceModel) (te : TargetNode),
      In te (allNodes (execute tr sm)) <->
      (exists (sp : list SourceNode),
          In sp (allTuples tr sm) /\
          In te (instantiatePattern tr sm sp));

    tr_execute_in_links :
      forall (tr: Transformation) (sm : SourceModel) (tl : TargetEdge),
        In tl (allEdges (execute tr sm)) <->
        (exists (sp : list SourceNode),
            In sp (allTuples tr sm) /\
            In tl (applyPattern tr sm sp));

    (** ** matchPattern *)

    tr_matchPattern_in :
       forall (tr: Transformation) (sm : SourceModel),
         forall (sp : list SourceNode)(r : Rule),
           In r (matchPattern tr sm sp) <->
             In r (Transformation_getRules tr) /\
             matchRuleOnPattern r sm sp = true;

    (** ** matchRuleOnPattern *)

    tr_matchRuleOnPattern_leaf :
    forall (tr: Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceNode),
      matchRuleOnPattern r sm sp =
       match evalGuardExpr r sm sp with Some true => true | _ => false end;

    (** ** instantiatePattern *)

    tr_instantiatePattern_in :
      forall (tr: Transformation) (sm : SourceModel) (sp: list SourceNode) (te : TargetNode),
        In te (instantiatePattern tr sm sp) <->
        (exists (r : Rule),
            In r (matchPattern tr sm sp) /\
            In te (instantiateRuleOnPattern r sm sp));

    (** ** instantiateRuleOnPattern *)

    tr_instantiateRuleOnPattern_in :
    forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceNode) (te : TargetNode),
      In te (instantiateRuleOnPattern r sm sp) <->
      (exists (i: nat),
          In i (seq 0 (evalIteratorExpr r sm sp)) /\
          In te (instantiateIterationOnPattern r sm sp i));

   (** ** instantiateIterationOnPattern *)

    tr_instantiateIterationOnPattern_in : 
      forall (r : Rule) (sm : SourceModel) (sp: list SourceNode) (te : TargetNode) (i:nat),
        In te (instantiateIterationOnPattern r sm sp i)
        <->
        (exists (ope: OutputPatternElement),
            In ope (Rule_getOutputPatternElements r) /\ 
            instantiateElementOnPattern ope sm sp i = Some te);

    (** ** instantiateElementOnPattern *)

    tr_instantiateElementOnPattern_leaf:
        forall (o: OutputPatternElement) (sm: SourceModel) (sp: list SourceNode) (iter: nat),
          instantiateElementOnPattern o sm sp iter = evalOutputPatternElementExpr sm sp iter o;

    (** ** applyPattern *)

    tr_applyPattern_in :
      forall (tr: Transformation) (sm : SourceModel) (sp: list SourceNode) (tl : TargetEdge),
        In tl (applyPattern tr sm sp) <->
        (exists (r : Rule),
            In r (matchPattern tr sm sp) /\
            In tl (applyRuleOnPattern r tr sm sp));

    (** ** applyRuleOnPattern *)

    tr_applyRuleOnPattern_in : 
      forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceNode) (tl : TargetEdge),
        In tl (applyRuleOnPattern r tr sm sp) <->
        (exists (i: nat),
            In i (seq 0 (evalIteratorExpr r sm sp)) /\
            In tl (applyIterationOnPattern r tr sm sp i));

    (** ** applyIterationOnPattern *)

    tr_applyIterationOnPattern_in : 
      forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceNode) (tl : TargetEdge) (i:nat),
        In tl (applyIterationOnPattern r tr sm sp i) <->
        (exists (ope: OutputPatternElement),
            In ope (Rule_getOutputPatternElements r) /\ 
            In tl (applyElementOnPattern ope tr sm sp i));

    (** ** applyElementOnPattern *)

    tr_applyElementOnPattern_in : 
      forall (tr: Transformation) (sm : SourceModel) (sp: list SourceNode) (tl : TargetEdge) 
             (i:nat) (ope: OutputPatternElement),
        In tl (applyElementOnPattern ope tr sm sp i ) <->
        (exists (oper: OutputPatternLink) (te: TargetNode),
            In oper (OutputPatternElement_getOutputLinks ope) /\ 
            (evalOutputPatternElementExpr sm sp i ope) = Some te /\
            applyLinkOnPattern oper tr sm sp i te = Some tl);

    (** ** applyLinkOnPattern *)

    tr_applyLinkOnPatternTraces_leaf : 
          forall (oper: OutputPatternLink)
                 (tr: Transformation)
                 (sm: SourceModel)
                 (sp: list SourceNode) (iter: nat) (te: TargetNode) (tls: list TraceLink),
            applyLinkOnPattern oper tr sm sp iter te  = evalOutputPatternLinkExpr sm sp te iter (trace tr sm) oper;

    (** ** resolve *)

    tr_resolveAll_in:
    forall (tls: list TraceLink) (sm: SourceModel) (name: string)
           (sps: list(list SourceNode)) (iter: nat)
      (te: TargetNode),
      (exists tes: list TargetNode,
          resolveAll tls sm name sps iter = Some tes /\ In te tes) <->
      (exists (sp: list SourceNode),
          In sp sps /\
          resolve tls sm name sp iter = Some te);

    tr_resolve_leaf:
    forall (tls:list TraceLink) (sm : SourceModel) (name: string)
      (sp: list SourceNode) (iter: nat) (x: TargetNode),
      resolve tls sm name sp iter = return x ->
       (exists (tl : TraceLink),
         In tl tls /\
         Is_true (list_beq SourceNode SourceElement_eqb (TraceLink_getSourcePattern tl) sp) /\
         ((TraceLink_getIterator tl) = iter) /\ 
         ((TraceLink_getName tl) = name)%string /\
         (TraceLink_getTargetElement tl) = x);
         
  }.
