Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.Metamodel.
Require Import core.Model.
Require Import core.Engine.
Require Import core.utils.TopUtils.
Require Import core.utils.CpdtTactics.

Section CoqTL.

  Variables (SourceModelElement SourceModelLink SourceModelClass SourceModelReference: Type)
            (smm: Metamodel SourceModelElement SourceModelLink SourceModelClass SourceModelReference)
            (TargetModelElement TargetModelLink TargetModelClass TargetModelReference: Type)
            (tmm: Metamodel TargetModelElement TargetModelLink TargetModelClass TargetModelReference).
  
  Definition SourceModel := Model SourceModelElement SourceModelLink.
  Definition TargetModel := Model TargetModelElement TargetModelLink.

  Fixpoint outputReferenceTypes
            (sclasses : list SourceModelClass) (tclass: TargetModelClass)  (tref: TargetModelReference):=
    match sclasses with
    | nil => (denoteModelClass tclass) -> (option (denoteModelReference tref))
    | cons class classes' => (denoteModelClass class) -> outputReferenceTypes classes' tclass tref
    end.
  
  Inductive OutputPatternElementReference : Type :=
    BuildOutputPatternElementReference :
      forall (InElTypes: list SourceModelClass),
      forall (t:TargetModelClass),
      forall (OutRef: TargetModelReference),
        (SourceModel -> (outputReferenceTypes InElTypes t OutRef)) ->
        OutputPatternElementReference.
  
  Fixpoint outputPatternElementTypes
            (sclasses : list SourceModelClass) (tclass: TargetModelClass) :=
    match sclasses with
    | nil => (denoteModelClass tclass)
    | cons class classes' =>
      (denoteModelClass class) ->
      outputPatternElementTypes classes' tclass
    end.

  Inductive OutputPatternElement : Type := 
    BuildOutputPatternElement :
      string ->
      forall (InElTypes: list SourceModelClass),
       forall (t:TargetModelClass),
       (SourceModel -> (outputPatternElementTypes InElTypes t)) ->
       list OutputPatternElementReference -> OutputPatternElement.

  Fixpoint guardTypes (classes : list SourceModelClass) :=
    match classes with
    | nil => bool
    | cons class classes' => (denoteModelClass class) -> guardTypes classes'
    end.
  
  Inductive Rule : Type := 
    BuildRule :
       forall (InElTypes: list SourceModelClass), (SourceModel -> (guardTypes InElTypes)) ->
      list OutputPatternElement -> Rule.
  
  Inductive Transformation : Type := 
    BuildTransformation :
      list Rule ->
      Transformation.

End CoqTL.


Arguments BuildTransformation [SourceModelElement] [SourceModelLink] [SourceModelClass]
     [SourceModelReference] _ [TargetModelElement] [TargetModelLink] [TargetModelClass]
 [TargetModelReference] _.
Arguments BuildRule [SourceModelElement] [SourceModelLink] [SourceModelClass]
     [SourceModelReference] _ [TargetModelElement] [TargetModelLink] [TargetModelClass]
 [TargetModelReference] _.
Arguments BuildOutputPatternElement [SourceModelElement] [SourceModelLink] [SourceModelClass]
     [SourceModelReference] _ [TargetModelElement] [TargetModelLink] [TargetModelClass]
 [TargetModelReference] _.
Arguments BuildOutputPatternElementReference [SourceModelElement] [SourceModelLink] [SourceModelClass]
     [SourceModelReference] _ [TargetModelElement] [TargetModelLink] [TargetModelClass]
 [TargetModelReference] _.