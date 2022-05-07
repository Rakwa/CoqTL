Require Import core.Semantics.
Require Import core.Syntax.
Require Import core.Model.
Require Import core.TransformationConfiguration.
Require Import String.
Require Import EqNat.
Require Import List.
Require Import Expressions.
Require Import core.utils.Utils.
Require Import PeanoNat.
Require Import Lia.
Require Import FunctionalExtensionality.


(*************************************************************)
(** * Injectivity on model elements                          *)
(*************************************************************)

Theorem Injectivity :
forall {tc: TransformationConfiguration}  (tr: Transformation) (sm : SourceModel) (sp1 sp2 : list SourceModelElement),
  instantiatePattern tr sm sp1 = instantiatePattern tr sm sp2 -> sp1 = sp2.
Abort. 
