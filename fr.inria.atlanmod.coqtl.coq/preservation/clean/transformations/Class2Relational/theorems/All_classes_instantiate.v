Require Import String.
Require Import Coq.Logic.Eqdep_dec.
Require Import Arith.
Require Import Coq.Arith.Gt.
Require Import Coq.Arith.EqNat.
Require Import List.
Require Import Omega.

Require Import core.utils.Utils.
Require Import core.SyntaxCertification.
Require Import core.Metamodel.
Require Import core.Model.
Require Import core.Syntax.
Require Import core.Engine.

Require Import transformations.Class2Relational.Class2RelationalAbstract.
Require Import transformations.Class2Relational.ClassMetamodel.
Require Import transformations.Class2Relational.RelationalMetamodel.

Theorem Relational_name_definedness:
forall (eng: TransformationEngine CoqTLSyntax) (cm : ClassModel) (c: Class) o,
  In o (@instantiatePattern _ _ eng Class2Relational cm [ClassMetamodel_toObject ClassClass c]) ->
     exists r, In r (@matchPattern _ _ eng Class2Relational cm [ClassMetamodel_toObject ClassClass c]).
Proof.
intros.
apply tr_instantiatePattern_in in H.
destruct H.
destruct H.
exists x.
exact H.
Qed.