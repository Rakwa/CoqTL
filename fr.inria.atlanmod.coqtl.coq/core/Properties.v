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

Definition transf_incl {tc: TransformationConfiguration} (t1 t2: Transformation) := True.
Definition sourcemodel_incl {tc: TransformationConfiguration} (t1 t2: SourceModel) := True.
Definition targetmodel_incl {tc: TransformationConfiguration} (t1 t2: TargetModel) := True.
Definition targetmodel_equiv {tc: TransformationConfiguration} (t1 t2: TargetModel) := True.

Definition Rule_eqdec: forall {tc: TransformationConfiguration}  (x y:Rule), {x = y} + {x <> y}.
Admitted.

(* Compute elementAt 3 (indexedElements 1 (3::4::5::nil)). *)

Theorem universality_elements :
forall (tc: TransformationConfiguration) (f: SourceModel -> TargetModel),
  exists (t: Transformation), 
  forall (sm: SourceModel), allModelElements (execute t sm) = allModelElements (f sm).
Proof.
  intros.
  pose (buildTransformation 0 
    ((buildRule "rule"%string 
     (fun sm sp => match sp with nil => Some true | _ => Some false end)
      (buildOutputPatternElement "out"%string 
      (fun sm sp => Some (length (allModelElements (f sm))))
      (fun i sm sp => nth_error (allModelElements (f sm)) i)
      nil 
      :: nil))
     ::nil)).
  exists t.
  intros.
  unfold execute. 
  unfold instantiatePattern. 
  unfold instantiateRuleOnPattern. 
  unfold instantiateElementsOnPattern. 
  unfold evalElementIteratorExpr. 
  simpl.
  repeat rewrite app_nil_r.
  destruct (f sm).
  induction modelElements.
  * reflexivity.
  * simpl.
    f_equal.
    rewrite <- IHmodelElements at 2.
    repeat rewrite flat_map_concat_map.
    f_equal.
    rewrite map_map.
    reflexivity.
Qed.

Theorem universality_links :
forall (tc: TransformationConfiguration) (f: SourceModel -> TargetModel),
  exists (t: Transformation), 
  forall (sm: SourceModel), allModelElements (f sm) <> nil -> allModelLinks (execute t sm) = allModelLinks (f sm).
Proof.
  intros.
  pose (buildTransformation 0 
    ((buildRule "rule"%string 
     (fun sm sp => match sp with nil => Some true | _ => Some false end)
      (buildOutputPatternElement "out"%string 
      (fun sm sp => Some (length (allModelElements (f sm))))
      (fun i sm sp => nth_error (allModelElements (f sm)) i)
      ((buildOutputPatternLink 
        (fun tls i sm sp te => match i with | 0 => Some (length (allModelLinks (f sm))) | _ => None end)
        (fun il tls i sm sp te => nth_error (allModelLinks (f sm)) il)
      )::nil) 
      :: nil))
     ::nil)).
  exists t.
  intros.
  unfold execute. 
  unfold applyPattern. 
  unfold applyRuleOnPattern. 
  unfold applyElementsOnPattern. 
  unfold applyElementOnPattern. 
  unfold applyLinksOnPattern.
  unfold applyLinkOnPattern.
  unfold evalOutputPatternLinkExpr.
  unfold evalElementIteratorExpr.
  unfold evalLinkIteratorExpr. 
  unfold evalExpr.
  simpl.
  destruct (f sm). simpl.
  destruct modelElements.
  * simpl. contradiction.
  * simpl. 
    repeat rewrite app_nil_r.
    assert (flat_map (fun n : nat => optionToList (nth_error modelLinks n))
    (indexes (Datatypes.length modelLinks)) = modelLinks). {
      clear H.
      induction modelLinks.
      + reflexivity.
      + simpl.
        f_equal.
        rewrite <- IHmodelLinks at 2.
        repeat rewrite flat_map_concat_map.
        f_equal.
        rewrite map_map.
        reflexivity.
    }
    rewrite <- H0 at 2.
    rewrite app_nil_end.
    f_equal.
    apply in_flat_map_nil.
    intros.
    repeat rewrite app_nil_r.
    destruct a.
    + exfalso.
      Search map S.

  
  induction modelLinks.
  * 
    Search flat_map.
    apply in_flat_map_nil.
    intros.
    rewrite app_nil_r.
    simpl.
    destruct (nth_error modelElements a).
    + apply in_flat_map_nil.
      intros.
      destruct a; reflexivity.
    + reflexivity.
  * simpl.
    f_equal.
    rewrite <- IHmodelElements at 2.
    repeat rewrite flat_map_concat_map.
    f_equal.
    rewrite map_map.
    reflexivity.
Qed.

Theorem confluence :
forall (tc: TransformationConfiguration) (t1 t2: Transformation) (sm: SourceModel),
  (forall (r: Rule), count_occ Rule_eqdec (Transformation_getRules t1) r = count_occ Rule_eqdec (Transformation_getRules t2) r)
  -> targetmodel_equiv (execute t1 sm) (execute t2 sm).
Admitted.

Theorem additivity :
forall (tc: TransformationConfiguration) (t1 t2: Transformation) (sm: SourceModel),
  transf_incl t1 t2 -> targetmodel_incl (execute t1 sm) (execute t2 sm).
Admitted.

Definition monotonicity (tc: TransformationConfiguration) (t: Transformation) :=
  forall (sm1 sm2: SourceModel),
  sourcemodel_incl sm1 sm2 -> targetmodel_incl (execute t sm1) (execute t sm2).
