Set Implicit Arguments.
Scheme Equality for list.


(** * Model
  Each model is constructed by a list of {@code ModelElement} and {@ModelLink}. **)

Class Model (ModelElement: Type) :=
  {
    modelElements : list ModelElement;
  }.

Definition allModelElements {ModelElement: Type} (m: Model ModelElement) : list ModelElement :=
  (@modelElements _ m).

(*
 allModelElements and allModelLinks are fields of record Model.
 To use them on a Model m:
 @allModelElements _ _ a.
 *)

Definition Model_beq {ME: Type} (ME_beq: ME -> ME -> bool) (m1 m2: Model ME) :=
  (list_beq ME_beq (@modelElements _ m1) (@modelElements _ m2)).