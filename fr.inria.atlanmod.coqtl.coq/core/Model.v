Set Implicit Arguments.
Scheme Equality for list.


(** * Model
  Each model is constructed by a list of {@code Node} and {@Edge}. **)

Class Model (Node: Type) (Edge: Type) :=
  {
    modelElements : list Node;
    modelLinks : list Edge;
  }.

Definition allNodes {Node: Type} {Edge: Type} (m: Model Node Edge) : list Node :=
  (@modelElements _ _ m).

Definition allEdges {Node: Type} {Edge: Type} (m: Model Node Edge) : list Edge :=
  (@modelLinks _ _ m).

(*
 allNodes and allEdges are fields of record Model.
 To use them on a Model m:
 @allNodes _ _ a.
 *)

Definition Model_beq {ME ML: Type} (ME_beq: ME -> ME -> bool) (ML_beq: ML -> ML -> bool) (m1 m2: Model ME ML) :=
  andb (list_beq ME_beq (@modelElements _ _ m1) (@modelElements _ _ m2))
  (list_beq ML_beq (@modelLinks _ _ m1) (@modelLinks _ _ m2)).