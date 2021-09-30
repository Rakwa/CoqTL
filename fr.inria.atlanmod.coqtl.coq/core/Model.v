Set Implicit Arguments.
Scheme Equality for list.


(** * Model
  Each model is constructed by a list of {@code Node} and {@Edge}. **)

Class Model (Node: Type) (Edge: Type) :=
  {
    modelNodes : list Node;
    modelLinks : list Edge;
  }.

Definition allNodes {Node: Type} {Edge: Type} (m: Model Node Edge) : list Node :=
  (@modelNodes _ _ m).

Definition allEdges {Node: Type} {Edge: Type} (m: Model Node Edge) : list Edge :=
  (@modelLinks _ _ m).

(*
 allNodes and allEdges are fields of record Model.
 To use them on a Model m:
 @allNodes _ _ a.
 *)

Definition Model_beq {ME ML: Type} (ME_beq: ME -> ME -> bool) (ML_beq: ML -> ML -> bool) (m1 m2: Model ME ML) :=
  andb (list_beq ME_beq (@modelNodes _ _ m1) (@modelNodes _ _ m2))
  (list_beq ML_beq (@modelLinks _ _ m1) (@modelLinks _ _ m2)).