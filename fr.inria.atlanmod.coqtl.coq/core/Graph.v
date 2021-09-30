Set Implicit Arguments.
Scheme Equality for list.


(** * Model
  Each model is constructed by a list of {@code Node} and {@Edge}. **)

Class Graph (Node: Type) (Edge: Type) :=
  {
    graphNodes : list Node;
    graphEdges : list Edge;
  }.

Definition allNodes {Node: Type} {Edge: Type} (m: Graph Node Edge) : list Node :=
  (@graphNodes _ _ m).

Definition allEdges {Node: Type} {Edge: Type} (m: Graph Node Edge) : list Edge :=
  (@graphEdges _ _ m).

(*
 allNodes and allEdges are fields of record Model.
 To use them on a Model m:
 @allNodes _ _ a.
 *)

Definition Graph_beq {ME ML: Type} (ME_beq: ME -> ME -> bool) (ML_beq: ML -> ML -> bool) (m1 m2: Graph ME ML) :=
  andb (list_beq ME_beq (@graphNodes _ _ m1) (@graphNodes _ _ m2))
  (list_beq ML_beq (@graphEdges _ _ m1) (@graphEdges _ _ m2)).