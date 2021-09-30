(** * Schema **)
Require Import core.Graph.
Require Import core.Schema.
Require Import core.EqDec.

Class Sum (SumType: Type) (SubTypeName: Type):=
  {
    denoteSubType: SubTypeName -> Set;
    toSubType: forall (t: SubTypeName), SumType -> option (denoteSubType t);
    toSumType: forall (t: SubTypeName), (denoteSubType t) -> SumType;

  }.

Class ModelingSchema `(mm : Schema) :=
{
    ModelClass: Type;
    ModelReference: Type;
    elements: Sum Node ModelClass;
    links: Sum Edge ModelReference;
    
    (* Denotation *)
    denoteModelClass: ModelClass -> Set := denoteSubType;
    denoteModelReference: ModelReference -> Set := denoteSubType;
  
    (* Downcasting *)
    toModelClass: forall (t:ModelClass), Node -> option (denoteModelClass t) := toSubType;
    toModelReference: forall (t:ModelReference), Edge -> option (denoteModelReference t) := toSubType;
  
    (* Upcasting *)
    toNode: forall (t: ModelClass), (denoteModelClass t) -> Node := toSumType;
    toEdge: forall (t: ModelReference), (denoteModelReference t) -> Edge := toSumType;

}.

Definition hasType {mm: Schema} {mmm: ModelingSchema mm} (t: ModelClass) (e: Node) : bool :=
  match (toModelClass t e) with
  | Some e' => true
  | _ => false
  end.
