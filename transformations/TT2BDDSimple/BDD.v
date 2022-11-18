Require Import String.

Inductive BDDTree :=
| bddleaf: 
(* name *) string -> 
(* value *) nat -> 
BDDTree
| bddnode: 
(* name *) string ->
(* falseNode *) BDDTree ->
(* trueNode *) BDDTree-> 
BDDTree
| bddnil: 
BDDTree
.

