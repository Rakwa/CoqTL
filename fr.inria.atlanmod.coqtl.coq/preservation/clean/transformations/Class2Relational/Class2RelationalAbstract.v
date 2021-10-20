Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.utils.Utils.

Require Import core.Syntax.
Require Import core.TransformationConfiguration.

Require Import Class2Relational.ClassMetamodel.
Require Import Class2Relational.RelationalMetamodel.

(* module Class2Relational; 
   create OUT : RelationalMetamodel from IN : ClassMetamodel;

   rule Class2Table {
       from 
         c : Class
       to 
         tab: Table (
           id <- c.id,
           name <- c.name,
           columns <- c.attributes->collect(a | thisModule.resolve(a, 'col'))
         )
    }
    rule Attribute2Column {
        from 
          a : Attribute (not a.derived)
        to 
          col: Column (
            id <- a.id,
            name <- a.name,
            reference <- thisModule.resolve(a.type, 'tab')
          )
    }
   } *)

Instance C2RConfiguration : TransformationConfiguration := 
   Build_TransformationConfiguration ClassM RelationalM.
 

Definition Class2Relational :=
  buildTransformation 1
    [
      buildRule "Class2Table"
        (fun m c => Some true)
        (fun m c => Some 1)
        [buildOutputPatternElement "tab"
          (fun i m sp => Some (RelationalMetamodel_BuildObject TableClass (BuildTable 1 "")))
          (fun tls i m c t => None)
        ]
    ].
