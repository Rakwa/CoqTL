Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingSchema.

Class ModelingTransformationConfiguration `(tc: TransformationConfiguration):= {

  smm: ModelingSchema SourceSchema;
  tmm: ModelingSchema TargetSchema;

  SourceGraphClass:= @ModelClass _ smm;
  SourceGraphReference:= @ModelReference _ smm;
  TargetGraphClass:= @ModelClass _ tmm;
  TargetGraphReference:= @ModelReference _ tmm;  

  denoteSourceGraphClass:= @denoteModelClass _ smm;
}.