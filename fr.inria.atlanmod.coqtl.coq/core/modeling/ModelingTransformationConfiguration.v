Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingSchema.

Class ModelingTransformationConfiguration `(tc: TransformationConfiguration):= {

  smm: ModelingSchema SourceSchema;
  tmm: ModelingSchema TargetSchema;

  SourceModelClass:= @ModelClass _ smm;
  SourceModelReference:= @ModelReference _ smm;
  TargetModelClass:= @ModelClass _ tmm;
  TargetModelReference:= @ModelReference _ tmm;  

  denoteSourceModelClass:= @denoteModelClass _ smm;
}.