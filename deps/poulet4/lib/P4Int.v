Require Import Coq.Numbers.BinNums.
Record t (tags_t: Type) :=
  { tags: tags_t;
    val: Z;
    width_signed: option (nat * bool); }.
Arguments tags [tags_t] _.
Arguments val [tags_t] _.
Arguments width_signed [tags_t] _.
