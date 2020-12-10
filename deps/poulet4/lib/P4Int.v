Require Import Coq.Numbers.BinNums.
Record t (tags_t: Type) :=
  { tags: tags_t;
    value: Z;
    width_signed: option (nat * bool); }.
Arguments tags [tags_t] _.
Arguments value [tags_t] _.
Arguments width_signed [tags_t] _.
