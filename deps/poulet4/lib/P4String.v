Require Petr4.String.

Record t (tags_t: Type) :=
  { tags: tags_t;
    str: String.t }.
Arguments tags [tags_t] _.
Arguments str [tags_t] _.

Definition strip [tags_t: Type] (s: t tags_t) :=
  {| tags := tt; str := s.(str) |}.

Definition equiv [tags_t: Type] (s1 s2: t tags_t) : Prop :=
  s1.(str) = s2.(str).

Definition equivb [tags_t: Type] (s1 s2: t tags_t) :=
  String.eqb s1.(str) s2.(str).

Definition eq_const [tags_t: Type] (s1: t tags_t) (s2: String.t) :=
  String.eqb s1.(str) s2.
