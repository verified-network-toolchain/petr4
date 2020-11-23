Require Import Strings.String.
Require Import OrderedType.

(* This is extracted to the OCaml caml_string type *)
Axiom caml_string: Type.
Axiom caml_string_lt: caml_string -> caml_string -> Prop.
Inductive cmp :=  LT | EQ | GT.
Axiom caml_string_cmp: caml_string -> caml_string -> cmp.
Axiom caml_string_eqb: caml_string -> caml_string -> bool.
Axiom caml_string_eqb_correct:
  forall s1 s2,
    caml_string_eqb s1 s2 = true <-> s1 = s2.
Axiom caml_string_cmp_correct_lt:
  forall s1 s2,
    caml_string_cmp s1 s2 = LT ->
    caml_string_lt s1 s2.
Axiom caml_string_cmp_correct_eq:
  forall s1 s2,
    caml_string_cmp s1 s2 = EQ ->
    s2 = s1.
Axiom caml_string_cmp_correct_gt:
  forall s1 s2,
    caml_string_cmp s1 s2 = GT ->
    caml_string_lt s2 s1.
Axiom caml_string_of_chars: string -> caml_string.

Module CamlStringOT <: OrderedType.OrderedType.
  Definition t := caml_string.
  Definition eq := @eq t.
  Definition lt := caml_string_lt.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  Axiom lt_trans :
    forall x y z : t, lt x y -> lt y z -> lt x z.
  Axiom lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Definition compare :
    forall x y : t, OrderedType.Compare lt eq x y.
  Proof.
    intros.
    remember (caml_string_cmp x y) as c.
    symmetry in Heqc.
    unfold lt, eq in *.
    destruct c;
      eauto using OrderedType.LT,
                  caml_string_cmp_correct_lt,
                  OrderedType.EQ,
                  caml_string_cmp_correct_eq,
                  OrderedType.GT,
                  caml_string_cmp_correct_gt,
                  eq_sym.
  Defined.
  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof.
    intros.
    remember (caml_string_eqb x y) as e.
    symmetry in Heqe.
    unfold eq.
    destruct e.
    - left.
      eapply caml_string_eqb_correct.
      assumption.
    - right.
      intro Heq.
      eapply caml_string_eqb_correct in Heq.
      congruence.
  Defined.
End CamlStringOT.

Module StrConstants.
  Definition isValid := caml_string_of_chars "isValid".
  Definition setValid := caml_string_of_chars "setValid".
  Definition setInvalid := caml_string_of_chars "setInvalid".
  Definition pop_front := caml_string_of_chars "pop_front".
  Definition push_front := caml_string_of_chars "push_front".
  Definition extract := caml_string_of_chars "extract".
  Definition accept := caml_string_of_chars "accept".
  Definition reject := caml_string_of_chars "reject".
End StrConstants.
