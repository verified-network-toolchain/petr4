Require Import Coq.PArith.BinPos Coq.ZArith.BinInt
  Poulet4.Monads.Option.
Require Export Poulet4.P4cub.Syntax.P4Field.
From RecordUpdate Require Import RecordSet.
Import String.

(** * P4cub AST *)

Module InOut.
  Section InOut.
    Variables A B : Set.
    
    (** Function parameters/arguments. *)
    Record t : Set :=
      mk_t
        { inn : list A;
          out : list B }.

    Global Instance eta_inout : Settable _ :=
      settable! mk_t < inn ; out >.
  End InOut.

  Arguments mk_t {A} {B}.
  Arguments inn {A} {B}.
  Arguments out {A} {B}.

  Section InOut.
    Context {A : Set}.

    Definition concat (io : t A A) : list A :=
      inn io ++ out io.

    Context {B : Set}.

    Definition length (io : t A B) : nat :=
      List.length (A:=A) $ inn $ io + List.length (A:=B) $ out $ io.

    Definition append (io1 io2 : t A B) : t A B :=
      mk_t (InOut.inn io1 ++ InOut.inn io2) (InOut.out io1 ++ InOut.out io2).
    
    (** Monadic sequence specifically for option.
        I tried to generalize it but ran into
        universe errors all  over the codebase... *)
    Definition opt_seq (io : t (option A) (option B)) : option (t A B) :=
      let* inns := sequence $ inn io in
      let^ outs := sequence $ out io in
      mk_t inns outs.
    
    Context {D C : Set}.
    
    Definition map (f : A -> C) (g : B -> D) (io : t A B) : t C D :=
      mk_t (List.map f io.(inn)) (List.map g io.(out)).
    
    Lemma map_inn : forall (f : A -> C) (g : B -> D) (io : t A B),
        inn (map f g io) = List.map f (inn io).
    Proof using. intros f g [ioi ioo]; reflexivity. Qed.

    Lemma map_out  : forall (f : A -> C) (g : B -> D) (io : t A B),
        out (map f g io) = List.map g (out io).
    Proof using. intros f g [ioi ioo]; reflexivity. Qed.
    
    Record Forall (R : A -> Prop) (Q : B -> Prop) (io : t A B) : Prop :=
      mk_Forall
        { inn_forall : List.Forall R io.(inn);
          out_forall : List.Forall Q io.(out) }.

    Record Forall2 (R : A -> C -> Prop) (Q : B -> D -> Prop) (io1 : t A B) (io2 : t C D) : Prop :=
      mk_Forall2
        { inn_forall2 : List.Forall2 R io1.(inn) io2.(inn);
          out_forall2 : List.Forall2 Q io1.(out) io2.(out) }.
  End InOut.

  Lemma length_map : forall {A B C D : Set} (f : A -> C) (g : B -> D) io,
      InOut.length (InOut.map f g io) = InOut.length io.
  Proof.
    intros. unfold length, map. unravel.
    do 2 rewrite map_length. reflexivity.
  Qed.
  
  Section Uniform.
    Context {A B : Set}.

    Definition map_uni (f : A -> B) : t A A -> t B B := map f f.

    Definition Forall_uni (R : A -> Prop) : t A A -> Prop := Forall R R.
  End Uniform.
End InOut.
  
Module Arr.
  Section Arr.
    Variables A B C : Set.
    Record t : Set :=
      mk_t
        { inout :> InOut.t A B;
          ret : option C }.

    Global Instance eta_arr : Settable _ :=
      settable! mk_t < inout ; ret >.
  End Arr.

  Arguments mk_t {A} {B} {C}.
  Arguments inout {A} {B} {C}.
  Arguments ret {A} {B} {C}.

  Section Arr.
    Context {A B C D E F : Set}.

    Definition map (f : A -> D) (g : B -> E) (h : C -> F) (arr : t A B C) : t D E F :=
      mk_t (InOut.map f g arr.(inout)) (option_map h arr.(ret)).

    Record Forall (R : A -> Prop) (Q : B -> Prop) (P : C -> Prop) (arr : t A B C) : Prop :=
      mk_Forall
        { inout_forall : InOut.Forall R Q arr.(inout);
          ret_forall   : predop P arr.(ret) }.

    Record Forall2 (R : A -> D -> Prop) (Q : B -> E -> Prop) (P : C -> F -> Prop)
      (arr1 : t A B C) (arr2 : t D E F) : Prop :=
      mk_Forall2
        { inout_forall2 : InOut.Forall2 R Q arr1.(inout) arr2.(inout);
          ret_forall2   : relop P arr1.(ret) arr2.(ret) }.
  End Arr.

  Section Uniform.
    Context {A B C D : Set}.

    Definition map_uni (f : A -> C) (g : B -> D) : t A A B -> t C C D :=
      map f f g.

    Definition Forall_uni (R : A -> Prop) (Q : B -> Prop) : t A A B -> Prop :=
      Forall R R Q.
  End Uniform.
End Arr.

(** * Type Grammar *)
Module Typ.
  (** Expression types. *)
  Inductive t : Set :=
  | Bool                                    (** bools *)
  | VarBit (max_width: N)                   (** variable-length bitstrings *)
  | Bit    (width : N)                      (** unsigned integers *)
  | Int    (width : positive)               (** signed integers *)
  | Error                                   (** the error type *)
  | Array  (size : N) (typ : t)             (** arrays, not header-stacks, normal arrays. *)
  | Struct (isheader : bool) (fields : list t) (** struct or header types. *)
  | Var    (type_name : nat)                  (** type variables *).

  Definition params : Set := InOut.t (string * t) (string * t).
  Definition arrow  : Set := Arr.t (string * t) (string * t) t.
End Typ.

(** Unary operations. *)
Module Una.
  Variant t : Set :=
    | Not                        (** boolean negation *)
    | BitNot                     (** bitwise negation *)
    | Minus                      (** integer negation *)
    | IsValid                    (** check header validity *).
End Una.

(** Binary operations. *)
Module Bin.
  (** The "Sat" suffix denotes
      saturating arithmetic:
      where there is no overflow. *)
  Variant t : Set :=
  | Plus     (** integer addition *)
  | PlusSat  (** saturating addition *)
  | Minus    (** integer subtraction *)
  | MinusSat (** saturating subtraction *)
  | Times    (** multiplication *)
  | Shl      (** bitwise left-shift *)
  | Shr      (** bitwise right-shift *)
  | Le       (** integer less-than *)
  | Ge       (** integer greater-than *)
  | Lt       (** integer less-than or equals *)
  | Gt       (** integer greater-than or equals *)
  | Eq       (** expression equality *)
  | NotEq    (** expression inequality *)
  | BitAnd   (** bitwise and *)
  | BitXor   (** bitwise exclusive-or *)
  | BitOr    (** bitwise or *)
  | PlusPlus (** bit-string concatenation *)
  | And      (** boolean and *)
  | Or       (** boolean or *).
End Bin.

(** Expression lists. *)
Module Lst.
  (** "list" variants:
      structs, headers, and arrays. *)
  Variant t : Set :=
    | Struct
    | Array  (element_type : Typ.t)
    | Header (b : bool).
End Lst.

(** * Expression Grammar *)
Module Exp.
  (** Expessions annotated with types,
      unless the type is obvious. *)
  Inductive t : Set :=
  | Bool   (b : bool)                                          (** booleans *)
  | VarBit (max_width : N) (width : N) (val : Z)            (** variable-width integers *)
  | Bit    (width : N) (val : Z)                            (** unsigned integers *)
  | Int    (width : positive) (val : Z)                     (** signed integers *)
  | Var    (type : Typ.t) (original_name : string) (x : nat)  (** variables *)
  | Slice  (hi lo : positive) (arg : t)                     (** bit-slicing *)
  | Cast   (type : Typ.t) (arg : t)                         (** explicit casts *)
  | Uop    (result_type : Typ.t) (op : Una.t) (arg : t)     (** unary operations *)
  | Bop    (result_type : Typ.t) (op : Bin.t) (lhs rhs : t) (** binary operations *)
  | Lists  (flag : Lst.t) (es : list t)                     (** structs, headers, or arrays *)
  | Index  (elem_type : Typ.t) (array index : t)            (** array-indexing *)
  | Member (result_type : Typ.t) (mem : nat) (arg : t)        (** struct member *)
  | Error  (err : string)                                   (** error literals *).

  Definition args : Set := InOut.t t t.
End Exp.

(** Parser states. *)
Module Lbl.
  (** Labels for parser-states. *)
  Variant t : Set :=
    | Start         (** start state *)
    | Accept        (** accept state *)
    | Reject        (** reject state *)
    | Name (st : nat) (** user-defined state *).
End Lbl.

(** Pattern grammer. *)
Module Pat.
  (** Select expression pattern.
      Corresponds to keySet expressions in p4. *)
  Inductive t : Set :=
  | Wild                               (** wild-card/anything pattern *)
  | Mask  (p1 p2 : t)                  (** mask pattern *)
  | Range (p1 p2 : t)                  (** range pattern *)
  | Bit   (width : N) (val : Z)        (** unsigned-int pattern *)
  | Int   (width : positive) (val : Z) (** signed-int pattern *)
  | Lists (ps : list t)                (** lists pattern *).
End Pat.

(** Parser transition grammer. *)
Module Trns.
  (** Parser transitions, which evaluate to state names *)
  Variant t : Set :=
  | Direct (st : Lbl.t)              (** direct transition to state [st] *)
  | Select (discriminee : Exp.t)
      (default : Lbl.t)
      (cases : list (Pat.t * Lbl.t)) (** select expressions,
                                        where "default" is
                                        the catch-all case *).
End Trns.

Module Call.
  (** Procedural calls. *)
  Variant t : Set :=
    | Funct  (function_name : string) (type_args : list Typ.t)
        (returns : option Exp.t)                             (** function application. *)
    | Action (action_name : string)
        (control_plane_args : list Exp.t)                    (** action call. *)
    | Method (extern_instance_name method_name : string)     (** extern method call *)
        (type_args : list Typ.t) (returns : option Exp.t)
    | Inst (instance_name : string) (ext_args : list string) (** parser/control instance apply *).
End Call.

(** * Statement and Block Grammar *)
Module Stm.
  Inductive t : Set :=
    
  (** terminators to a statement block: *)
  | Skip                                              (** skip/no-op *)
  | Ret (e : option Exp.t)                            (** return *)
  | Exit                                              (** exit *)
  | Trans (trns : Trns.t)                             (** parser transition *)  
  | Asgn (lhs rhs : Exp.t)                            (** assignment *)
  | SetValidity (validity : bool) (hdr : Exp.t) (** set a header [hdr]'s validity to [validity] *)
  | App (call : Call.t) (args : Exp.args)             (** procedural application *)
  | Invoke (lhs : option Exp.t) (table_name : string) (** table invocation *)
      
  (** blocks of statements: *)
  | LetIn (original_name : string) (init : Typ.t  + Exp.t)
      (tail : t)                       (** variable declaration/initialization, a let-in operator *)
  | Seq (head tail : t)                (** sequenced blocks, variables introduced in [head] not in [tail] *)
  | Cond (guard : Exp.t) (tru fls : t) (** conditionals *).
End Stm.

(** * Control Grammar *)
Module Ctrl.
  (** Declarations occuring within controls. *)
  Variant t : Set :=
    | Var (original_name : string) (expr : Typ.t + Exp.t) (** variable declaration *)
    | Action (action_name : string)
        (control_plane_params : list (string * Typ.t))
        (data_plane_params : Typ.params)
        (body : Stm.t)                                      (** action declaration *)
    | Table (table_name : string)
        (key : list (Exp.t * string))
        (actions :
          list
            (string (** action name *)
             * Exp.args (** data-plane arguments *)))
        (default_action : option (string * list Exp.t))     (** table declaration *).
End Ctrl.

(** Constructor variants in p4. *)
Module Cnstr.
  Variant t : Set :=
    | Control (** control *)
    | Parser  (** parser *).
End Cnstr.

Module InstTyp.
  (** Constructor Parameter types, for instantiations *)
  Variant t : Set :=    
    | Ctr (flag : Cnstr.t)
        (extern_params : list string)
        (parameters : Typ.params)   (** parser or control instance types *)
    | Package                       (** package instance types *)
    | Extern (extern_name : string) (** extern instance types *).
End InstTyp.

(** Top-Level Declarations *)
Module Top.
  Definition constructor_params : Set := list (string * InstTyp.t).
  Definition constructor_args : Set := list string.
  
  Variant t : Set :=
    | Instantiate
        (constructor_name instance_name : string)
        (type_args : list Typ.t)
        (cargs : constructor_args)
        (expr_cargs : list Exp.t) (** instantiations *)
    | Extern
        (extern_name : string)
        (type_params : nat)
        (cparams : constructor_params)
        (expr_cparams : list Typ.t)
        (methods : Field.fs
                     string (** method name *)
                     (nat             (** type parameters *)
                      * list string (** extern parameters *)
                      * Typ.arrow (** parameters *)))
    (** extern declarations *)
    | Control
        (control_name : string)
        (cparams : constructor_params) (** constructor params *)
        (expr_cparams : list Typ.t)
        (eparams : list (string * string))      (** runtime extern params *)
        (params : Typ.params)  (** apply block params *)
        (body : list Ctrl.t) (** control body *)
        (apply_blk : Stm.t)
    | Parser
        (parser_name : string)
        (cparams : constructor_params) (** constructor params *)
        (expr_cparams : list Typ.t)
        (eparams : list (string * string))      (** runtime extern params *)
        (params : Typ.params)              (** invocation params *)
        (start : Stm.t) (** start state *)
        (states : list Stm.t) (** parser states *)
    (** parser declaration *)
    | Funct
        (function_name : string)
        (type_params : nat)
        (signature : Typ.arrow)
        (body : Stm.t) (** function declaration *).

  (** A p4cub program. *)
  Definition prog : Set := list t.
End Top.
