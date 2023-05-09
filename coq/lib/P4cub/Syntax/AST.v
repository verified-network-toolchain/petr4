Require Import Coq.PArith.BinPos Coq.ZArith.BinInt.
Require Export Poulet4.P4cub.Syntax.P4Field.
Import String.

(** * P4cub AST *)

(** De Bruijn syntax. *)

(** Function call parameters/arguments. *)
Variant paramarg (A B : Set) : Set :=
  | PAIn    (a : A) (** in-parameter. *)
  | PAOut   (b : B) (** out-parameter. *)
  | PAInOut (b : B) (** inout-parameter. *).

Arguments PAIn {_} {_}.
Arguments PAOut {_} {_}.
Arguments PAInOut {_} {_}.

Definition paramarg_map {A B C D : Set}
           (f : A -> C) (g : B -> D)
           (pa : paramarg A B) : paramarg C D :=
  match pa with
  | PAIn    a => PAIn      (f a)
  | PAOut   b => PAOut     (g b)
  | PAInOut b => PAInOut   (g b)
  end.

Definition paramarg_map_same
           {A B : Set} (f : A -> B)
  : paramarg A A -> paramarg B B :=
  paramarg_map f f.

(** A predicate on a [paramarg]. *)
Variant pred_paramarg {A B : Set}
  (P : A -> Prop) (Q : B -> Prop) : paramarg A B -> Prop :=
  | pred_PAIn a : P a -> pred_paramarg P Q (PAIn a)
  | pred_PAOut b : Q b -> pred_paramarg P Q (PAOut b)
  | pred_PAInOut b : Q b -> pred_paramarg P Q (PAInOut b).

Definition pred_paramarg_same {A : Set} (P : A -> Prop)
  : paramarg A A -> Prop := pred_paramarg P P.

Definition paramarg_strength {A B : Set} (arg : paramarg (option A) (option B)) : option (paramarg A B) :=
  match arg with
  | PAIn a => a >>| PAIn
  | PAOut b => b >>| PAOut
  | PAInOut b => b >>| PAInOut
  end.

(** Relating [paramarg]s. *)
Variant rel_paramarg {A1 A2 B1 B2 : Set}
  (R : A1 -> A2 -> Prop) (Q : B1 -> B2 -> Prop)
  : paramarg A1 B1 -> paramarg A2 B2 -> Prop :=
  | rel_paramarg_PAIn a1 a2 :
    R a1 a2 -> rel_paramarg R Q (PAIn a1) (PAIn a2)
  | rel_paramarg_PAOut b1 b2 :
    Q b1 b2 -> rel_paramarg R Q (PAOut b1) (PAOut b2)
  | rel_paramarg_PAInOut b1 b2 :
    Q b1 b2 -> rel_paramarg R Q (PAInOut b1) (PAInOut b2).

Definition rel_paramarg_same {A B : Set} (R : A -> B -> Prop) :
  paramarg A A -> paramarg B B -> Prop :=
  rel_paramarg R R.

Definition paramarg_elim {A : Set} (p : paramarg A A) : A :=
    match p with
    | PAIn a | PAOut a | PAInOut a => a
    end.

(** Function signatures/instantiations. *)
Record arrow (A B C : Set) : Set :=
  { paramargs : list (A * paramarg B C);
    rtrns : option C }.

Arguments paramargs {_} {_} {_}.
Arguments rtrns {_} {_} {_}.

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

  (** Function parameters. *)
  Definition param : Set := paramarg Typ.t Typ.t.
  Definition params : Set :=
    list ((* original name *) string * param).

  (** Function types. *)
  Definition arrowT : Set := arrow (* original name *) string Typ.t Typ.t.
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

  (** Function call arguments. *)
  Definition arg : Set := paramarg Exp.t Exp.t.
  Definition args : Set := list arg.
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
        (returns : option Exp.t)                              (** function application. *)
    | Action (action_name : string)
        (control_plane_args : list Exp.t)                     (** action call. *)
    | Method (extern_instance_name method_name : string)       (** extern method call *)
        (type_args : list Typ.t) (returns : option Exp.t)
    | Inst   (instance_name : string) (ext_args : list string) (** parser/control instance apply *).
End Call.

(** * Statement and Block Grammar *)
Module Stm.
  Inductive t : Set :=
    
  (** terminators to a statement block: *)
  | Skip                                               (** skip/no-op *)
  | Ret (e : option Exp.t)                            (** return *)
  | Exit                                               (** exit *)
  | Trans (trns : Trns.t)                              (** parser transition *)  
  | Asgn (lhs rhs : Exp.t)                            (** assignment *)
  | SetValidity (validity : bool) (hdr : Exp.t) (** set a header [hdr]'s validity to [validity] *)
  | App (call : Call.t) (args : Exp.args)             (** procedural application *)
  | Invoke (lhs : option Exp.t) (table_name : string) (** table invocation *)
      
  (** blocks of statements: *)
  | LetIn (original_name : string) (init : Typ.t  + Exp.t)
      (tail : t)                        (** variable declaration/initialization, a let-in operator *)
  | Seq (head tail : t)                 (** sequenced blocks, variables introduced in [head] not in [tail] *)
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
                      * Typ.arrowT (** parameters *)))
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
        (signature : Typ.arrowT)
        (body : Stm.t) (** function declaration *).

  (** A p4cub program. *)
  Definition prog : Set := list t.
End Top.
