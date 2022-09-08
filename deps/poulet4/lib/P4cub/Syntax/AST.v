Require Import Coq.PArith.BinPos Coq.ZArith.BinInt.
Require Export Poulet4.P4cub.Syntax.P4Field.
Import String.

(** * P4cub AST *)

(** De Bruijn syntax. *)

(** Function call parameters/arguments. *)
Variant paramarg (A B : Set) : Set :=
  | PAIn      (a : A) (** in-parameter. *)
  | PAOut     (b : B) (** out-parameter. *)
  | PAInOut   (b : B) (** inout-parameter. *).

Arguments PAIn {_} {_}.
Arguments PAOut {_} {_}.
Arguments PAInOut {_} {_}.

Definition paramarg_map {A B C D : Set}
           (f : A -> C) (g : B -> D)
           (pa : paramarg A B) : paramarg C D :=
  match pa with
  | PAIn      a => PAIn      (f a)
  | PAOut     b => PAOut     (g b)
  | PAInOut   b => PAInOut   (g b)
  end.

Definition paramarg_map_same
           {A B : Set} (f : A -> B)
  : paramarg A A -> paramarg B B :=
  paramarg_map f f.

(** A predicate on a [paramarg]. *)
Definition pred_paramarg {A B : Set}
           (PA : A -> Prop) (PB : B -> Prop) (pa : paramarg A B) : Prop :=
  match pa with
  | PAIn  a             => PA a
  | PAOut b | PAInOut b => PB b
  end.

Definition pred_paramarg_same {A : Set} (P : A -> Prop)
  : paramarg A A -> Prop := pred_paramarg P P.

(** Relating [paramarg]s. *)
Definition rel_paramarg {A1 A2 B1 B2 : Set}
           (RA : A1 -> A2 -> Prop) (RB : B1 -> B2 -> Prop)
           (pa1 : paramarg A1 B1)
           (pa2 : paramarg A2 B2) : Prop :=
  match pa1, pa2 with
  | PAIn      a1, PAIn      a2 => RA a1 a2
  | PAOut     b1, PAOut     b2
  | PAInOut   b1, PAInOut   b2 => RB b1 b2
  | _           , _            => False
  end.

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

(** * Expression Grammar *)
Module Expr.
  (** Expression types. *)
  Inductive t : Set :=
  | TBool                       (** bools *)
  | TBit (width : N)            (** unsigned integers *)
  | TInt (width : positive)     (** signed integers *)
  | TError                      (** the error type *)
  | TArray (size : N) (typ : t) (** arrays, not header-stacks, normal arrays. *)
  | TStruct (isheader : bool) (fields : list t) (** struct or header types. *)
  | TVar (type_name : nat)        (** type variables *).
    
  (** Function parameters. *)
  Definition params : Set :=
    list ((* original name *) string * paramarg t t).
    
  (** Function types. *)
  Definition arrowT : Set := arrow (* original name *) string t t.
  
  Variant uop : Set :=
    | Not        (** boolean negation *)
    | BitNot     (** bitwise negation *)
    | UMinus     (** integer negation *)
    | IsValid    (** check header validity *)
    | SetValidity (validity : bool) (** set a header's validity to [validity] *).
  
  (** Binary operations.
      The "Sat" suffix denotes
      saturating arithmetic:
      where there is no overflow. *)
  Variant bop : Set :=
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

  (** "list" variants:
      structs, headers, and arrays. *)
  Variant lists : Set :=
  | lists_struct
  | lists_array (element_type : t)
  | lists_header (b : bool).
  
  (** Expressions annotated with types,
      unless the type is obvious. *)  
  Inductive e : Set :=
  | Bool (b : bool)                     (** booleans *)
  | Bit (width : N) (val : Z)        (** unsigned integers *)
  | Int (width : positive) (val : Z) (** signed integers *)
  | Var (type : t) (original_name : string) (x : nat)  (** variables *)
  | Slice (hi lo : positive) (arg : e) (** bit-slicing *)
  | Cast (type : t) (arg : e)          (** explicit casts *)
  | Uop (result_type : t) (op : uop)
        (arg : e)                     (** unary operations *)
  | Bop (result_type : t) (op : bop)
        (lhs rhs : e)                 (** binary operations *)
  | Lists (flag : lists) (es : list e)
  | Index (elem_type : t) (array index : e)      (** array-indexing *)
  | Member (result_type : t) (mem : nat) (arg : e) (** struct member *)
  | Error (err : string)  (** error literals *).
  
  (** Function call arguments. *)
  Definition args : Set := list (paramarg e e).
End Expr.

(** * Parser Grammar *)
Module Parser.
  (** Labels for parser-states. *)
  Variant state_label : Set :=
    | Start         (** start state *)
    | Accept        (** accept state *)
    | Reject        (** reject state *)
    | Name (st : nat) (** user-defined state *).

  (** Select expression pattern.
      Corresponds to keySet expressions in p4. *)
  Inductive pat : Set :=
  | Wild                      (** wild-card/anything pattern *)
  | Mask  (p1 p2 : pat)       (** mask pattern *)
  | Range (p1 p2 : pat)       (** range pattern *)
  | Bit (width : N) (val : Z) (** unsigned-int pattern *)
  | Int (width : positive) (val : Z) (** signed-int pattern *)
  | Lists (ps : list pat)     (** lists pattern *).

  (** Parser transitions, which evaluate to state names *)
  Variant trns : Set :=
  | Direct (st : state_label) (** direct transition to state [st] *)
  | Select (discriminee : Expr.e)
      (default : state_label)
      (cases : Field.fs pat state_label)
  (** select expressions,
      where "default" is
      the catch-all case *).

  Definition pt := trns.
End Parser.

(** * Statement and Block Grammar *)
Module Stmt.
  (** Function, action, extern method, or apply instance. *)
  Variant fun_kind : Set :=
    | Funct (function_name : string)
        (type_args : list Expr.t) (returns : option Expr.e)
    | Action (action_name : string)
        (control_plane_args : list Expr.e)
    | Method (extern_instance_name method_name : string)
        (type_args : list Expr.t) (returns : option Expr.e).
  
  (** Statements. *)
  Inductive s : Set :=
  (** terminators to a statement block: *)
  | Skip                          (** skip/no-op *)
  | Return (e : option Expr.e)    (** return *)
  | Exit                          (** exit *)
  | Transition (trns : Parser.pt) (** parser transition *)  
  | Assign (lhs rhs : Expr.e)     (** assignment *)
  | Call (call : fun_kind) (** kind of call *)
      (args : Expr.args)   (** arguments *)
  | Invoke (table_name : string) (** table invocation *)
  | Apply (instance_name : string)
      (ext_args : list string)
      (args : Expr.args) (** apply statements *)
  (** blocks of statements: *)
  | Var (original_name : string)
      (expr : Expr.t (** unitialized decl *) + Expr.e (** initialzed decl *))
      (tail : s) (** variable declaration/initialization
                     a let-in operator. *)
  | Seq (head tail : s) (** sequenced blocks,
                            variables introduced in [head]
                            do not occur in [tail] *)
  | Conditional (guard : Expr.e)
      (tru_blk fls_blk : s) (** conditionals *).
End Stmt.

(** * Control Grammar *)
Module Control.
  (** Declarations occuring within controls. *)
  Variant d : Set :=
  | Var (original_name : string)
      (expr : Expr.t (** unitialized decl *) + Expr.e (** initialzed decl *))
  | Action (action_name : string)
      (control_plane_params
        : list ((* original parameter name *) string * Expr.t))
      (data_plane_params : Expr.params)
      (body : Stmt.s) (** action declaration *)
  | Table (table_name : string)
      (key : list (Expr.e * string))
      (actions :
        list
          (string (** action name *)
           * Expr.args (** data-plane arguments *))).
End Control.

(** Top-Level Declarations *)
Module TopDecl.
  (** Constructor Parameter types, for instantiations *)
  Variant it : Set :=    
    | ControlInstType
        (extern_params : list string)
        (parameters : Expr.params) (** control instance types *)
    | ParserInstType
        (extern_params : list string)
        (parameters : Expr.params) (** parser instance types *)
    | PackageInstType (** package instance types *)
    | ExternInstType (extern_name : string) (** extern instance types *).
  
  Definition constructor_params : Set := list (string * it).
    
  Definition constructor_args : Set := list string.
  
  (** Top-level declarations. *)
  Variant d : Set :=
    | Instantiate
        (constructor_name instance_name : string)
        (type_args : list Expr.t)
        (cargs : constructor_args)
        (expr_cargs : list Expr.e) (** instantiations *)
    | Extern
        (extern_name : string)
        (type_params : nat)
        (cparams : constructor_params)
        (expr_cparams : list Expr.t)
        (methods : Field.fs
                     string (** method name *)
                     (nat             (** type parameters *)
                      * list string (** extern parameters *)
                      * Expr.arrowT (** parameters *)))
    (** extern declarations *)
    | Control
        (control_name : string)
        (cparams : constructor_params) (** constructor params *)
        (expr_cparams : list Expr.t)
        (eparams : list (string * string))      (** runtime extern params *)
        (params : Expr.params)  (** apply block params *)
        (body : list Control.d) (** control body *)
        (apply_blk : Stmt.s)
    | Parser
        (parser_name : string)
        (cparams : constructor_params) (** constructor params *)
        (expr_cparams : list Expr.t)
        (eparams : list (string * string))      (** runtime extern params *)
        (params : Expr.params)              (** invocation params *)
        (start : Stmt.s) (** start state *)
        (states : list Stmt.s) (** parser states *)
    (** parser declaration *)
    | Funct
        (function_name : string)
        (type_params : nat)
        (signature : Expr.arrowT)
        (body : Stmt.s) (** function declaration *).

  (** A p4cub program. *)
  Definition prog : Set := list d.
End TopDecl.
