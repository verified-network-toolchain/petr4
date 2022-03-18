Require Import Coq.PArith.BinPosDef Coq.PArith.BinPos
        Coq.ZArith.BinIntDef Coq.ZArith.BinInt
        Coq.Classes.EquivDec Coq.Program.Program.
Require Export Poulet4.P4cub.Syntax.P4Field.
Require Coq.Logic.Eqdep_dec.
Import String.

(** * P4cub AST *)

(** De Bruijn syntax. *)

(** Function call parameters/arguments. *)
Variant paramarg (A B : Set) : Set :=
| PAIn      (a : A) (** in-parameter. *)
| PAOut     (b : B) (** out-parameter. *)
| PAInOut   (b : B) (** inout-parameter. *)
| PADirLess (a : A) (** direction-less parameter *).

Arguments PAIn {_} {_}.
Arguments PAOut {_} {_}.
Arguments PAInOut {_} {_}.
Arguments PADirLess {_} {_}.

Definition paramarg_map {A B C D : Set}
           (f : A -> C) (g : B -> D)
           (pa : paramarg A B) : paramarg C D :=
  match pa with
  | PAIn      a => PAIn      (f a)
  | PAOut     b => PAOut     (g b)
  | PAInOut   b => PAInOut   (g b)
  | PADirLess a => PADirLess (f a)
  end.

(** A predicate on a [paramarg]. *)
Definition pred_paramarg {A B : Set}
           (PA : A -> Prop) (PB : B -> Prop) (pa : paramarg A B) : Prop :=
  match pa with
  | PAIn  a | PADirLess a => PA a
  | PAOut b | PAInOut   b => PB b
  end.

Definition pred_paramarg_same {A : Set} (P : A -> Prop)
  : paramarg A A -> Prop := pred_paramarg P P.

(** Relating [paramarg]s. *)
Definition rel_paramarg {A1 A2 B1 B2 : Set}
           (RA : A1 -> A2 -> Prop) (RB : B1 -> B2 -> Prop)
           (pa1 : paramarg A1 B1)
           (pa2 : paramarg A2 B2) : Prop :=
  match pa1, pa2 with
  | PADirLess a1, PADirLess a2 
  | PAIn      a1, PAIn      a2 => RA a1 a2
  | PAOut     b1, PAOut     b2
  | PAInOut   b1, PAInOut   b2 => RB b1 b2
  | _           , _            => False
  end.

Definition rel_paramarg_same {A B : Set} (R : A -> B -> Prop) :
  paramarg A A -> paramarg B B -> Prop :=
  rel_paramarg R R.

(** Function signatures/instantiations. *)
Record arrow (A B : Set) : Set :=
  { paramargs : list (paramarg A B);
    rtrns : option B }.

Arguments paramargs {_} {_}.
Arguments rtrns {_} {_}.

(** * Expression Grammar *)
Module Expr.
  (** Expression types. *)
  Inductive t : Set :=
  | TBool                     (** bool *)
  | TBit (width : N)          (** unsigned integers *)
  | TInt (width : positive)   (** signed integers *)
  | TError                    (** the error type *)
  | TStruct (fields : list t)
            (isheader : bool)    (** struct types *)
  | TVar (type_name : nat)      (** type variables *).  
    
  (** Function parameters. *)
  Definition params : Set := list (paramarg t t).
    
  (** Function types. *)
  Definition arrowT : Set := arrow t t.
    
  (** Constructor types. *)
  Inductive ct : Set :=
  | CTType (type : t)              (** expression types *)
  | CTControl (cparams : list ct)
              (runtime_extern_params : list string)
              (parameters : params)(** control types *)
  | CTParser (cparams : list ct)
             (runtime_extern_params : list string)
             (parameters : params) (** parser types *)
  | CTPackage (cparams : list ct)  (** package types *)
  | CTExtern (extern_name : string).  
    
  Definition constructor_params : Set := list ct.
  
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

  (** Expressions annotated with types,
      unless the type is obvious. *)
  
  Inductive e : Set :=
  | Bool (b : bool)                      (** booleans *)
  | Bit (width : N) (val : Z)         (** unsigned integers *)
  | Int (width : positive) (val : Z)  (** signed integers *)
  | Var (type : t) (x : nat)            (** variables *)
  | Slice (arg : e)
           (hi lo : positive)          (** bit-slicing *)
  | Cast (type : t) (arg : e)         (** explicit casts *)
  | Uop (result_type : t) (op : uop)
         (arg : e)                     (** unary operations *)
  | Bop (result_type : t) (op : bop)
         (lhs rhs : e)                 (** binary operations *)
  | Struct (fields : list e) (valid : option e) (** struct literals *)
  | Member (result_type : t) (mem : nat)
            (arg : e)              (** member-expressions *)
  | Error (err : option string)       (** error literals *).    
  
  (** Function call arguments. *)
  Definition args : Set := list (paramarg e e).
    
  (** Function call. *)
  Definition arrowE : Set := arrow e e.
    
  (** Constructor arguments. *)
  Variant constructor_arg : Set :=
    | CAExpr (expr : e)   (** plain expression *)
    | CAName (x : nat)      (** name of parser, control, package, or extern *).
    
  Definition constructor_args : Set := list constructor_arg.
End Expr.

(** Statement Grammar *)
Module Stmt.
  Inductive s : Set :=
  | Skip (** skip/no-op *)
  | Var (expr : Expr.t + Expr.e) (** variable declaration. *)
  | Assign (lhs rhs : Expr.e) (** assignment *)
  | Conditional
      (guard : Expr.e)
      (tru_blk fls_blk : s) (** conditionals *)
  | Seq (s1 s2 : s) (** sequences *)
  | Block (blk : s) (** blocks *)
  | ExternMethodCall
      (extern_name method_name : string)
      (typ_args : list Expr.t)
      (args : Expr.arrowE ) (** extern method calls *)
  | FunCall
      (f : string)
      (typ_args : list Expr.t)
      (args : Expr.arrowE)  (** function call *)
  | ActCall
      (action_name : string)
      (args : Expr.args) (** action call *)
  | Return (e : option Expr.e) (** return statement *)
  | Exit (** exit statement *)
  | Invoke (table_name : string) (** table invocation *)
  | Apply (instance_name : string)
           (ext_args : list string)
           (args : Expr.args) (** apply statements *).
End Stmt.

(** Parsers *)
Module Parser.
  (** Labels for parser-states. *)
  Variant state : Set :=
    | Start         (** start state *)
    | Accept        (** accept state *)
    | Reject        (** reject state *)
    | Name (st : nat) (** user-defined state *).

  (** Select expression pattern.
      Corresponds to keySet expressions in p4. *)
  Inductive pat : Set :=
  | Wild                             (** wild-card/anything pattern *)
  | Mask (p1 p2 : pat)               (** mask pattern *)
  | Range (p1 p2 : pat)              (** range pattern *)
  | Bit (width : N) (val : Z)        (** unsigned-int pattern *)
  | Int (width : positive) (val : Z) (** signed-int pattern *)
  | Struct (ps : list pat)           (** struct pattern *).

  (** Parser expressions, which evaluate to state names *)
  Inductive e : Set :=
  | Goto (st : state)  (** goto state [st] *)
  | Select (discriminee : Expr.e)
            (default : e) (cases : Field.fs pat e)
                       (** select expressions,
                                       where "default" is
                                       the catch-all case *).
  
  (** Parser State Blocks. *)
  Record state_block : Set :=
    { stmt : Stmt.s ; trans : e }.
End Parser.

(** Controls *)
Module Control.
  (** Table. *)
  Record table : Set :=
    { table_key : list (Expr.e * string); 
      table_actions : list string }.
    
  (** Declarations that may occur within Controls. *)
  Inductive d : Set :=
  | Action (action_name : string)
             (signature : Expr.params) (body : Stmt.s )
  (** action declaration *)
  | Table (table_name : string)
            (body : table)  (** table declaration *)
  | Seq (d1 d2 : d)       (** sequence of declarations *).
End Control.

(** Top-Level Declarations *)
Module TopDecl.
  (** Top-level declarations. *)
  Inductive d : Set :=
  | Instantiate
      (constructor_name instance_name : string)
      (type_args : list Expr.t)
      (cargs : Expr.constructor_args )
  (** instantiations *)
  | Extern
      (extern_name : string)
      (type_params : nat)
      (cparams : Expr.constructor_params)
      (methods : Field.fs
                   string (** method name *)
                   (nat             (** type parameters *)
                    * list string (** extern parameters *)
                    * Expr.arrowT (** parameters *)))
  (** extern declarations *)
  | Control
      (control_name : string)
      (cparams : Expr.constructor_params) (** constructor params *)
      (eparams : list string)      (** runtime extern params *)
      (params : Expr.params)       (** apply block params *)
      (body : Control.d ) (apply_blk : Stmt.s )
  (** control declarations *)
  | Parser
      (parser_name : string)
      (cparams : Expr.constructor_params) (** constructor params *)
      (eparams : list string)      (** runtime extern params *)
      (params : Expr.params)              (** invocation params *)
      (start : Parser.state_block ) (** start state *)
      (states : list (Parser.state_block )) (** parser states *)
  (** parser declaration *)
  | Funct
        (function_name : string)
        (type_params : nat)
        (signature : Expr.arrowT) (body : Stmt.s )
  (** function/method declaration *)
  | Seq (d1 d2 : d) .
End TopDecl.
