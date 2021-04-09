Require Export Poulet4.P4cub.Check.
Require Export Poulet4.P4cub.P4Arith.

Require Import Poulet4.P4cub.Value.

Require Import Coq.Bool.Bool.
Require Import Coq.NArith.BinNatDef.
Require Import Coq.ZArith.BinIntDef.
Require Import Coq.NArith.BinNat.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Arith.Compare_dec.

Module V := Val.

(** Notation entries. *)
Declare Custom Entry p4evalsignal.

Reserved Notation "⟨ ϵ , e ⟩ ⇓ v"
         (at level 40, e custom p4expr, v custom p4value).

Reserved Notation "⧠ e ⇓ lv"
         (at level 40, e custom p4expr, lv custom p4lvalue).

Reserved Notation "⟪ cp , tenv , aenv , fenv , ienv , ϵ1 , s ⟫ ⤋ ⟪ ϵ2 , sig ⟫"
         (at level 40, s custom p4stmt,
          ϵ2 custom p4env, sig custom p4evalsignal).

Reserved Notation "⧼ cp , cs , fnv , ins1 , ϵ1 , d ⧽ ⟱  ⧼ ϵ2 , ins2 ⧽"
         (at level 40, d custom p4decl, ϵ2 custom p4env).

Reserved Notation "⦉ cp , cs , ts1 , aa1 , fns , ins1 , ϵ1 , d ⦊ ⟱  ⦉ ϵ2 , ins2 , aa2 , ts2 ⦊"
         (at level 40, d custom p4ctrldecl,
          ϵ2 custom p4env, ts2 custom p4env).

Reserved Notation "⦇ cp , cs1 , fns1 , ins1 , ϵ1 , d ⦈ ⟱  ⦇ ϵ2 , ins2 , fns2 , cs2 ⦈"
         (at level 40, d custom p4topdecl, ϵ2 custom p4env).

Module Step.
  Module P := P4cub.
  Module E := P.Expr.
  Module ST := P.Stmt.
  Module D := P.Decl.
  Module CD := P.Control.ControlDecl.
  Module TP := P.TopDecl.
  Module F := P.F.

  Import P.P4cubNotations.
  Import V.ValueNotations.
  Import V.LValueNotations.

  (** Statement signals. *)
  Inductive signal : Type :=
  | SIG_Cont                  (* continue *)
  | SIG_Exit                  (* exit *)
  | SIG_Rtrn (v : option V.v) (* return *).

  (*
  Arguments SIG_Cont {_}.
  Arguments SIG_Exit {_}.
  Arguments SIG_Rtrn {_}. *)

  Notation "x"
    := x (in custom p4evalsignal at level 0, x constr at level 0).
  Notation "'C'" := SIG_Cont (in custom p4evalsignal at level 0).
  Notation "'X'" := SIG_Exit (in custom p4evalsignal at level 0).
  Notation "'R' 'of' v ?"
    := (SIG_Rtrn v) (in custom p4evalsignal at level 0).
  Notation "'Void'" := (SIG_Rtrn None) (in custom p4evalsignal at level 0).
  Notation "'Fruit' v" := (SIG_Rtrn (Some v)) (in custom p4evalsignal at level 0).

  Import Env.EnvNotations.

  Section StepDefs.
    (* Context {tags_t : Type}. *)

    (** Unsigned integer binary operations. *)
    Definition eval_bit_binop
               (op : E.bop) (w : positive)
               (n1 n2 : N) : option V.v :=
      match op with
      | E.Plus     => Some (V.VBit w (BitArith.plus_mod w n1 n2))
      | E.PlusSat  => Some (V.VBit w (BitArith.plus_sat w n1 n2))
      | E.Minus    => Some (V.VBit w (BitArith.minus_mod w n1 n2))
      | E.MinusSat => Some (V.VBit w (N.sub n1 n2))
      | E.Shl      => Some (V.VBit w (BitArith.shift_left w n1 n2))
      | E.Shr      => Some (V.VBit w (BitArith.shift_right w n1 n2))
      | E.Le       => Some (V.VBool (N.leb n1 n2))
      | E.Ge       => Some (V.VBool (N.leb n2 n1))
      | E.Lt       => Some (V.VBool (N.ltb n1 n2))
      | E.Gt       => Some (V.VBool (N.ltb n2 n1))
      | E.Eq       => Some (V.VBool (N.eqb n1 n2))
      | E.NotEq    => Some (V.VBool (negb (N.eqb n1 n2)))
      | E.BitAnd   => Some (V.VBit w (BitArith.bit_and w n1 n2))
      | E.BitXor   => Some (V.VBit w (BitArith.bit_xor w n1 n2))
      | E.BitOr    => Some (V.VBit w (BitArith.bit_or  w n1 n2))
      | E.PlusPlus
      | E.And
      | E.Or       => None
      end.
    (**[]*)

    (** Signed integer binary operations. *)
    Definition eval_int_binop
               (op : E.bop) (w : positive)
               (z1 z2 : Z) : option V.v :=
      match op with
      | E.Plus     => Some (V.VInt w (IntArith.plus_mod w z1 z2))
      | E.PlusSat  => Some (V.VInt w (IntArith.plus_sat w z1 z2))
      | E.Minus    => Some (V.VInt w (IntArith.minus_mod w z1 z2))
      | E.MinusSat => Some (V.VInt w (IntArith.minus_sat w z1 z2))
      | E.Shl      => Some (V.VInt w (IntArith.shift_left w z1 z2))
      | E.Shr      => Some (V.VInt w (IntArith.shift_right w z1 z2))
      | E.Le       => Some (V.VBool (Z.leb z1 z2))
      | E.Ge       => Some (V.VBool (Z.leb z2 z1))
      | E.Lt       => Some (V.VBool (Z.ltb z1 z2))
      | E.Gt       => Some (V.VBool (Z.ltb z2 z1))
      | E.Eq       => Some (V.VBool (Z.eqb z1 z2))
      | E.NotEq    => Some (V.VBool (negb (Z.eqb z1 z2)))
      | E.BitAnd   => Some (V.VInt w (IntArith.bit_and w z1 z2))
      | E.BitXor   => Some (V.VInt w (IntArith.bit_xor w z1 z2))
      | E.BitOr    => Some (V.VInt w (IntArith.bit_or  w z1 z2))
      | E.PlusPlus
      | E.And
      | E.Or       => None
      end.
    (**[]*)

    (** Boolean binary operations. *)
    Definition eval_bool_binop (op : E.bop) (b1 b2 : bool) : option bool :=
      match op with
      | E.Eq    => Some (eqb b1 b2)
      | E.NotEq => Some (negb (eqb b1 b2))
      | E.And   => Some (b1 && b2)
      | E.Or    => Some (b1 || b2)
      | _       => None
      end.

    (** Header operations. *)
    Definition eval_hdr_op
               (op : E.hdr_op) (vs : F.fs string V.v)
               (b : bool) : V.v :=
      match op with
      | E.HOIsValid => ~{ VBOOL b }~
      | E.HOSetValid => ~{ HDR { vs } VALID:=true }~
      | E.HOSetInValid => ~{ HDR { vs } VALID:=false }~
      end.
    (**[]*)

    (** Header stack operations. *)
    Definition eval_stk_op
               (op : E.hdr_stk_op) (size : positive)
               (nextIndex : N) (ts : F.fs string E.t)
               (bvss : list (bool * F.fs string V.v))
      : option V.v :=
      let w := 32%positive in
      let sizenat := Pos.to_nat size in
      match op with
      | E.HSOSize => let s := (Npos size)%N in Some ~{ w VW s }~
      | E.HSONext => match nth_error bvss (N.to_nat nextIndex) with
                    | None => None
                    | Some (b,vs) => Some ~{ HDR { vs } VALID:=b }~
                    end
      | E.HSOPush n
        => let nnat := N.to_nat n in
          if lt_dec nnat sizenat then
            let new_hdrs := repeat (false, F.map V.vdefault ts) nnat in
            let remains := firstn (sizenat - nnat) bvss in
            let new_nextIndex := N.min (nextIndex + n) (N.pos size - 1)%N in
            Some (V.VHeaderStack ts (new_hdrs ++ remains) size new_nextIndex)
          else
            let new_hdrs := repeat (false, F.map V.vdefault ts) sizenat in
            Some (V.VHeaderStack ts new_hdrs size ((N.pos size) - 1)%N)
      | E.HSOPop  n
        => let nnat := N.to_nat n in
          if lt_dec nnat sizenat then
            let new_hdrs := repeat (false, F.map V.vdefault ts) nnat in
            let remains := skipn nnat bvss in
            Some (V.VHeaderStack ts (remains ++ new_hdrs) size (nextIndex - n))
          else
            let new_hdrs := repeat (false, F.map V.vdefault ts) sizenat in
            Some (V.VHeaderStack ts new_hdrs size 0%N)
      end.
    (**[]*)

    Definition eval_cast
               (target : E.t) (v : V.v) : option V.v :=
      match target, v with
      | {{ bit<xH> }}, ~{ TRUE }~         => Some (V.VBit 1%positive 1%N)
      | {{ bit<xH> }}, ~{ FALSE }~        => Some (V.VBit 1%positive 0%N)
      | {{ Bool }}, V.VBit 1%positive 1%N => Some ~{ TRUE }~
      | {{ Bool }}, V.VBit 1%positive 0%N => Some ~{ FALSE }~
      | {{ bit<w> }}, ~{ _ VS Z0 }~       => Some ~{ w VW N0 }~
      | {{ bit<w> }}, V.VInt _ (Zneg p)
      | {{ bit<w> }}, V.VInt _ (Zpos p)   => let n := BitArith.return_bound w (Npos p) in
                                            Some ~{ w VW n }~
      (* TODO: casting bit -> int is incorrect. *)
      | {{ int<w> }}, ~{ _ VW n }~ => let z := IntArith.return_bound w (Z.of_N n) in
                                     Some ~{ w VS z }~
      | {{ bit<w> }}, ~{ _ VW n }~ => let n := BitArith.return_bound w n in
                                     Some ~{ w VW n }~
      | {{ int<w> }}, ~{ _ VS z }~ => let z := IntArith.return_bound w z in
                                     Some ~{ w VS z }~
      | _, _ => None
      end.
    (**[]*)

    (** Variable to Value mappings. *)
    Definition epsilon : Type := Env.t string V.v.

    (** Lookup an lvalue. *)
    Fixpoint lv_lookup (ϵ : epsilon) (lv : V.lv) : option V.v :=
      match lv with
      | l{ VAR x }l => ϵ x
      | l{ lv DOT x }l =>
        (* TODO: use monadic bind. *)
        match lv_lookup ϵ lv with
        | None => None
        | Some ~{ REC { fs } }~
        | Some ~{ HDR { fs } VALID:=_ }~ => F.get x fs
        | Some _ => None
        end
      | l{ lv[n] }l =>
        match lv_lookup ϵ lv with
        | None => None
        | Some ~{ STACK vss:_[_] NEXT:=_ }~ =>
          match nth_error vss (N.to_nat n) with
          | None => None
          | Some (b,vs) => Some ~{ HDR { vs } VALID:=b }~
          end
        | Some _ => None
        end
      end.
    (**[]*)

    (** Updating an lvalue in an environment. *)
    Fixpoint lv_update (lv : V.lv) (v : V.v) (ϵ : epsilon) : epsilon :=
      match lv with
      | l{ VAR x }l    => !{ x ↦ v ;; ϵ }!
      | l{ lv DOT x }l =>
        match lv_lookup ϵ lv with
        | Some ~{ REC { vs } }~ => lv_update lv (V.VRecord (F.update x v vs)) ϵ
        | Some ~{ HDR { vs } VALID:=b }~ =>
          lv_update lv (V.VHeader (F.update x v vs) b) ϵ
        | Some _ | None => ϵ
        end
      | l{ lv[n] }l =>
        match v, lv_lookup ϵ lv with
        | ~{ HDR { vs } VALID:=b }~ ,
          Some ~{ STACK vss:ts[size] NEXT:=ni }~ =>
          let vss := nth_update (N.to_nat n) (b,vs) vss in
          lv_update lv ~{ STACK vss:ts[size] NEXT:=ni }~ ϵ
        | _, Some _ | _, None => ϵ
        end
      end.
    (**[]*)

    (** Create a new environment
        from a closure environment where
        values of [In] args are substituted
        into the function parameters. *)
    Definition copy_in
               (argsv : V.argsv)
               (ϵcall : epsilon) : epsilon -> epsilon :=
      F.fold (fun x arg ϵ =>
                match arg with
                | P.PAIn v     => !{ x ↦ v ;; ϵ }!
                | P.PAInOut lv => match lv_lookup ϵcall lv with
                                 | None   => ϵ
                                 | Some v => !{ x ↦ v ;; ϵ }!
                                end
                | P.PAOut _    => ϵ
                end) argsv.
    (**[]*)

    (** Update call-site environment with
        out variables from function call evaluation. *)
    Definition copy_out
               (argsv : V.argsv)
               (ϵf : epsilon) : epsilon -> epsilon :=
      F.fold (fun x arg ϵ =>
                match arg with
                | P.PAIn _ => ϵ
                | P.PAOut lv
                | P.PAInOut lv =>
                  match ϵf x with
                  | None   => ϵ
                  | Some v => lv_update lv v ϵ
                  end
                end) argsv.
    (**[]*)

    (** Evidence that control-flow
        is interrupted by an exit or return statement. *)
    Inductive interrupt : signal -> Prop :=
    | interrupt_exit : interrupt SIG_Exit
    | interrupt_rtrn (vo : option V.v) : interrupt (SIG_Rtrn vo).
    (**[]*)

    (* P4cub will use locators instead of qualified names.
    Definition bare (x : string) : name tags_t :=
      Typed.BareName x.
    (**[]*) *)

    Context {tags_t : Type}.

    (** Table environment. *)
    Definition tenv : Type := Env.t string (CD.table tags_t).

    (** Function declarations and closures. *)
    Inductive fdecl : Type :=
    | FDecl (closure : epsilon) (fs : fenv) (ins : ienv) (body : ST.s tags_t)
    with fenv : Type :=
    | FEnv (fs : Env.t string fdecl)
    (** Action declarations and closures *)
    with adecl : Type :=
    | ADecl (closure : epsilon) (fs : fenv) (ins : ienv) (aa : aenv) (body : ST.s tags_t)
    with aenv : Type :=
    | AEnv (aa : Env.t string adecl)
    (** Instances and Environment. *)
    with inst : Type :=
    | CInst (closure : epsilon) (fs : fenv) (ins : ienv)
            (tbls : tenv) (aa : aenv)
            (apply_blk : ST.s tags_t)  (* control instance *)
    | PInst (* TODO: parser instance *)
    | EInst (* TODO: extern object instance *)
    with ienv : Type :=
    | IEnv (ins : Env.t string inst).
    (**[]*)

    (** Function lookup. *)
    Definition lookup '(FEnv fs : fenv) : string -> option fdecl := fs.

    (** Bind a function declaration to an environment. *)
    Definition update '(FEnv fs : fenv) (x : string) (d : fdecl) : fenv :=
      FEnv !{ x ↦ d ;; fs }!.
    (**[]*)

    (** Instance lookup. *)
    Definition ilookup '(IEnv fs : ienv) : string -> option inst := fs.

    (** Bind an instance to an environment. *)
    Definition iupdate '(IEnv fs : ienv) (x : string) (d : inst) : ienv :=
      IEnv !{ x ↦ d ;; fs }!.
    (**[]*)

    (** Action lookup. *)
    Definition alookup '(AEnv aa : aenv) : string -> option adecl := aa.

    (** Bind a function declaration to an environment. *)
    Definition aupdate '(AEnv aa : aenv) (x : string) (d : adecl) : aenv :=
      AEnv !{ x ↦ d ;; aa }!.
    (**[]*)

    (** Control plane table entries,
        essentially mapping tables to an action call. *)
    Definition entries : Type :=
      list (V.v * E.matchkind) ->
      list string ->
      string * E.args tags_t.
    (**[]*)

    (** Control plane tables. *)
    Definition ctrl : Type := Env.t string entries.

    (** Control declarations and closures. *)
    Inductive cdecl : Type :=
    | CDecl (cs : cenv) (closure : epsilon) (fs : fenv) (ins : ienv)
            (body : CD.d tags_t) (apply_block : ST.s tags_t)
    with cenv : Type :=
    | CEnv (cs : Env.t string cdecl).
    (**[]*)

    (** Control lookup. *)
    Definition clookup '(CEnv cs : cenv) : string -> option cdecl := cs.

    (** Bind an instance to an environment. *)
    Definition cupdate '(CEnv cs : cenv) (x : string) (d : cdecl) : cenv :=
      CEnv !{ x ↦ d ;; cs }!.
    (**[]*)
  End StepDefs.

  (** Expression big-step semantics. *)
  Inductive expr_big_step {tags_t : Type} (ϵ : epsilon) : E.e tags_t -> V.v -> Prop :=
  (* Literals. *)
  | ebs_bool (b : bool) (i : tags_t) :
      ⟨ ϵ, BOOL b @ i ⟩ ⇓ VBOOL b
  | ebs_bit (w : positive) (n : N) (i : tags_t) :
      ⟨ ϵ, w W n @ i ⟩ ⇓ w VW n
  | ebs_int (w : positive) (z : Z) (i : tags_t) :
      ⟨ ϵ, w S z @ i ⟩ ⇓ w VS z
  | ebs_var (x : string) (τ : E.t) (i : tags_t) (v : V.v) :
      ϵ x = Some v ->
      ⟨ ϵ, Var x:τ @ i ⟩ ⇓ v
  | ebs_cast (τ : E.t) (e : E.e tags_t) (i : tags_t) (v v' : V.v) :
      eval_cast τ v = Some v' ->
      ⟨ ϵ, e ⟩ ⇓ v ->
      ⟨ ϵ, Cast e:τ @ i ⟩ ⇓ v'
  | ebs_error (err : option string) (i : tags_t) :
      ⟨ ϵ, Error err @ i ⟩ ⇓ ERROR err
  | ebs_matchkind (mk : E.matchkind) (i : tags_t) :
      ⟨ ϵ, Matchkind mk @ i ⟩ ⇓ MATCHKIND mk
  (* Unary Operations. *)
  | ebs_not (e : E.e tags_t) (i : tags_t) (b b' : bool) :
      negb b = b' ->
      ⟨ ϵ, e ⟩ ⇓ VBOOL b ->
      ⟨ ϵ, UOP ! e:Bool @ i ⟩ ⇓ VBOOL b'
  | ebs_bitnot (e : E.e tags_t) (i : tags_t)
               (w : positive) (n n' : N) :
      BitArith.neg w n = n' ->
      ⟨ ϵ, e ⟩ ⇓ w VW n ->
      ⟨ ϵ, UOP ~ e:bit<w> @ i ⟩ ⇓ w VW n'
  | ebs_uminus (e : E.e tags_t) (i : tags_t)
               (w : positive) (z z' : Z) :
      IntArith.neg w z = z' ->
      ⟨ ϵ, e ⟩ ⇓ w VS z ->
      ⟨ ϵ, UOP - e:int<w> @ i ⟩ ⇓ w VS z'
  (* Binary Operations. *)
  | ebs_bop_bit (e1 e2 : E.e tags_t) (op : E.bop) (v : V.v)
                (i : tags_t) (w : positive) (n1 n2 : N) :
      eval_bit_binop op w n1 n2 = Some v ->
      ⟨ ϵ, e1 ⟩ ⇓ w VW n1 ->
      ⟨ ϵ, e2 ⟩ ⇓ w VW n2 ->
      ⟨ ϵ, BOP e1:bit<w> op e2:bit<w> @ i ⟩ ⇓ v
  | ebs_plusplus (e1 e2 : E.e tags_t) (i : tags_t)
                 (w w1 w2 : positive) (n n1 n2 : N) :
      (w1 + w2)%positive = w ->
      BitArith.bit_concat w1 w2 n1 n2 = n ->
      ⟨ ϵ, e1 ⟩ ⇓ w1 VW n1 ->
      ⟨ ϵ, e2 ⟩ ⇓ w2 VW n2 ->
      ⟨ ϵ, BOP e1:bit<w1> ++ e2:bit<w2> @ i ⟩ ⇓ w VW n
  | ebs_bop_int (e1 e2 : E.e tags_t) (op : E.bop) (v : V.v)
                (i : tags_t) (w : positive) (z1 z2 : Z) :
      eval_int_binop op w z1 z2 = Some v ->
      ⟨ ϵ, e1 ⟩ ⇓ w VS z1 ->
      ⟨ ϵ, e2 ⟩ ⇓ w VS z2 ->
      ⟨ ϵ, BOP e1:int<w> op e2:int <w> @ i ⟩ ⇓ v
  | ebs_bop_bool (e1 e2 : E.e tags_t) (op : E.bop)
                 (i : tags_t) (b b1 b2 : bool) :
      eval_bool_binop op b1 b2 = Some b ->
      ⟨ ϵ, e1 ⟩ ⇓ VBOOL b1 ->
      ⟨ ϵ, e2 ⟩ ⇓ VBOOL b2 ->
      ⟨ ϵ, BOP e1:Bool op e2:Bool @ i⟩ ⇓ VBOOL b
  | ebs_eq (e1 e2 : E.e tags_t) (τ1 τ2 : E.t)
                (i : tags_t) (v1 v2 : V.v) (b : bool) :
      V.eqbv v1 v2 = b ->
      ⟨ ϵ, e1 ⟩ ⇓ v1 ->
      ⟨ ϵ, e2 ⟩ ⇓ v2 ->
      ⟨ ϵ, BOP e1:τ1 == e2:τ2 @ i ⟩ ⇓ VBOOL b
  | ebs_neq (e1 e2 : E.e tags_t) (τ1 τ2 : E.t)
            (i : tags_t) (v1 v2 : V.v) (b : bool) :
      negb (V.eqbv v1 v2) = b ->
      ⟨ ϵ, e1 ⟩ ⇓ v1 ->
      ⟨ ϵ, e2 ⟩ ⇓ v2 ->
      ⟨ ϵ, BOP e1:τ1 != e2:τ2 @ i ⟩ ⇓ VBOOL b
  (* Structs *)
  | ebs_rec_mem (e : E.e tags_t) (x : string) (i : tags_t)
                (tfs : F.fs string E.t)
                (vfs : F.fs string V.v) (v : V.v) :
      F.get x vfs = Some v ->
      ⟨ ϵ, e ⟩ ⇓ REC { vfs } ->
      ⟨ ϵ, Mem e:rec { tfs } dot x @ i ⟩ ⇓ v
  | ebs_hdr_mem (e : E.e tags_t) (x : string) (i : tags_t)
                (tfs : F.fs string E.t) (b : bool)
                (vfs : F.fs string V.v) (v : V.v) :
      F.get x vfs = Some v ->
      ⟨ ϵ, e ⟩ ⇓ HDR { vfs } VALID:=b ->
      ⟨ ϵ, Mem e:hdr { tfs } dot x @ i ⟩ ⇓ v
  | ebs_tuple (es : list (E.e tags_t)) (i : tags_t)
              (vs : list (V.v)) :
      Forall2 (fun e v => ⟨ ϵ, e ⟩ ⇓ v) es vs ->
      ⟨ ϵ, tup es @ i ⟩ ⇓ TUPLE vs
  | ebs_rec_lit (efs : F.fs string (E.t * E.e tags_t))
                (i : tags_t) (vfs : F.fs string V.v) :
      F.relfs
        (fun te v =>
           let e := snd te in ⟨ ϵ, e ⟩ ⇓ v) efs vfs ->
      ⟨ ϵ, rec { efs } @ i ⟩ ⇓ REC { vfs }
  | ebs_hdr_lit (efs : F.fs string (E.t * E.e tags_t))
                (e : E.e tags_t) (i : tags_t) (b : bool)
                (vfs : F.fs string V.v) :
      F.relfs
        (fun te v =>
           let e := snd te in ⟨ ϵ, e ⟩ ⇓ v) efs vfs ->
      ⟨ ϵ, e ⟩ ⇓ VBOOL b ->
      ⟨ ϵ, hdr { efs } valid:=e @ i ⟩ ⇓ HDR { vfs } VALID:=b
  | ebs_hdr_op  (op : E.hdr_op) (e : E.e tags_t) (i : tags_t)
                (v : V.v) (vs : F.fs string (V.v)) (b : bool) :
      eval_hdr_op op vs b = v ->
      ⟨ ϵ, e ⟩ ⇓ HDR { vs } VALID:=b ->
      ⟨ ϵ, HDR_OP op e @ i ⟩ ⇓ v
  | ebs_hdr_stack (ts : F.fs string (E.t))
                  (hs : list (E.e tags_t))
                  (n : positive) (ni : N)
                  (vss : list (bool * F.fs string (V.v))) :
      Forall2
        (fun e bvs =>
           let b := fst bvs in
           let vs := snd bvs in
           ⟨ ϵ, e ⟩ ⇓ HDR { vs } VALID:=b)
        hs vss ->
      ⟨ ϵ, Stack hs:ts[n] nextIndex:=ni ⟩ ⇓ STACK vss:ts [n] NEXT:=ni
  | ebs_access (e : E.e tags_t) (i : tags_t)
               (n : positive) (index ni : N)
               (ts : F.fs string (E.t))
               (vss : list (bool * F.fs string (V.v)))
               (b : bool) (vs : F.fs string (V.v)) :
      nth_error vss (N.to_nat index) = Some (b,vs) ->
      ⟨ ϵ, e ⟩ ⇓ STACK vss:ts [n] NEXT:=ni ->
      ⟨ ϵ, Access e[index] @ i ⟩ ⇓ HDR { vs } VALID:=b
  | ebs_stk_op  (op : E.hdr_stk_op) (e : E.e tags_t) (i : tags_t)
                (v : V.v) (ts : F.fs string (E.t))
                (bvss : list (bool * F.fs string (V.v)))
                (size : positive) (nextIndex : N) :
      eval_stk_op op size nextIndex ts bvss = Some v ->
      ⟨ ϵ, e ⟩ ⇓ STACK bvss:ts[size] NEXT:=nextIndex ->
      ⟨ ϵ, STK_OP op e @ i ⟩ ⇓ v
  where "⟨ ϵ , e ⟩ ⇓ v" := (expr_big_step ϵ e v).
  (**[]*)

  (** A custom induction principle for
      the expression big-step relation. *)
  Section ExprEvalInduction.
    Variable (tags_t: Type).

    Variable P : epsilon -> E.e tags_t -> V.v -> Prop.

    Hypothesis HBool : forall ϵ b i, P ϵ <{ BOOL b @ i }> ~{ VBOOL b }~.

    Hypothesis HBit : forall ϵ w n i, P ϵ <{ w W n @ i }> ~{ w VW n }~.

    Hypothesis HInt : forall ϵ w z i, P ϵ <{ w S z @ i }> ~{ w VS z }~.

    Hypothesis HVar : forall ϵ x τ i v,
        ϵ x = Some v ->
        P ϵ <{ Var x:τ @ i }> v.
    (**[]*)

    Hypothesis HCast : forall ϵ τ e i v v',
        eval_cast τ v = Some v' ->
        ⟨ ϵ, e ⟩ ⇓ v ->
        P ϵ e v ->
        P ϵ <{ Cast e:τ @ i }> v'.
    (**[]*)

    Hypothesis HError : forall ϵ err i, P ϵ <{ Error err @ i }> ~{ ERROR err }~.

    Hypothesis HMatchkind : forall ϵ mk i,
        P ϵ <{ Matchkind mk @ i }> ~{ MATCHKIND mk }~.
    (**[]*)

    Hypothesis HNot : forall ϵ e i b b',
        negb b = b' ->
        ⟨ ϵ, e ⟩ ⇓ VBOOL b ->
        P ϵ e ~{ VBOOL b }~ ->
        P ϵ <{ UOP ! e:Bool @ i }> ~{ VBOOL b'}~.
    (**[]*)

    Hypothesis HBitNot : forall ϵ e i w n n',
        BitArith.neg w n = n' ->
        ⟨ ϵ, e ⟩ ⇓ w VW n ->
        P ϵ e ~{ w VW n }~ ->
        P ϵ <{ UOP ~ e:bit<w> @ i }> ~{ w VW n' }~.
    (**[]*)

    Hypothesis HUMinus : forall ϵ e i w z z',
        IntArith.neg w z = z' ->
        ⟨ ϵ, e ⟩ ⇓ w VS z ->
        P ϵ e ~{ w VS z }~ ->
        P ϵ <{ UOP - e:int<w> @ i }> ~{ w VS z' }~.
    (**[]*)

    Hypothesis HBOPBit : forall ϵ e1 e2 op v i w n1 n2,
        eval_bit_binop op w n1 n2 = Some v ->
        ⟨ ϵ, e1 ⟩ ⇓ w VW n1 ->
        P ϵ e1 ~{ w VW n1 }~ ->
        ⟨ ϵ, e2 ⟩ ⇓ w VW n2 ->
        P ϵ e2 ~{ w VW n2 }~ ->
        P ϵ <{ BOP e1:bit<w> op e2:bit<w> @ i }> v.
    (**[]*)

    Hypothesis HPlusPlus : forall ϵ e1 e2 i w w1 w2 n n1 n2,
      (w1 + w2)%positive = w ->
      BitArith.bit_concat w1 w2 n1 n2 = n ->
      ⟨ ϵ, e1 ⟩ ⇓ w1 VW n1 ->
      P ϵ e1 ~{ w1 VW n1 }~ ->
      ⟨ ϵ, e2 ⟩ ⇓ w2 VW n2 ->
      P ϵ e2 ~{ w2 VW n2 }~ ->
      P ϵ <{ BOP e1:bit<w1> ++ e2:bit<w2> @ i }> ~{ w VW n }~.
    (**[]*)

    Hypothesis HBOPInt : forall ϵ e1 e2 op v i w z1 z2,
      eval_int_binop op w z1 z2 = Some v ->
      ⟨ ϵ, e1 ⟩ ⇓ w VS z1 ->
      P ϵ e1 ~{ w VS z1 }~ ->
      ⟨ ϵ, e2 ⟩ ⇓ w VS z2 ->
      P ϵ e2 ~{ w VS z2 }~ ->
      P ϵ <{ BOP e1:int<w> op e2:int<w> @ i }> v.
    (**[]*)

    Hypothesis HBOPBool : forall ϵ e1 e2 op i b b1 b2,
      eval_bool_binop op b1 b2 = Some b ->
      ⟨ ϵ, e1 ⟩ ⇓ VBOOL b1 ->
      P ϵ e1 ~{ VBOOL b1 }~ ->
      ⟨ ϵ, e2 ⟩ ⇓ VBOOL b2 ->
      P ϵ e2 ~{ VBOOL b2 }~ ->
      P ϵ <{ BOP e1:Bool op e2:Bool @ i }> ~{VBOOL b}~.
    (**[]*)

    Hypothesis HEq : forall ϵ e1 e2 τ1 τ2 i v1 v2 b,
        V.eqbv v1 v2 = b ->
        ⟨ ϵ, e1 ⟩ ⇓ v1 ->
        P ϵ e1 v1 ->
        ⟨ ϵ, e2 ⟩ ⇓ v2 ->
        P ϵ e2 v2 ->
        P ϵ <{ BOP e1:τ1 == e2:τ2 @ i }> ~{ VBOOL b }~.
    (**[]*)

    Hypothesis HNeq : forall ϵ e1 e2 τ1 τ2 i v1 v2 b,
        negb (V.eqbv v1 v2) = b ->
        ⟨ ϵ, e1 ⟩ ⇓ v1 ->
        P ϵ e1 v1 ->
        ⟨ ϵ, e2 ⟩ ⇓ v2 ->
        P ϵ e2 v2 ->
        P ϵ <{ BOP e1:τ1 != e2:τ2 @ i }> ~{ VBOOL b }~.
    (**[]*)

    Hypothesis HRecMem : forall ϵ e x i ts vs v,
        F.get x vs = Some v ->
        ⟨ ϵ, e ⟩ ⇓ REC { vs } ->
        P ϵ e ~{ REC { vs } }~ ->
        P ϵ <{ Mem e:rec { ts } dot x @ i }> v.
    (**[]*)

    Hypothesis HHdrMem : forall ϵ e x i ts b vs v,
        F.get x vs = Some v ->
        ⟨ ϵ, e ⟩ ⇓ HDR { vs } VALID:=b ->
        P ϵ e ~{ HDR { vs } VALID:=b }~ ->
        P ϵ <{ Mem e:hdr { ts } dot x @ i }> v.
    (**[]*)

    Hypothesis HTuple : forall ϵ es i vs,
        Forall2 (fun e v => ⟨ ϵ, e ⟩ ⇓ v) es vs ->
        Forall2 (P ϵ) es vs ->
        P ϵ <{ tup es @ i }> ~{ TUPLE vs }~.
    (**[]*)

    Hypothesis HRecLit : forall ϵ efs i vfs,
        F.relfs
          (fun te v =>
             let e := snd te in ⟨ ϵ, e ⟩ ⇓ v) efs vfs ->
        F.relfs (fun te v => let e := snd te in P ϵ e v) efs vfs ->
        P ϵ <{ rec { efs } @ i }> ~{ REC { vfs } }~.
    (**[]*)

    Hypothesis HHdrLit : forall ϵ efs e i b vfs,
        F.relfs
          (fun te v =>
             let e := snd te in ⟨ ϵ, e ⟩ ⇓ v) efs vfs ->
        F.relfs (fun te v => let e := snd te in P ϵ e v) efs vfs ->
        ⟨ ϵ, e ⟩ ⇓ VBOOL b ->
        P ϵ e ~{ VBOOL b }~ ->
        P ϵ <{ hdr { efs } valid:=e @ i }> ~{ HDR { vfs } VALID:=b }~.
    (**[]*)

    Hypothesis HHdrOp : forall ϵ op e i v vs b,
        eval_hdr_op op vs b = v ->
        ⟨ ϵ, e ⟩ ⇓ HDR { vs } VALID:=b ->
        P ϵ e ~{ HDR { vs } VALID:=b }~ ->
        P ϵ <{ HDR_OP op e @ i }> v.
    (**[]*)

    Hypothesis HHdrStack : forall ϵ ts hs n ni vss,
        Forall2
          (fun e bvs =>
             let b := fst bvs in
             let vs := snd bvs in
             ⟨ ϵ, e ⟩ ⇓ HDR { vs } VALID:=b)
          hs vss ->
        Forall2
          (fun e bvs =>
             let b := fst bvs in
             let vs := snd bvs in
             P ϵ e ~{ HDR { vs } VALID:=b}~ )
          hs vss ->
        P ϵ <{ Stack hs:ts[n] nextIndex:=ni }> ~{ STACK vss:ts[n] NEXT:=ni }~.
    (**[]*)

    Hypothesis HAccess : forall ϵ e i n index ni ts vss b vs,
               nth_error vss (N.to_nat index) = Some (b,vs) ->
               ⟨ ϵ, e ⟩ ⇓ STACK vss:ts[n] NEXT:=ni ->
               P ϵ e ~{ STACK vss:ts[n] NEXT:=ni }~ ->
               P ϵ <{ Access e[index] @ i }> ~{ HDR { vs } VALID:=b }~.
    (**[]*)

    Hypothesis HStackOp : forall ϵ op e i v ts bvss size nextIndex,
        eval_stk_op op size nextIndex ts bvss = Some v ->
        ⟨ ϵ, e ⟩ ⇓ STACK bvss:ts[size] NEXT:=nextIndex ->
        P ϵ e ~{ STACK bvss:ts[size] NEXT:=nextIndex }~ ->
        P ϵ <{ STK_OP op e @ i }> v.
    (**[]*)

    (** Custom induction principle for
        the expression big-step relation.
        [Do induction ?H using custom_expr_big_step_ind]. *)
    Definition custom_expr_big_step_ind :
      forall (ϵ : epsilon) (e : E.e tags_t)
        (v : V.v) (Hy : ⟨ ϵ, e ⟩ ⇓ v), P ϵ e v :=
      fix ebsind ϵ e v Hy :=
        let fix lind
                {es : list (E.e tags_t)}
                {vs : list (V.v)}
                (HR : Forall2 (fun e v => ⟨ ϵ, e ⟩ ⇓ v) es vs)
            : Forall2 (P ϵ) es vs :=
            match HR with
            | Forall2_nil _ => Forall2_nil _
            | Forall2_cons _ _ Hh Ht => Forall2_cons
                                         _ _
                                         (ebsind _ _ _ Hh)
                                         (lind Ht)
            end in
        let fix fsind
                {efs : F.fs string (E.t * E.e tags_t)}
                {vfs : F.fs string (V.v)}
                (HRs : F.relfs
                         (fun te v =>
                            let e := snd te in
                            ⟨ ϵ , e ⟩ ⇓ v) efs vfs)
                : F.relfs
                    (fun te v => let e := snd te in P ϵ e v)
                    efs vfs :=
                match HRs
                      in (Forall2 _ es vs)
                      return
                      (Forall2
                         (F.relf (fun te v => let e := snd te in P ϵ e v))
                         es vs) with
                | Forall2_nil _ => Forall2_nil _
                | Forall2_cons _ _
                               (conj Hname Hhead)
                               Htail => Forall2_cons
                                         _ _
                                         (conj Hname (ebsind _ _ _ Hhead))
                                         (fsind Htail)
                end in
        let fix ffind
                {es : list (E.e tags_t)}
                {vss : list (bool * F.fs string (V.v))}
                (HRs : Forall2
                         (fun e bvs =>
                            let b := fst bvs in
                            let vs := snd bvs in
                            ⟨ ϵ, e ⟩ ⇓ HDR { vs } VALID:=b)
                         es vss)
            : Forall2
                (fun e bvs =>
                   let b := fst bvs in
                   let vs := snd bvs in
                   P ϵ e ~{ HDR { vs } VALID:=b}~ )
                es vss :=
            match HRs with
            | Forall2_nil _ => Forall2_nil _
            | Forall2_cons _ _ Hhead Htail => Forall2_cons
                                               _ _
                                               (ebsind _ _ _ Hhead)
                                               (ffind Htail)
            end in
        match Hy in (⟨ _, e' ⟩ ⇓ v') return P ϵ e' v' with
        | ebs_bool _ b i => HBool ϵ b i
        | ebs_bit _ w n i => HBit ϵ w n i
        | ebs_int _ w z i => HInt ϵ w z i
        | ebs_var _ _ τ i _ Hx => HVar _ _ τ i _ Hx
        | ebs_cast _ _ _ i _ _
                   Hcast He => HCast _ _ _ i _ _ Hcast
                                    He (ebsind _ _ _ He)
        | ebs_error _ err i => HError _ err i
        | ebs_matchkind _ mk i => HMatchkind _ mk i
        | ebs_not _ _ i _ _ Hnot He => HNot _ _ i _ _ Hnot
                                            He (ebsind _ _ _ He)
        | ebs_bitnot _ _ i _ _ _
                     Hnot He => HBitNot _ _ i _ _ _ Hnot
                                       He (ebsind _ _ _ He)
        | ebs_uminus _ _ i _ _ _
                     Hneg He => HUMinus _ _ i _ _ _ Hneg
                                       He (ebsind _ _ _ He)
        | ebs_bop_bit _ _ _ _ _ i _ _ _
                      Hv He1 He2 => HBOPBit _ _ _ _ _ i _ _ _ Hv
                                           He1 (ebsind _ _ _ He1)
                                           He2 (ebsind _ _ _ He2)
        | ebs_plusplus _ _ _ i _ _ _ _ _ _
                       Hw Hconcat He1 He2 => HPlusPlus _ _ _ i _ _ _ _ _ _
                                                      Hw Hconcat
                                                      He1 (ebsind _ _ _ He1)
                                                      He2 (ebsind _ _ _ He2)
        | ebs_bop_int _ _ _ _ _ i _ _ _
                      Hv He1 He2 => HBOPInt _ _ _ _ _ i _ _ _ Hv
                                           He1 (ebsind _ _ _ He1)
                                           He2 (ebsind _ _ _ He2)
        | ebs_bop_bool _ _ _ _ i _ _ _
                      Hb He1 He2 => HBOPBool _ _ _ _ i _ _ _ Hb
                                           He1 (ebsind _ _ _ He1)
                                           He2 (ebsind _ _ _ He2)
        | ebs_eq _ _ _ _ _ i _ _ _
                 Hb He1 He2 => HEq _ _ _ _ _ i _ _ _ Hb
                                  He1 (ebsind _ _ _ He1)
                                  He2 (ebsind _ _ _ He2)
        | ebs_neq _ _ _ _ _ i _ _ _
                  Hb He1 He2 => HNeq _ _ _ _ _ i _ _ _ Hb
                                   He1 (ebsind _ _ _ He1)
                                   He2 (ebsind _ _ _ He2)
        | ebs_hdr_mem _ _ _ i _ _ _ _
                      Hget He => HHdrMem _ _ _ i _ _ _ _ Hget
                                        He (ebsind _ _ _ He)
        | ebs_rec_mem _ _ _ i _ _ _
                      Hget He => HRecMem _ _ _ i _ _ _ Hget
                                        He (ebsind _ _ _ He)
        | ebs_hdr_op _ _ _ i _ _ _
                     Hv He => HHdrOp _ _ _ i _ _ _ Hv
                                    He (ebsind _ _ _ He)
        | ebs_tuple _ _ i _ HR => HTuple _ _ i _ HR (lind HR)
        | ebs_rec_lit _ _ i _ HR => HRecLit _ _ i _ HR (fsind HR)
        | ebs_hdr_lit _ _ _ i _ _
                      HR He => HHdrLit _ _ _ i _ _
                                      HR (fsind HR)
                                      He (ebsind _ _ _ He)
        | ebs_hdr_stack _ _ _ n ni _ HR => HHdrStack _ _ _ n ni _
                                                  HR (ffind HR)
        | ebs_access _ _ i n index ni ts _ _ _
                     Hnth He => HAccess _ _ i n index ni ts _ _ _ Hnth
                                       He (ebsind _ _ _ He)
        | ebs_stk_op _ _ _ i _ _ _ _ _
                     Hv He => HStackOp _ _ _ i _ _ _ _ _ Hv
                                      He (ebsind _ _ _ He)
        end.
    (**[]*)

  End ExprEvalInduction.

  Inductive lvalue_big_step {tags_t : Type} : E.e tags_t -> V.lv -> Prop :=
  | lvbs_var (x : string) (τ : E.t) (i : tags_t) :
      ⧠ Var x:τ @ i ⇓ VAR x
  | lvbs_rec_member (e : E.e tags_t) (x : string)
                (tfs : F.fs string (E.t))
                (i : tags_t) (lv : V.lv) :
      ⧠ e ⇓ lv ->
      ⧠ Mem e:rec { tfs } dot x @ i ⇓ lv DOT x
  | lvbs_hdr_member (e : E.e tags_t) (x : string)
                    (tfs : F.fs string E.t)
                    (i : tags_t) (lv : V.lv):
      ⧠ e ⇓ lv ->
      ⧠ Mem e:hdr { tfs } dot x @ i ⇓ lv DOT x
  | lvbs_stack_access (e : E.e tags_t) (i : tags_t)
                      (lv : V.lv) (n : N) :
      let w := 32%positive in
      ⧠ e ⇓ lv ->
      ⧠ Access e[n] @ i ⇓ lv[n]
  where "⧠ e ⇓ lv" := (lvalue_big_step e lv).
  (**[]*)

  (** Statement big-step semantics. *)
  Inductive stmt_big_step
            {tags_t : Type} (cp : ctrl) (ts : tenv) (aa : aenv)
            (fs : fenv) (ins : ienv) (ϵ : epsilon) :
    ST.s tags_t -> epsilon -> signal -> Prop :=
  | sbs_skip (i : tags_t) :
      ⟪ cp, ts, aa, fs, ins, ϵ, skip @ i ⟫ ⤋ ⟪ ϵ, C ⟫
  | sbs_seq_cont (s1 s2 : ST.s tags_t) (i : tags_t)
                 (ϵ' ϵ'' : epsilon) (sig : signal) :
      ⟪ cp, ts, aa, fs, ins, ϵ,  s1 ⟫ ⤋ ⟪ ϵ',  C ⟫ ->
      ⟪ cp, ts, aa, fs, ins, ϵ', s2 ⟫ ⤋ ⟪ ϵ'', sig ⟫ ->
      ⟪ cp, ts, aa, fs, ins, ϵ,  s1 ; s2 @ i ⟫ ⤋ ⟪ ϵ'', sig ⟫
  | sbs_seq_interrupt (s1 s2 : ST.s tags_t) (i : tags_t)
                         (ϵ' : epsilon) (sig : signal) :
      interrupt sig ->
      ⟪ cp, ts, aa, fs, ins, ϵ, s1 ⟫ ⤋ ⟪ ϵ', sig ⟫ ->
      ⟪ cp, ts, aa, fs, ins, ϵ, s1 ; s2 @ i ⟫ ⤋ ⟪ ϵ', sig ⟫
  | sbs_vardecl (τ : E.t) (x : string)
                (i : tags_t) (v : V.v) :
      V.vdefault τ = v ->
      ⟪ cp, ts, aa, fs, ins, ϵ, var x : τ @ i ⟫ ⤋ ⟪ x ↦ v ;; ϵ, C ⟫
  | sbs_assign (τ : E.t) (e1 e2 : E.e tags_t) (i : tags_t)
               (lv : V.lv) (v : V.v) (ϵ' : epsilon) :
      lv_update lv v ϵ = ϵ' ->
      ⧠ e1 ⇓ lv ->
      ⟨ ϵ, e2 ⟩ ⇓ v ->
      ⟪ cp, ts, aa, fs, ins, ϵ, asgn e1 := e2 : τ @ i ⟫ ⤋ ⟪ ϵ', C ⟫
  | sbs_exit (i : tags_t) :
      ⟪ cp, ts, aa, fs, ins, ϵ, exit @ i ⟫ ⤋ ⟪ ϵ, X ⟫
  | sbs_retvoid (i : tags_t) :
      ⟪ cp, ts, aa, fs, ins, ϵ, returns @ i ⟫ ⤋ ⟪ ϵ, Void ⟫
  | sbs_retfruit (τ : E.t) (e : E.e tags_t)
                 (i : tags_t) (v : V.v) :
      ⟨ ϵ, e ⟩ ⇓ v ->
      ⟪ cp, ts, aa, fs, ins, ϵ, return e:τ @ i ⟫ ⤋ ⟪ ϵ, Fruit v ⟫
  | sbs_cond_true (guard : E.e tags_t)
                  (tru fls : ST.s tags_t) (i : tags_t)
                  (ϵ' : epsilon) (sig : signal) :
      ⟨ ϵ, guard ⟩ ⇓ TRUE ->
      ⟪ cp, ts, aa, fs, ins, ϵ, tru ⟫ ⤋ ⟪ ϵ', sig ⟫ ->
      ⟪ cp, ts, aa, fs, ins, ϵ, if guard:Bool then tru else fls @ i ⟫
        ⤋ ⟪ ϵ', sig ⟫
  | sbs_cond_false (guard : E.e tags_t)
                   (tru fls : ST.s tags_t) (i : tags_t)
                   (ϵ' : epsilon) (sig : signal) :
      ⟨ ϵ, guard ⟩ ⇓ FALSE ->
      ⟪ cp, ts, aa, fs, ins, ϵ, fls ⟫ ⤋ ⟪ ϵ', sig ⟫ ->
      ⟪ cp, ts, aa, fs, ins, ϵ, if guard:Bool then tru else fls @ i ⟫
        ⤋ ⟪ ϵ', sig ⟫
  | sbs_action_call (args : E.args tags_t)
                    (argsv : V.argsv)
                    (a : string) (i : tags_t)
                    (body : ST.s tags_t) (aclosure : aenv)
                    (fclosure : fenv) (ains : ienv)
                    (closure ϵ' ϵ'' ϵ''' : epsilon) :
      (* Looking up action. *)
      alookup aa a = Some (ADecl closure fclosure ains aclosure body) ->
      (* Argument evaluation. *)
      F.relfs
        (P.rel_paramarg
           (fun '(_,e) v  => ⟨ ϵ, e ⟩ ⇓ v)
           (fun '(_,e) lv => ⧠ e ⇓ lv))
        args argsv ->
      (* Copy-in. *)
      copy_in argsv ϵ closure = ϵ' ->
      (* Action evaluation *)
      ⟪ cp, ts, aclosure, fclosure, ains, ϵ', body ⟫ ⤋ ⟪ ϵ'', Void ⟫ ->
      (* Copy-out *)
      copy_out argsv ϵ'' ϵ = ϵ''' ->
      ⟪ cp, ts, aa, fs, ins, ϵ, calling a with args @ i ⟫ ⤋ ⟪ ϵ''', C ⟫
  | sbs_void_call (args : E.args tags_t)
                  (argsv : V.argsv)
                  (f : string) (i : tags_t)
                  (body : ST.s tags_t) (fclosure : fenv) (fins : ienv)
                  (closure ϵ' ϵ'' ϵ''' : epsilon) :
      (* Looking up function. *)
      lookup fs f = Some (FDecl closure fclosure fins body) ->
      (* Argument evaluation. *)
      F.relfs
        (P.rel_paramarg
           (fun '(_,e) v  => ⟨ ϵ, e ⟩ ⇓ v)
           (fun '(_,e) lv => ⧠ e ⇓ lv))
        args argsv ->
      (* Copy-in. *)
      copy_in argsv ϵ closure = ϵ' ->
      (* Function evaluation *)
      ⟪ cp, ts, aa, fclosure, fins, ϵ', body ⟫ ⤋ ⟪ ϵ'', Void ⟫ ->
      (* Copy-out *)
      copy_out argsv ϵ'' ϵ = ϵ''' ->
      ⟪ cp, ts, aa, fs, ins, ϵ, call f with args @ i ⟫ ⤋ ⟪ ϵ''', C ⟫
  | sbs_fruit_call (args : E.args tags_t)
                   (argsv : V.argsv)
                   (f : string) (τ : E.t)
                   (e : E.e tags_t) (i : tags_t)
                   (v : V.v) (lv : V.lv)
                   (body : ST.s tags_t) (fclosure : fenv) (fins : ienv)
                   (closure ϵ' ϵ'' ϵ''' ϵ'''' : epsilon) :
      (* Looking up function. *)
      lookup fs f = Some (FDecl closure fclosure fins body) ->
      (* Argument evaluation. *)
      F.relfs
        (P.rel_paramarg
           (fun '(_,e) v => ⟨ ϵ, e ⟩ ⇓ v)
           (fun '(_,e) lv => ⧠ e ⇓ lv))
        args argsv ->
      (* Copy-in. *)
      copy_in argsv ϵ closure = ϵ' ->
      (* Lvalue Evaluation. *)
      ⧠ e ⇓ lv ->
      (* Function evaluation. *)
      ⟪ cp, ts, aa, fclosure, fins, ϵ', body ⟫ ⤋ ⟪ ϵ'', Fruit v ⟫ ->
      (* Copy-out. *)
      copy_out argsv ϵ'' ϵ = ϵ''' ->
      (* Assignment to lvalue. *)
      lv_update lv v ϵ''' = ϵ'''' ->
      ⟪ cp, ts, aa, fs, ins, ϵ, let e:τ := call f with args @ i ⟫ ⤋ ⟪ ϵ'''', C ⟫
  | sbs_apply (args : E.args tags_t)
              (argsv : V.argsv)
              (x : string) (i : tags_t)
              (body : ST.s tags_t) (fclosure : fenv) (iins : ienv)
              (tblclosure : tenv) (aclosure : aenv)
              (closure ϵ' ϵ'' ϵ''' ϵ'''' : epsilon) :
      (* Instance lookup. *)
      ilookup ins x = Some (CInst closure fclosure iins tblclosure aclosure body) ->
      (* Argument evaluation. *)
      F.relfs
        (P.rel_paramarg
           (fun '(_,e) v => ⟨ ϵ, e ⟩ ⇓ v)
           (fun '(_,e) lv => ⧠ e ⇓ lv))
        args argsv ->
      (* Copy-in. *)
      copy_in argsv ϵ closure = ϵ' ->
      (* Apply block evaluation. *)
      ⟪ cp, tblclosure, aclosure, fclosure, iins, ϵ', body ⟫ ⤋ ⟪ ϵ'', Void ⟫ ->
      (* Copy-out. *)
      copy_out argsv ϵ'' ϵ = ϵ''' ->
      ⟪ cp, ts, aa, fs, ins, ϵ, apply x with args @ i ⟫ ⤋ ⟪ ϵ'''', C ⟫
  | sbs_invoke (x : string) (i : tags_t)
               (es : entries)
               (ky : list (E.t * E.e tags_t * E.matchkind))
               (acts : list (string))
               (vky : list (V.v * E.matchkind))
               (a : string) (args : E.args tags_t)
               (ϵ' : epsilon)
               (sig : signal) :
      cp x = Some es ->
      ts x = Some (CD.Table ky acts) ->
      Forall2 (fun '(_,k,_) '(v,_) => ⟨ ϵ, k ⟩ ⇓ v) ky vky ->
      (* Black box, need extra assumption for soundness *)
      es vky acts = (a,args) ->
      ⟪ cp, ts, aa, fs, ins, ϵ, calling a with args @ i ⟫ ⤋ ⟪ ϵ', sig ⟫ ->
      ⟪ cp, ts, aa, fs, ins, ϵ, invoke x @ i ⟫ ⤋ ⟪ ϵ', sig ⟫
  where "⟪ cp , ts , aa , fs , ins , ϵ , s ⟫ ⤋ ⟪ ϵ' , sig ⟫"
          := (stmt_big_step cp ts aa fs ins ϵ s ϵ' sig).

  (** Declaration big-step semantics. *)
  Inductive decl_big_step
            {tags_t : Type} (cp : @ctrl tags_t) (cs : cenv) (fns : fenv)
            (ins : ienv) (ϵ : epsilon) : D.d tags_t -> epsilon -> ienv -> Prop :=
  | dbs_vardecl (τ : E.t) (x : string) (i : tags_t) :
      let v := V.vdefault τ in
      ⧼ cp, cs, fns, ins, ϵ, Var x:τ @ i ⧽ ⟱  ⧼ x ↦ v ;; ϵ, ins ⧽
  | dbs_varinit (τ : E.t) (x : string)
                (e : E.e tags_t) (i : tags_t) (v : V.v) :
      ⟨ ϵ, e ⟩ ⇓ v ->
      ⧼ cp, cs, fns, ins, ϵ, Let x:τ := e @ i ⧽ ⟱  ⧼ x ↦ v ;; ϵ, ins ⧽
  | dbs_instantiate (c : string) (x : string)
                    (cargs : E.constructor_args tags_t)
                    (vargs : F.fs string (either (V.v) inst)) (i : tags_t)
                    (ctrlclosure : cenv) (fclosure : fenv)
                    (iclosure ins' ins'' : ienv)
                    (body : CD.d tags_t) (applyblk : ST.s tags_t)
                    (closure ϵ' ϵ'' : epsilon) (tbls : tenv) (aa : aenv) :
      clookup cs c = Some (CDecl ctrlclosure closure fclosure iclosure body applyblk) ->
      F.relfs
        (fun carg v =>
           match carg,v with
           | E.CAExpr e, Left v => ⟨ ϵ, e ⟩ ⇓ v
           | E.CAName c, Right cinst => ilookup ins c = Some cinst
           | _, _ => False
           end) cargs vargs ->
      F.fold (fun x v '(ϵ,ins) =>
                match v with
                | Left v => (!{ x ↦ v;; ϵ }!, ins)
                | Right cinst => (ϵ, iupdate ins x cinst)
                end) vargs (closure,iclosure) = (ϵ',ins') ->
      let empty_tbls := Env.empty (string) (CD.table tags_t) in
      let empty_acts := AEnv (Env.empty (string) adecl) in
      ⦉ cp, cs, empty_tbls, empty_acts, fclosure, ins', ϵ', body ⦊
        ⟱  ⦉ ϵ'', ins'', aa, tbls ⦊ ->
      let ins''' := iupdate ins x (CInst ϵ'' fclosure ins' tbls aa applyblk) in
      ⧼ cp, cs, fns, ins, ϵ, Instance x of c(cargs) @ i ⧽ ⟱  ⧼ ϵ, ins''' ⧽
  | dbs_declseq (d1 d2 : D.d tags_t) (i : tags_t)
                (ϵ' ϵ'' : epsilon) (ins' ins'' : ienv) :
      ⧼ cp, cs, fns, ins,  ϵ,  d1 ⧽ ⟱  ⧼ ϵ',  ins'  ⧽ ->
      ⧼ cp, cs, fns, ins', ϵ', d2 ⧽ ⟱  ⧼ ϵ'', ins'' ⧽ ->
      ⧼ cp, cs, fns, ins,  ϵ,  d1 ;; d2 @ i ⧽ ⟱  ⧼ ϵ'', ins'' ⧽
  where "⧼ cp , cs , fnv , ins1 , ϵ1 , d ⧽ ⟱  ⧼ ϵ2 , ins2 ⧽"
          := (decl_big_step cp cs fnv ins1 ϵ1 d ϵ2 ins2)
  (**[]*)

  (** Control declaration big-step semantics. *)
  with ctrldecl_big_step
       {tags_t : Type} (cp : @ctrl tags_t) (cs : cenv) (fns : fenv) (ins : ienv) (ϵ : epsilon)
       : tenv -> aenv -> CD.d tags_t -> epsilon -> ienv -> aenv -> tenv -> Prop :=
  | cdbs_action (tbls : tenv) (aa aa' : @aenv tags_t)
                (a : string)
                (params : E.params)
                (body : ST.s tags_t) (i : tags_t) :
      let aa' := aupdate aa a (ADecl ϵ fns ins aa body) in
      ⦉ cp, cs, tbls, aa, fns, ins, ϵ, action a (params) {body} @ i ⦊
        ⟱  ⦉ ϵ, ins, aa', tbls ⦊
  | cdbs_table (tbls : tenv) (aa : aenv) (t : string)
               (kys : list
                        (E.t * E.e tags_t * E.matchkind))
               (actns : list (string))
               (i : tags_t) :
      let tbl := CD.Table kys actns in
      ⦉ cp, cs, tbls, aa, fns, ins, ϵ, table t key:=kys actions:=actns @ i ⦊
        ⟱  ⦉ ϵ, ins, aa, t ↦ tbl;; tbls ⦊
  | cdbs_decl (tbls : tenv) (aa : aenv)
              (d : D.d tags_t) (i : tags_t)
              (ϵ' : epsilon) (ins' : ienv) :
      ⧼ cp, cs, fns, ins, ϵ, d ⧽ ⟱  ⧼ ϵ', ins' ⧽ ->
      ⦉ cp, cs, tbls, aa, fns, ins, ϵ, Decl d @ i ⦊ ⟱  ⦉ ϵ', ins', aa, tbls ⦊
  | cdbs_seq (d1 d2 : CD.d tags_t) (i : tags_t)
             (ϵ' ϵ'' : epsilon) (ins' ins'' : ienv)
             (aa aa' aa'' : aenv) (tbls tbls' tbls'' : tenv) :
      ⦉ cp, cs, tbls,  aa,  fns, ins,  ϵ,  d1 ⦊ ⟱  ⦉ ϵ',  ins',  aa',  tbls'  ⦊ ->
      ⦉ cp, cs, tbls', aa', fns, ins', ϵ', d2 ⦊ ⟱  ⦉ ϵ'', ins'', aa'', tbls'' ⦊ ->
      ⦉ cp, cs, tbls,  aa,  fns, ins,  ϵ, d1 ;c; d2 @ i ⦊
        ⟱  ⦉ ϵ'', ins'', aa'', tbls'' ⦊
  where "⦉ cp , cs , ts1 , aa1 , fns , ins1 , ϵ1 , d ⦊ ⟱  ⦉ ϵ2 , ins2 , aa2 , ts2 ⦊"
          := (ctrldecl_big_step cp cs fns ins1 ϵ1 ts1 aa1 d ϵ2 ins2 aa2 ts2).
  (**[]*)

  (** Top-level declaration big-step semantics. *)
  Inductive topdecl_big_step
            {tags_t : Type} (cp : ctrl) (cs : cenv)
            (fns : fenv) (ins : ienv) (ϵ : epsilon)
    : TP.d tags_t -> epsilon -> ienv -> fenv -> cenv -> Prop :=
  | tpbs_control (c : string) (cparams : E.constructor_params)
                 (params : E.params) (body : CD.d tags_t)
                 (apply_blk : ST.s tags_t) (i : tags_t) (cs' : @cenv tags_t) :
      let cs' := cupdate cs c (CDecl cs ϵ fns ins body apply_blk) in
      ⦇ cp, cs, fns, ins, ϵ,
        control c (cparams)(params) apply { apply_blk } where { body } @ i ⦈
        ⟱  ⦇ ϵ, ins, fns, cs' ⦈
  | tpbs_fruit_function (f : string) (params : E.params)
                        (τ : E.t) (body : ST.s tags_t) (i : tags_t) :
      let fns' := update fns f (FDecl ϵ fns ins body) in
      ⦇ cp, cs, fns, ins, ϵ, fn f (params) -> τ { body } @ i ⦈
        ⟱  ⦇ ϵ, ins, fns', cs ⦈
  | tpbs_void_function (f : string) (params : E.params)
                       (body : ST.s tags_t) (i : tags_t) :
      let fns' := update fns f (FDecl ϵ fns ins body) in
      ⦇ cp, cs, fns, ins, ϵ, void f (params) { body } @ i ⦈
        ⟱  ⦇ ϵ, ins, fns', cs ⦈
  | tpbs_decl (d : D.d tags_t) (i : tags_t)
              (ϵ' : epsilon) (ins' : ienv) :
      ⧼ cp, cs, fns, ins, ϵ, d ⧽ ⟱  ⧼ ϵ', ins' ⧽ ->
      ⦇ cp, cs, fns, ins, ϵ, DECL d @ i ⦈ ⟱  ⦇ ϵ', ins', fns, cs ⦈
  | tpbs_seq (d1 d2 : TP.d tags_t) (i : tags_t)
             (ϵ' ϵ'' : epsilon) (ins' ins'' : ienv)
             (fns' fns'' : fenv) (cs' cs'' : cenv) :
      ⦇ cp, cs,  fns,  ins,  ϵ,  d1 ⦈ ⟱  ⦇ ϵ',  ins',  fns',  cs'  ⦈ ->
      ⦇ cp, cs', fns', ins', ϵ', d2 ⦈ ⟱  ⦇ ϵ'', ins'', fns'', cs'' ⦈ ->
      ⦇ cp, cs,  fns,  ins,  ϵ, d1 ;%; d2 @ i ⦈
        ⟱  ⦇ ϵ'', ins'', fns'', cs'' ⦈
  where "⦇ cp , cs1 , fns1 , ins1 , ϵ1 , d ⦈ ⟱  ⦇ ϵ2 , ins2 , fns2 , cs2 ⦈"
          := (topdecl_big_step cp cs1 fns1 ins1 ϵ1 d ϵ2 ins2 fns2 cs2).
  (**[]*)
End Step.
