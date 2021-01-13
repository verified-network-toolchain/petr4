Require Import Coq.Lists.List.
Require Import Coq.Numbers.BinNums.
Require Import Coq.Bool.Bvector.
Require Import Strings.String.

Require Import Petr4.P4String.
Require Import Petr4.Syntax.
Require Import Petr4.Typed.

Open Scope string_scope.

Definition decl1 := [{| tags := tt; str := "NoError" |};
                     {| tags := tt; str := "PacketTooShort" |};
                     {| tags := tt; str := "NoMatch" |};
                     {| tags := tt; str := "StackOutOfBounds" |};
                     {| tags := tt; str := "HeaderTooShort" |};
                     {| tags := tt; str := "ParserTimeout" |};
                     {| tags := tt; str := "ParserInvalidArgument" |}].

Axiom decl2 : Declaration unit.

Axiom decl3 : Declaration unit.

Axiom decl4 : Declaration unit.

Axiom decl5 : Declaration unit.

Axiom decl6 : Declaration unit.

Axiom decl7 : Declaration unit.

Check (MkDeclarationField tt (TypBool tt) {| tags := tt; str := "ingress_port" |}).

Definition standard_metadata_t := DeclStruct tt
    {| tags := tt; str := "standard_metadata_t" |}
    [(MkDeclarationField tt  {| tags := tt; str := "ingress_port" |});
     (MkDeclarationField tt  {| tags := tt; str := "egress_spec" |});
     (MkDeclarationField tt  {| tags := tt; str := "egress_port" |});
     (MkDeclarationField tt  {| tags := tt; str := "instance_type" |});
     (MkDeclarationField tt  {| tags := tt; str := "packet_length" |});
     (MkDeclarationField tt  {| tags := tt; str := "enq_timestamp" |});
     (MkDeclarationField tt  {| tags := tt; str := "enq_qdepth" |});
     (MkDeclarationField tt  {| tags := tt; str := "deq_timedelta" |});
     (MkDeclarationField tt  {| tags := tt; str := "deq_qdepth" |});
     (MkDeclarationField tt 
         {| tags := tt; str := "ingress_global_timestamp" |});
     (MkDeclarationField tt 
         {| tags := tt; str := "egress_global_timestamp" |});
     (MkDeclarationField tt  {| tags := tt; str := "mcast_grp" |});
     (MkDeclarationField tt  {| tags := tt; str := "egress_rid" |});
     (MkDeclarationField tt  {| tags := tt; str := "checksum_error" |});
     (MkDeclarationField tt  {| tags := tt; str := "parser_error" |});
     (MkDeclarationField tt  {| tags := tt; str := "priority" |})].

Axiom decl8 : Declaration unit.

Axiom decl9 : Declaration unit.

Axiom decl10 : Declaration unit.

Axiom decl11 : Declaration unit.

Axiom decl12 : Declaration unit.

Axiom decl13 : Declaration unit.

Axiom decl14 : Declaration unit.

Axiom decl15 : Declaration unit.

Axiom decl16 : Declaration unit.

Axiom decl17 : Declaration unit.

Axiom decl18 : Declaration unit.

Axiom decl19 : Declaration unit.

Axiom decl20 : Declaration unit.

Axiom decl21 : Declaration unit.

Axiom decl22 : Declaration unit.

Axiom decl23 : Declaration unit.

Axiom decl24 : Declaration unit.

Axiom decl25 : Declaration unit.

Axiom decl26 : Declaration unit.

Axiom decl27 : Declaration unit.

Axiom decl28 : Declaration unit.

Axiom decl29 : Declaration unit.

Axiom decl30 : Declaration unit.

Axiom decl31 : Declaration unit.

Axiom decl32 : Declaration unit.

Axiom decl33 : Declaration unit.

Axiom decl34 : Declaration unit.

Axiom decl35 : Declaration unit.

Axiom decl36 : Declaration unit.

Axiom decl37 : Declaration unit.

Axiom decl38 : Declaration unit.

Axiom decl39 : Declaration unit.

Axiom decl40 : Declaration unit.

Axiom decl41 : Declaration unit.

Axiom decl42 : Declaration unit.

Definition metadata := DeclStruct tt {| tags := tt; str := "metadata" |} nil.

Definition headers := DeclStruct tt {| tags := tt; str := "headers" |} nil.

Definition MyParser := DeclParser tt {| tags := tt; str := "MyParser" |} nil
    [(MkParameter false 
         (TypTypeName (BareName {| tags := tt; str := "packet_in" |})) 
         {| tags := tt; str := "packet" |});
     (MkParameter false 
         (TypTypeName (BareName {| tags := tt; str := "headers" |})) 
         {| tags := tt; str := "hdr" |});
     (MkParameter false 
         (TypTypeName (BareName {| tags := tt; str := "metadata" |})) 
         {| tags := tt; str := "meta" |});
     (MkParameter false 
         (TypTypeName (BareName {| tags := tt;
                                   str := "standard_metadata_t" |})) 
         {| tags := tt; str := "standard_metadata" |})] nil nil [].

Definition MyIngress := DeclControl tt {| tags := tt; str := "MyIngress" |}
    nil
    [(MkParameter false 
         (TypTypeName (BareName {| tags := tt; str := "headers" |})) 
         {| tags := tt; str := "hdr" |});
     (MkParameter false 
         (TypTypeName (BareName {| tags := tt; str := "metadata" |})) 
         {| tags := tt; str := "meta" |});
     (MkParameter false 
         (TypTypeName (BareName {| tags := tt;
                                   str := "standard_metadata_t" |})) 
         {| tags := tt; str := "standard_metadata" |})] nil
    [(DeclAction tt {| tags := tt; str := "drop" |} nil nil
     (BlockCons (MkStatement tt
     (StatMethodCall ((MkExpression tt
                          (ExpName (BareName {| tags := tt;
                                                str := "mark_to_drop" |}))  )
     nil []) ) (BlockEmpty tt)))] (BlockCons (MkStatement tt
    (StatMethodCall ((MkExpression tt
                         (ExpName (BareName {| tags := tt; str := "drop" |}))
                          ) nil nil) ) (BlockEmpty tt)).

Definition MyEgress := DeclControl tt {| tags := tt; str := "MyEgress" |} nil
    [(MkParameter false 
         (TypTypeName (BareName {| tags := tt; str := "headers" |})) 
         {| tags := tt; str := "hdr" |});
     (MkParameter false 
         (TypTypeName (BareName {| tags := tt; str := "metadata" |})) 
         {| tags := tt; str := "meta" |});
     (MkParameter false 
         (TypTypeName (BareName {| tags := tt;
                                   str := "standard_metadata_t" |})) 
         {| tags := tt; str := "standard_metadata" |})] nil nil
    (BlockEmpty tt).

Definition MyDeparser := DeclControl tt {| tags := tt; str := "MyDeparser" |}
    nil
    [(MkParameter false 
         (TypTypeName (BareName {| tags := tt; str := "packet_out" |})) 
         {| tags := tt; str := "packet" |});
     (MkParameter false 
         (TypTypeName (BareName {| tags := tt; str := "headers" |})) 
         {| tags := tt; str := "hdr" |})] nil nil (BlockEmpty tt).

Definition MyVerifyChecksum := DeclControl tt
    {| tags := tt; str := "MyVerifyChecksum" |} nil
    [(MkParameter false 
         (TypTypeName (BareName {| tags := tt; str := "headers" |})) 
         {| tags := tt; str := "hdr" |});
     (MkParameter false 
         (TypTypeName (BareName {| tags := tt; str := "metadata" |})) 
         {| tags := tt; str := "meta" |})] nil nil (BlockEmpty tt).

Definition MyComputeChecksum := DeclControl tt
    {| tags := tt; str := "MyComputeChecksum" |} nil
    [(MkParameter false 
         (TypTypeName (BareName {| tags := tt; str := "headers" |})) 
         {| tags := tt; str := "hdr" |});
     (MkParameter false 
         (TypTypeName (BareName {| tags := tt; str := "metadata" |})) 
         {| tags := tt; str := "meta" |})] nil nil (BlockEmpty tt).

Definition main := DeclInstantiation tt 
    [((MkExpression tt (ExpNamelessInstantiation  nil)  );
     ((MkExpression tt (ExpNamelessInstantiation  nil)  );
     ((MkExpression tt (ExpNamelessInstantiation  nil)  );
     ((MkExpression tt (ExpNamelessInstantiation  nil)  );
     ((MkExpression tt (ExpNamelessInstantiation  nil)  );
     ((MkExpression tt (ExpNamelessInstantiation  nil)  )]
    {| tags := tt; str := "main" |} .

Definition program := [decl1; decl2; decl3; decl4; decl5; decl6; decl7;
                       standard_metadata_t; decl8; decl9; decl10; decl11;
                       decl12; decl13; decl14; decl15; decl16; decl17;
                       decl18; decl19; decl20; decl21; decl22; decl23;
                       decl24; decl25; decl26; decl27; decl28; decl29;
                       decl30; decl31; decl32; decl33; decl34; decl35;
                       decl36; decl37; decl38; decl39; decl40; decl41;
                       decl42; metadata; headers; MyParser; MyIngress;
                       MyEgress; MyDeparser; MyVerifyChecksum;
                       MyComputeChecksum; main].
