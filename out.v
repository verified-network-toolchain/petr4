Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Strings.String.

Require Import Petr4.P4String.
Require Import Petr4.P4Int.
Require Import Petr4.Syntax.
Require Import Petr4.Typed.

Open Scope string_scope.

Import ListNotations.

Notation stags := P4String.tags.

Notation itags := P4Int.tags.

Definition decl1 := DeclError tt
    [{| stags := tt; str := "NoError" |};
     {| stags := tt; str := "PacketTooShort" |};
     {| stags := tt; str := "NoMatch" |};
     {| stags := tt; str := "StackOutOfBounds" |};
     {| stags := tt; str := "HeaderTooShort" |};
     {| stags := tt; str := "ParserTimeout" |};
     {| stags := tt; str := "ParserInvalidArgument" |}].

Definition packet_in := DeclExternObject tt
    {| stags := tt; str := "packet_in" |} nil
    [(ProtoMethod tt (TypBit 32) {| stags := tt; str := "length" |} nil nil);
     (ProtoMethod tt TypVoid {| stags := tt; str := "advance" |} nil
          [(MkParameter false In (TypBit 32) None
                {| stags := tt; str := "sizeInBits" |})]);
     (ProtoMethod tt (TypTypeName (BareName {| stags := tt; str := "T1" |}))
          {| stags := tt; str := "lookahead" |}
          [{| stags := tt; str := "T1" |}] nil);
     (ProtoMethod tt TypVoid {| stags := tt; str := "extract" |}
          [{| stags := tt; str := "T0" |}]
          [(MkParameter false Out
                (TypTypeName (BareName {| stags := tt; str := "T0" |})) 
                None {| stags := tt; str := "variableSizeHeader" |});
           (MkParameter false In (TypBit 32) None
                {| stags := tt; str := "variableFieldSizeInBits" |})]);
     (ProtoMethod tt TypVoid {| stags := tt; str := "extract" |}
          [{| stags := tt; str := "T" |}]
          [(MkParameter false Out
                (TypTypeName (BareName {| stags := tt; str := "T" |})) 
                None {| stags := tt; str := "hdr" |})])].

Definition packet_out := DeclExternObject tt
    {| stags := tt; str := "packet_out" |} nil
    [(ProtoMethod tt TypVoid {| stags := tt; str := "emit" |}
          [{| stags := tt; str := "T2" |}]
          [(MkParameter false In
                (TypTypeName (BareName {| stags := tt; str := "T2" |})) 
                None {| stags := tt; str := "hdr" |})])].

Definition verify := DeclExternFunction tt TypVoid
    {| stags := tt; str := "verify" |} nil
    [(MkParameter false In TypBool None {| stags := tt; str := "check" |});
     (MkParameter false In TypError None
          {| stags := tt; str := "toSignal" |})].

Definition NoAction := DeclAction tt {| stags := tt; str := "NoAction" |} nil
    nil (BlockEmpty tt).

Definition decl2 := DeclMatchKind tt
    [{| stags := tt; str := "exact" |}; {| stags := tt; str := "ternary" |};
     {| stags := tt; str := "lpm" |}].

Definition decl3 := DeclMatchKind tt
    [{| stags := tt; str := "range" |}; {| stags := tt; str := "selector" |}].

Definition standard_metadata_t := DeclStruct tt
    {| stags := tt; str := "standard_metadata_t" |}
    [(MkDeclarationField tt (TypBit 9)
          {| stags := tt; str := "ingress_port" |});
     (MkDeclarationField tt (TypBit 9)
          {| stags := tt; str := "egress_spec" |});
     (MkDeclarationField tt (TypBit 9)
          {| stags := tt; str := "egress_port" |});
     (MkDeclarationField tt (TypBit 32)
          {| stags := tt; str := "instance_type" |});
     (MkDeclarationField tt (TypBit 32)
          {| stags := tt; str := "packet_length" |});
     (MkDeclarationField tt (TypBit 32)
          {| stags := tt; str := "enq_timestamp" |});
     (MkDeclarationField tt (TypBit 19)
          {| stags := tt; str := "enq_qdepth" |});
     (MkDeclarationField tt (TypBit 32)
          {| stags := tt; str := "deq_timedelta" |});
     (MkDeclarationField tt (TypBit 19)
          {| stags := tt; str := "deq_qdepth" |});
     (MkDeclarationField tt (TypBit 48)
          {| stags := tt; str := "ingress_global_timestamp" |});
     (MkDeclarationField tt (TypBit 48)
          {| stags := tt; str := "egress_global_timestamp" |});
     (MkDeclarationField tt (TypBit 16)
          {| stags := tt; str := "mcast_grp" |});
     (MkDeclarationField tt (TypBit 16)
          {| stags := tt; str := "egress_rid" |});
     (MkDeclarationField tt (TypBit 1)
          {| stags := tt; str := "checksum_error" |});
     (MkDeclarationField tt TypError
          {| stags := tt; str := "parser_error" |});
     (MkDeclarationField tt (TypBit 3) {| stags := tt; str := "priority" |})].

Definition CounterType := DeclEnum tt {| stags := tt; str := "CounterType" |}
    [{| stags := tt; str := "packets" |}; {| stags := tt; str := "bytes" |};
     {| stags := tt; str := "packets_and_bytes" |}].

Definition MeterType := DeclEnum tt {| stags := tt; str := "MeterType" |}
    [{| stags := tt; str := "packets" |}; {| stags := tt; str := "bytes" |}].

Definition counter := DeclExternObject tt {| stags := tt; str := "counter" |}
    nil
    [(ProtoConstructor tt {| stags := tt; str := "counter" |}
          [(MkParameter false Directionless (TypBit 32) None
                {| stags := tt; str := "size" |});
           (MkParameter false Directionless
                (TypTypeName
                 (BareName {| stags := tt; str := "CounterType" |})) 
                None {| stags := tt; str := "type" |})]);
     (ProtoMethod tt TypVoid {| stags := tt; str := "count" |} nil
          [(MkParameter false In (TypBit 32) None
                {| stags := tt; str := "index" |})])].

Definition direct_counter := DeclExternObject tt
    {| stags := tt; str := "direct_counter" |} nil
    [(ProtoConstructor tt {| stags := tt; str := "direct_counter" |}
          [(MkParameter false Directionless
                (TypTypeName
                 (BareName {| stags := tt; str := "CounterType" |})) 
                None {| stags := tt; str := "type" |})]);
     (ProtoMethod tt TypVoid {| stags := tt; str := "count" |} nil nil)].

Definition meter := DeclExternObject tt {| stags := tt; str := "meter" |} nil
    [(ProtoConstructor tt {| stags := tt; str := "meter" |}
          [(MkParameter false Directionless (TypBit 32) None
                {| stags := tt; str := "size" |});
           (MkParameter false Directionless
                (TypTypeName
                 (BareName {| stags := tt; str := "MeterType" |})) None
                {| stags := tt; str := "type" |})]);
     (ProtoMethod tt TypVoid {| stags := tt; str := "execute_meter" |}
          [{| stags := tt; str := "T3" |}]
          [(MkParameter false In (TypBit 32) None
                {| stags := tt; str := "index" |});
           (MkParameter false Out
                (TypTypeName (BareName {| stags := tt; str := "T3" |})) 
                None {| stags := tt; str := "result" |})])].

Definition direct_meter := DeclExternObject tt
    {| stags := tt; str := "direct_meter" |} [{| stags := tt; str := "T4" |}]
    [(ProtoConstructor tt {| stags := tt; str := "direct_meter" |}
          [(MkParameter false Directionless
                (TypTypeName
                 (BareName {| stags := tt; str := "MeterType" |})) None
                {| stags := tt; str := "type" |})]);
     (ProtoMethod tt TypVoid {| stags := tt; str := "read" |} nil
          [(MkParameter false Out
                (TypTypeName (BareName {| stags := tt; str := "T4" |})) 
                None {| stags := tt; str := "result" |})])].

Definition register := DeclExternObject tt
    {| stags := tt; str := "register" |} [{| stags := tt; str := "T5" |}]
    [(ProtoConstructor tt {| stags := tt; str := "register" |}
          [(MkParameter false Directionless (TypBit 32) None
                {| stags := tt; str := "size" |})]);
     (ProtoMethod tt TypVoid {| stags := tt; str := "write" |} nil
          [(MkParameter false In (TypBit 32) None
                {| stags := tt; str := "index" |});
           (MkParameter false In
                (TypTypeName (BareName {| stags := tt; str := "T5" |})) 
                None {| stags := tt; str := "value" |})]);
     (ProtoMethod tt TypVoid {| stags := tt; str := "read" |} nil
          [(MkParameter false Out
                (TypTypeName (BareName {| stags := tt; str := "T5" |})) 
                None {| stags := tt; str := "result" |});
           (MkParameter false In (TypBit 32) None
                {| stags := tt; str := "index" |})])].

Definition action_profile := DeclExternObject tt
    {| stags := tt; str := "action_profile" |} nil
    [(ProtoConstructor tt {| stags := tt; str := "action_profile" |}
          [(MkParameter false Directionless (TypBit 32) None
                {| stags := tt; str := "size" |})])].

Definition random := DeclExternFunction tt TypVoid
    {| stags := tt; str := "random" |} [{| stags := tt; str := "T6" |}]
    [(MkParameter false Out
          (TypTypeName (BareName {| stags := tt; str := "T6" |})) None
          {| stags := tt; str := "result" |});
     (MkParameter false In
          (TypTypeName (BareName {| stags := tt; str := "T6" |})) None
          {| stags := tt; str := "lo" |});
     (MkParameter false In
          (TypTypeName (BareName {| stags := tt; str := "T6" |})) None
          {| stags := tt; str := "hi" |})].

Definition digest := DeclExternFunction tt TypVoid
    {| stags := tt; str := "digest" |} [{| stags := tt; str := "T7" |}]
    [(MkParameter false In (TypBit 32) None
          {| stags := tt; str := "receiver" |});
     (MkParameter false In
          (TypTypeName (BareName {| stags := tt; str := "T7" |})) None
          {| stags := tt; str := "data" |})].

Definition HashAlgorithm := DeclEnum tt
    {| stags := tt; str := "HashAlgorithm" |}
    [{| stags := tt; str := "crc32" |};
     {| stags := tt; str := "crc32_custom" |};
     {| stags := tt; str := "crc16" |};
     {| stags := tt; str := "crc16_custom" |};
     {| stags := tt; str := "random" |};
     {| stags := tt; str := "identity" |};
     {| stags := tt; str := "csum16" |}; {| stags := tt; str := "xor16" |}].

Definition mark_to_drop := DeclExternFunction tt TypVoid
    {| stags := tt; str := "mark_to_drop" |} nil nil.

Definition mark_to_drop_2 := DeclExternFunction tt TypVoid
    {| stags := tt; str := "mark_to_drop" |} nil
    [(MkParameter false InOut
          (TypTypeName
           (BareName {| stags := tt; str := "standard_metadata_t" |})) 
          None {| stags := tt; str := "standard_metadata" |})].

Definition hash := DeclExternFunction tt TypVoid
    {| stags := tt; str := "hash" |}
    [{| stags := tt; str := "O" |}; {| stags := tt; str := "T8" |};
     {| stags := tt; str := "D" |}; {| stags := tt; str := "M" |}]
    [(MkParameter false Out
          (TypTypeName (BareName {| stags := tt; str := "O" |})) None
          {| stags := tt; str := "result" |});
     (MkParameter false In
          (TypTypeName (BareName {| stags := tt; str := "HashAlgorithm" |}))
          None {| stags := tt; str := "algo" |});
     (MkParameter false In
          (TypTypeName (BareName {| stags := tt; str := "T8" |})) None
          {| stags := tt; str := "base" |});
     (MkParameter false In
          (TypTypeName (BareName {| stags := tt; str := "D" |})) None
          {| stags := tt; str := "data" |});
     (MkParameter false In
          (TypTypeName (BareName {| stags := tt; str := "M" |})) None
          {| stags := tt; str := "max" |})].

Definition action_selector := DeclExternObject tt
    {| stags := tt; str := "action_selector" |} nil
    [(ProtoConstructor tt {| stags := tt; str := "action_selector" |}
          [(MkParameter false Directionless
                (TypTypeName
                 (BareName {| stags := tt; str := "HashAlgorithm" |})) 
                None {| stags := tt; str := "algorithm" |});
           (MkParameter false Directionless (TypBit 32) None
                {| stags := tt; str := "size" |});
           (MkParameter false Directionless (TypBit 32) None
                {| stags := tt; str := "outputWidth" |})])].

Definition CloneType := DeclEnum tt {| stags := tt; str := "CloneType" |}
    [{| stags := tt; str := "I2E" |}; {| stags := tt; str := "E2E" |}].

Definition Checksum16 := DeclExternObject tt
    {| stags := tt; str := "Checksum16" |} nil
    [(ProtoConstructor tt {| stags := tt; str := "Checksum16" |} nil);
     (ProtoMethod tt (TypBit 16) {| stags := tt; str := "get" |}
          [{| stags := tt; str := "D9" |}]
          [(MkParameter false In
                (TypTypeName (BareName {| stags := tt; str := "D9" |})) 
                None {| stags := tt; str := "data" |})])].

Definition verify_checksum := DeclExternFunction tt TypVoid
    {| stags := tt; str := "verify_checksum" |}
    [{| stags := tt; str := "T10" |}; {| stags := tt; str := "O11" |}]
    [(MkParameter false In TypBool None
          {| stags := tt; str := "condition" |});
     (MkParameter false In
          (TypTypeName (BareName {| stags := tt; str := "T10" |})) None
          {| stags := tt; str := "data" |});
     (MkParameter false InOut
          (TypTypeName (BareName {| stags := tt; str := "O11" |})) None
          {| stags := tt; str := "checksum" |});
     (MkParameter false Directionless
          (TypTypeName (BareName {| stags := tt; str := "HashAlgorithm" |}))
          None {| stags := tt; str := "algo" |})].

Definition update_checksum := DeclExternFunction tt TypVoid
    {| stags := tt; str := "update_checksum" |}
    [{| stags := tt; str := "T12" |}; {| stags := tt; str := "O13" |}]
    [(MkParameter false In TypBool None
          {| stags := tt; str := "condition" |});
     (MkParameter false In
          (TypTypeName (BareName {| stags := tt; str := "T12" |})) None
          {| stags := tt; str := "data" |});
     (MkParameter false InOut
          (TypTypeName (BareName {| stags := tt; str := "O13" |})) None
          {| stags := tt; str := "checksum" |});
     (MkParameter false Directionless
          (TypTypeName (BareName {| stags := tt; str := "HashAlgorithm" |}))
          None {| stags := tt; str := "algo" |})].

Definition verify_checksum_with_payload := DeclExternFunction tt TypVoid
    {| stags := tt; str := "verify_checksum_with_payload" |}
    [{| stags := tt; str := "T14" |}; {| stags := tt; str := "O15" |}]
    [(MkParameter false In TypBool None
          {| stags := tt; str := "condition" |});
     (MkParameter false In
          (TypTypeName (BareName {| stags := tt; str := "T14" |})) None
          {| stags := tt; str := "data" |});
     (MkParameter false InOut
          (TypTypeName (BareName {| stags := tt; str := "O15" |})) None
          {| stags := tt; str := "checksum" |});
     (MkParameter false Directionless
          (TypTypeName (BareName {| stags := tt; str := "HashAlgorithm" |}))
          None {| stags := tt; str := "algo" |})].

Definition update_checksum_with_payload := DeclExternFunction tt TypVoid
    {| stags := tt; str := "update_checksum_with_payload" |}
    [{| stags := tt; str := "T16" |}; {| stags := tt; str := "O17" |}]
    [(MkParameter false In TypBool None
          {| stags := tt; str := "condition" |});
     (MkParameter false In
          (TypTypeName (BareName {| stags := tt; str := "T16" |})) None
          {| stags := tt; str := "data" |});
     (MkParameter false InOut
          (TypTypeName (BareName {| stags := tt; str := "O17" |})) None
          {| stags := tt; str := "checksum" |});
     (MkParameter false Directionless
          (TypTypeName (BareName {| stags := tt; str := "HashAlgorithm" |}))
          None {| stags := tt; str := "algo" |})].

Definition resubmit := DeclExternFunction tt TypVoid
    {| stags := tt; str := "resubmit" |} [{| stags := tt; str := "T18" |}]
    [(MkParameter false In
          (TypTypeName (BareName {| stags := tt; str := "T18" |})) None
          {| stags := tt; str := "data" |})].

Definition recirculate := DeclExternFunction tt TypVoid
    {| stags := tt; str := "recirculate" |} [{| stags := tt; str := "T19" |}]
    [(MkParameter false In
          (TypTypeName (BareName {| stags := tt; str := "T19" |})) None
          {| stags := tt; str := "data" |})].

Definition clone := DeclExternFunction tt TypVoid
    {| stags := tt; str := "clone" |} nil
    [(MkParameter false In
          (TypTypeName (BareName {| stags := tt; str := "CloneType" |})) 
          None {| stags := tt; str := "type" |});
     (MkParameter false In (TypBit 32) None
          {| stags := tt; str := "session" |})].

Definition clone3 := DeclExternFunction tt TypVoid
    {| stags := tt; str := "clone3" |} [{| stags := tt; str := "T20" |}]
    [(MkParameter false In
          (TypTypeName (BareName {| stags := tt; str := "CloneType" |})) 
          None {| stags := tt; str := "type" |});
     (MkParameter false In (TypBit 32) None
          {| stags := tt; str := "session" |});
     (MkParameter false In
          (TypTypeName (BareName {| stags := tt; str := "T20" |})) None
          {| stags := tt; str := "data" |})].

Definition truncate := DeclExternFunction tt TypVoid
    {| stags := tt; str := "truncate" |} nil
    [(MkParameter false In (TypBit 32) None
          {| stags := tt; str := "length" |})].

Definition assert := DeclExternFunction tt TypVoid
    {| stags := tt; str := "assert" |} nil
    [(MkParameter false In TypBool None {| stags := tt; str := "check" |})].

Definition assume := DeclExternFunction tt TypVoid
    {| stags := tt; str := "assume" |} nil
    [(MkParameter false In TypBool None {| stags := tt; str := "check" |})].

Definition Parser := DeclParserType tt {| stags := tt; str := "Parser" |}
    [{| stags := tt; str := "H" |}; {| stags := tt; str := "M21" |}]
    [(MkParameter false Directionless
          (TypTypeName (BareName {| stags := tt; str := "packet_in" |})) 
          None {| stags := tt; str := "b" |});
     (MkParameter false Out
          (TypTypeName (BareName {| stags := tt; str := "H" |})) None
          {| stags := tt; str := "parsedHdr" |});
     (MkParameter false InOut
          (TypTypeName (BareName {| stags := tt; str := "M21" |})) None
          {| stags := tt; str := "meta" |});
     (MkParameter false InOut
          (TypTypeName
           (BareName {| stags := tt; str := "standard_metadata_t" |})) 
          None {| stags := tt; str := "standard_metadata" |})].

Definition VerifyChecksum := DeclControlType tt
    {| stags := tt; str := "VerifyChecksum" |}
    [{| stags := tt; str := "H22" |}; {| stags := tt; str := "M23" |}]
    [(MkParameter false InOut
          (TypTypeName (BareName {| stags := tt; str := "H22" |})) None
          {| stags := tt; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName (BareName {| stags := tt; str := "M23" |})) None
          {| stags := tt; str := "meta" |})].

Definition Ingress := DeclControlType tt {| stags := tt; str := "Ingress" |}
    [{| stags := tt; str := "H24" |}; {| stags := tt; str := "M25" |}]
    [(MkParameter false InOut
          (TypTypeName (BareName {| stags := tt; str := "H24" |})) None
          {| stags := tt; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName (BareName {| stags := tt; str := "M25" |})) None
          {| stags := tt; str := "meta" |});
     (MkParameter false InOut
          (TypTypeName
           (BareName {| stags := tt; str := "standard_metadata_t" |})) 
          None {| stags := tt; str := "standard_metadata" |})].

Definition Egress := DeclControlType tt {| stags := tt; str := "Egress" |}
    [{| stags := tt; str := "H26" |}; {| stags := tt; str := "M27" |}]
    [(MkParameter false InOut
          (TypTypeName (BareName {| stags := tt; str := "H26" |})) None
          {| stags := tt; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName (BareName {| stags := tt; str := "M27" |})) None
          {| stags := tt; str := "meta" |});
     (MkParameter false InOut
          (TypTypeName
           (BareName {| stags := tt; str := "standard_metadata_t" |})) 
          None {| stags := tt; str := "standard_metadata" |})].

Definition ComputeChecksum := DeclControlType tt
    {| stags := tt; str := "ComputeChecksum" |}
    [{| stags := tt; str := "H28" |}; {| stags := tt; str := "M29" |}]
    [(MkParameter false InOut
          (TypTypeName (BareName {| stags := tt; str := "H28" |})) None
          {| stags := tt; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName (BareName {| stags := tt; str := "M29" |})) None
          {| stags := tt; str := "meta" |})].

Definition Deparser := DeclControlType tt
    {| stags := tt; str := "Deparser" |} [{| stags := tt; str := "H30" |}]
    [(MkParameter false Directionless
          (TypTypeName (BareName {| stags := tt; str := "packet_out" |}))
          None {| stags := tt; str := "b" |});
     (MkParameter false In
          (TypTypeName (BareName {| stags := tt; str := "H30" |})) None
          {| stags := tt; str := "hdr" |})].

Definition V1Switch := DeclPackageType tt
    {| stags := tt; str := "V1Switch" |}
    [{| stags := tt; str := "H31" |}; {| stags := tt; str := "M32" |}]
    [(MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName (BareName {| stags := tt; str := "Parser" |}))
               [(TypTypeName (BareName {| stags := tt; str := "H31" |}));
                (TypTypeName (BareName {| stags := tt; str := "M32" |}))])
          None {| stags := tt; str := "p" |});
     (MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName
                (BareName {| stags := tt; str := "VerifyChecksum" |}))
               [(TypTypeName (BareName {| stags := tt; str := "H31" |}));
                (TypTypeName (BareName {| stags := tt; str := "M32" |}))])
          None {| stags := tt; str := "vr" |});
     (MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName (BareName {| stags := tt; str := "Ingress" |}))
               [(TypTypeName (BareName {| stags := tt; str := "H31" |}));
                (TypTypeName (BareName {| stags := tt; str := "M32" |}))])
          None {| stags := tt; str := "ig" |});
     (MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName (BareName {| stags := tt; str := "Egress" |}))
               [(TypTypeName (BareName {| stags := tt; str := "H31" |}));
                (TypTypeName (BareName {| stags := tt; str := "M32" |}))])
          None {| stags := tt; str := "eg" |});
     (MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName
                (BareName {| stags := tt; str := "ComputeChecksum" |}))
               [(TypTypeName (BareName {| stags := tt; str := "H31" |}));
                (TypTypeName (BareName {| stags := tt; str := "M32" |}))])
          None {| stags := tt; str := "ck" |});
     (MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName (BareName {| stags := tt; str := "Deparser" |}))
               [(TypTypeName (BareName {| stags := tt; str := "H31" |}))])
          None {| stags := tt; str := "dep" |})].

Definition egressSpec_t := DeclTypeDef tt
    {| stags := tt; str := "egressSpec_t" |} (inl (TypBit 9)).

Definition myHeader_t := DeclHeader tt {| stags := tt; str := "myHeader_t" |}
    [(MkDeclarationField tt (TypBit 1) {| stags := tt; str := "firstBit" |});
     (MkDeclarationField tt (TypBit 7) {| stags := tt; str := "padding" |})].

Definition metadata := DeclStruct tt {| stags := tt; str := "metadata" |}
    nil.

Definition headers := DeclStruct tt {| stags := tt; str := "headers" |}
    [(MkDeclarationField tt
          (TypHeader
           [(MkFieldType {| stags := tt; str := "firstBit" |} (TypBit 1));
            (MkFieldType {| stags := tt; str := "padding" |} (TypBit 7))])
          {| stags := tt; str := "myHeader" |})].

Definition MyParser := DeclParser tt {| stags := tt; str := "MyParser" |} nil
    [(MkParameter false Directionless
          (TypTypeName (BareName {| stags := tt; str := "packet_in" |})) 
          None {| stags := tt; str := "packet" |});
     (MkParameter false Out
          (TypTypeName (BareName {| stags := tt; str := "headers" |})) 
          None {| stags := tt; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName (BareName {| stags := tt; str := "metadata" |})) 
          None {| stags := tt; str := "meta" |});
     (MkParameter false InOut
          (TypTypeName
           (BareName {| stags := tt; str := "standard_metadata_t" |})) 
          None {| stags := tt; str := "standard_metadata" |})] nil nil
    [(MkParserState tt {| stags := tt; str := "start" |}
          [(MkStatement tt
                (StatMethodCall
                     (MkExpression tt
                          (ExpExpressionMember
                               (MkExpression tt
                                    (ExpName
                                     (BareName
                                      {| stags := tt; str := "packet" |}))
                                    (TypTypeName
                                     (BareName
                                      {| stags := tt; str := "packet_in" |}))
                                    Directionless)
                               {| stags := tt; str := "extract" |})
                          (TypFunction
                           (MkFunctionType [{| stags := tt; str := "T" |}]
                                [(MkParameter false Out
                                      (TypTypeName
                                       (BareName
                                        {| stags := tt; str := "T" |})) 
                                      None {| stags := tt; str := "hdr" |})]
                                FunExtern TypVoid)) Directionless)
                     [(TypHeader
                       [(MkFieldType {| stags := tt; str := "firstBit" |}
                             (TypBit 1));
                        (MkFieldType {| stags := tt; str := "padding" |}
                             (TypBit 7))])]
                     [(Some
                       (MkExpression tt
                            (ExpExpressionMember
                                 (MkExpression tt
                                      (ExpName
                                       (BareName
                                        {| stags := tt; str := "hdr" |}))
                                      (TypTypeName
                                       (BareName
                                        {| stags := tt; str := "headers" |}))
                                      Out)
                                 {| stags := tt; str := "myHeader" |})
                            (TypHeader
                             [(MkFieldType
                                   {| stags := tt; str := "firstBit" |}
                                   (TypBit 1));
                              (MkFieldType
                                   {| stags := tt; str := "padding" |}
                                   (TypBit 7))]) Directionless))]) StmUnit)]
          (ParserDirect tt {| stags := tt; str := "accept" |}))].

Definition MyIngress := DeclControl tt {| stags := tt; str := "MyIngress" |}
    nil
    [(MkParameter false InOut
          (TypTypeName (BareName {| stags := tt; str := "headers" |})) 
          None {| stags := tt; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName (BareName {| stags := tt; str := "metadata" |})) 
          None {| stags := tt; str := "meta" |});
     (MkParameter false InOut
          (TypTypeName
           (BareName {| stags := tt; str := "standard_metadata_t" |})) 
          None {| stags := tt; str := "standard_metadata" |})] nil
    [(DeclInstantiation tt
          (TypSpecializedType
               (TypTypeName (BareName {| stags := tt; str := "counter" |}))
               nil)
          [(MkExpression tt
                (ExpCast (TypBit 32)
                     (MkExpression tt
                          (ExpInt
                           {| itags := tt; value := 2;
                              width_signed := None |}) TypInteger
                          Directionless)) (TypBit 32) Directionless);
           (MkExpression tt
                (ExpTypeMember
                     (BareName {| stags := tt; str := "CounterType" |})
                     {| stags := tt; str := "packets_and_bytes" |})
                (TypEnum {| stags := tt; str := "CounterType" |} None
                     [{| stags := tt; str := "packets" |};
                      {| stags := tt; str := "bytes" |};
                      {| stags := tt; str := "packets_and_bytes" |}])
                Directionless)] {| stags := tt; str := "myCounter" |} 
          None);
     (DeclAction tt {| stags := tt; str := "drop" |} nil nil
          (BlockCons
               (MkStatement tt
                    (StatMethodCall
                         (MkExpression tt
                              (ExpName
                               (BareName
                                {| stags := tt; str := "mark_to_drop" |}))
                              (TypFunction
                               (MkFunctionType nil
                                    [(MkParameter false InOut
                                          (TypTypeName
                                           (BareName
                                            {| stags := tt;
                                               str := "standard_metadata_t" |}))
                                          None
                                          {| stags := tt;
                                             str := "standard_metadata" |})]
                                    FunExtern TypVoid)) Directionless) nil
                         [(Some
                           (MkExpression tt
                                (ExpName
                                 (BareName
                                  {| stags := tt;
                                     str := "standard_metadata" |}))
                                (TypTypeName
                                 (BareName
                                  {| stags := tt;
                                     str := "standard_metadata_t" |})) InOut))])
                    StmUnit)
               (BlockCons
                    (MkStatement tt
                         (StatMethodCall
                              (MkExpression tt
                                   (ExpExpressionMember
                                        (MkExpression tt
                                             (ExpName
                                              (BareName
                                               {| stags := tt;
                                                  str := "myCounter" |}))
                                             (TypExtern
                                              {| stags := tt;
                                                 str := "counter" |})
                                             Directionless)
                                        {| stags := tt; str := "count" |})
                                   (TypFunction
                                    (MkFunctionType nil
                                         [(MkParameter false In (TypBit 32)
                                               None
                                               {| stags := tt;
                                                  str := "index" |})]
                                         FunExtern TypVoid)) Directionless)
                              nil
                              [(Some
                                (MkExpression tt
                                     (ExpCast (TypBit 32)
                                          (MkExpression tt
                                               (ExpExpressionMember
                                                    (MkExpression tt
                                                         (ExpExpressionMember
                                                              (MkExpression
                                                                   tt
                                                                   (ExpName
                                                                    (
                                                                    BareName
                                                                    {| 
                                                                    stags := tt;
                                                                    str := "hdr" |}))
                                                                   (TypTypeName
                                                                    (
                                                                    BareName
                                                                    {| 
                                                                    stags := tt;
                                                                    str := "headers" |}))
                                                                   InOut)
                                                              {| stags := tt;
                                                                 str := "myHeader" |})
                                                         (TypHeader
                                                          [(MkFieldType
                                                                {| stags := tt;
                                                                   str := "firstBit" |}
                                                                (TypBit 1));
                                                           (MkFieldType
                                                                {| stags := tt;
                                                                   str := "padding" |}
                                                                (TypBit 7))])
                                                         Directionless)
                                                    {| stags := tt;
                                                       str := "firstBit" |})
                                               (TypBit 1) Directionless))
                                     (TypBit 32) Directionless))]) StmUnit)
                    (BlockEmpty tt))));
     (DeclAction tt {| stags := tt; str := "do_forward" |} nil
          [(MkParameter false Directionless
                (TypTypeName
                 (BareName {| stags := tt; str := "egressSpec_t" |})) 
                None {| stags := tt; str := "port" |})]
          (BlockCons
               (MkStatement tt
                    (StatAssignment
                         (MkExpression tt
                              (ExpExpressionMember
                                   (MkExpression tt
                                        (ExpName
                                         (BareName
                                          {| stags := tt;
                                             str := "standard_metadata" |}))
                                        (TypTypeName
                                         (BareName
                                          {| stags := tt;
                                             str := "standard_metadata_t" |}))
                                        InOut)
                                   {| stags := tt; str := "egress_spec" |})
                              (TypBit 9) Directionless)
                         (MkExpression tt
                              (ExpName
                               (BareName {| stags := tt; str := "port" |}))
                              (TypTypeName
                               (BareName
                                {| stags := tt; str := "egressSpec_t" |}))
                              Directionless)) StmUnit)
               (BlockCons
                    (MkStatement tt
                         (StatMethodCall
                              (MkExpression tt
                                   (ExpExpressionMember
                                        (MkExpression tt
                                             (ExpName
                                              (BareName
                                               {| stags := tt;
                                                  str := "myCounter" |}))
                                             (TypExtern
                                              {| stags := tt;
                                                 str := "counter" |})
                                             Directionless)
                                        {| stags := tt; str := "count" |})
                                   (TypFunction
                                    (MkFunctionType nil
                                         [(MkParameter false In (TypBit 32)
                                               None
                                               {| stags := tt;
                                                  str := "index" |})]
                                         FunExtern TypVoid)) Directionless)
                              nil
                              [(Some
                                (MkExpression tt
                                     (ExpCast (TypBit 32)
                                          (MkExpression tt
                                               (ExpExpressionMember
                                                    (MkExpression tt
                                                         (ExpExpressionMember
                                                              (MkExpression
                                                                   tt
                                                                   (ExpName
                                                                    (
                                                                    BareName
                                                                    {| 
                                                                    stags := tt;
                                                                    str := "hdr" |}))
                                                                   (TypTypeName
                                                                    (
                                                                    BareName
                                                                    {| 
                                                                    stags := tt;
                                                                    str := "headers" |}))
                                                                   InOut)
                                                              {| stags := tt;
                                                                 str := "myHeader" |})
                                                         (TypHeader
                                                          [(MkFieldType
                                                                {| stags := tt;
                                                                   str := "firstBit" |}
                                                                (TypBit 1));
                                                           (MkFieldType
                                                                {| stags := tt;
                                                                   str := "padding" |}
                                                                (TypBit 7))])
                                                         Directionless)
                                                    {| stags := tt;
                                                       str := "firstBit" |})
                                               (TypBit 1) Directionless))
                                     (TypBit 32) Directionless))]) StmUnit)
                    (BlockEmpty tt))));
     (DeclTable tt {| stags := tt; str := "forward" |}
          [(MkTableKey tt
                (MkExpression tt
                     (ExpExpressionMember
                          (MkExpression tt
                               (ExpExpressionMember
                                    (MkExpression tt
                                         (ExpName
                                          (BareName
                                           {| stags := tt; str := "hdr" |}))
                                         (TypTypeName
                                          (BareName
                                           {| stags := tt;
                                              str := "headers" |})) InOut)
                                    {| stags := tt; str := "myHeader" |})
                               (TypHeader
                                [(MkFieldType
                                      {| stags := tt; str := "firstBit" |}
                                      (TypBit 1));
                                 (MkFieldType
                                      {| stags := tt; str := "padding" |}
                                      (TypBit 7))]) Directionless)
                          {| stags := tt; str := "firstBit" |}) (TypBit 1)
                     Directionless) {| stags := tt; str := "exact" |})]
          [(MkTableActionRef tt
                (MkTablePreActionRef
                     (BareName {| stags := tt; str := "do_forward" |}) nil)
                (TypAction nil
                     [(MkParameter false Directionless
                           (TypTypeName
                            (BareName
                             {| stags := tt; str := "egressSpec_t" |})) 
                           None {| stags := tt; str := "port" |})]));
           (MkTableActionRef tt
                (MkTablePreActionRef
                     (BareName {| stags := tt; str := "drop" |}) nil)
                (TypAction nil nil))] None
          (Some
           (MkTableActionRef tt
                (MkTablePreActionRef
                     (BareName {| stags := tt; str := "drop" |}) nil)
                TypVoid))
          (Some {| itags := tt; value := 2; width_signed := None |}) nil)]
    (BlockCons
         (MkStatement tt
              (StatConditional
                   (MkExpression tt
                        (ExpFunctionCall
                             (MkExpression tt
                                  (ExpExpressionMember
                                       (MkExpression tt
                                            (ExpExpressionMember
                                                 (MkExpression tt
                                                      (ExpName
                                                       (BareName
                                                        {| stags := tt;
                                                           str := "hdr" |}))
                                                      (TypTypeName
                                                       (BareName
                                                        {| stags := tt;
                                                           str := "headers" |}))
                                                      InOut)
                                                 {| stags := tt;
                                                    str := "myHeader" |})
                                            (TypHeader
                                             [(MkFieldType
                                                   {| stags := tt;
                                                      str := "firstBit" |}
                                                   (TypBit 1));
                                              (MkFieldType
                                                   {| stags := tt;
                                                      str := "padding" |}
                                                   (TypBit 7))])
                                            Directionless)
                                       {| stags := tt; str := "isValid" |})
                                  (TypFunction
                                   (MkFunctionType nil nil FunBuiltin
                                        TypBool)) Directionless) nil nil)
                        TypBool Directionless)
                   (MkStatement tt
                        (StatBlock
                         (BlockCons
                              (MkStatement tt
                                   (StatMethodCall
                                        (MkExpression tt
                                             (ExpExpressionMember
                                                  (MkExpression tt
                                                       (ExpName
                                                        (BareName
                                                         {| stags := tt;
                                                            str := "forward" |}))
                                                       (TypTable
                                                        {| stags := tt;
                                                           str := "apply_result_forward" |})
                                                       Directionless)
                                                  {| stags := tt;
                                                     str := "apply" |})
                                             (TypFunction
                                              (MkFunctionType nil nil
                                                   FunTable
                                                   (TypTypeName
                                                    (BareName
                                                     {| stags := tt;
                                                        str := "apply_result_forward" |}))))
                                             Directionless) nil nil) StmUnit)
                              (BlockEmpty tt))) StmUnit) None) StmUnit)
         (BlockEmpty tt)).

Definition MyEgress := DeclControl tt {| stags := tt; str := "MyEgress" |}
    nil
    [(MkParameter false InOut
          (TypTypeName (BareName {| stags := tt; str := "headers" |})) 
          None {| stags := tt; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName (BareName {| stags := tt; str := "metadata" |})) 
          None {| stags := tt; str := "meta" |});
     (MkParameter false InOut
          (TypTypeName
           (BareName {| stags := tt; str := "standard_metadata_t" |})) 
          None {| stags := tt; str := "standard_metadata" |})] nil nil
    (BlockEmpty tt).

Definition MyDeparser := DeclControl tt
    {| stags := tt; str := "MyDeparser" |} nil
    [(MkParameter false Directionless
          (TypTypeName (BareName {| stags := tt; str := "packet_out" |}))
          None {| stags := tt; str := "packet" |});
     (MkParameter false In
          (TypTypeName (BareName {| stags := tt; str := "headers" |})) 
          None {| stags := tt; str := "hdr" |})] nil nil
    (BlockCons
         (MkStatement tt
              (StatMethodCall
                   (MkExpression tt
                        (ExpExpressionMember
                             (MkExpression tt
                                  (ExpName
                                   (BareName
                                    {| stags := tt; str := "packet" |}))
                                  (TypTypeName
                                   (BareName
                                    {| stags := tt; str := "packet_out" |}))
                                  Directionless)
                             {| stags := tt; str := "emit" |})
                        (TypFunction
                         (MkFunctionType [{| stags := tt; str := "T2" |}]
                              [(MkParameter false In
                                    (TypTypeName
                                     (BareName
                                      {| stags := tt; str := "T2" |})) 
                                    None {| stags := tt; str := "hdr" |})]
                              FunExtern TypVoid)) Directionless)
                   [(TypHeader
                     [(MkFieldType {| stags := tt; str := "firstBit" |}
                           (TypBit 1));
                      (MkFieldType {| stags := tt; str := "padding" |}
                           (TypBit 7))])]
                   [(Some
                     (MkExpression tt
                          (ExpExpressionMember
                               (MkExpression tt
                                    (ExpName
                                     (BareName
                                      {| stags := tt; str := "hdr" |}))
                                    (TypTypeName
                                     (BareName
                                      {| stags := tt; str := "headers" |}))
                                    In) {| stags := tt; str := "myHeader" |})
                          (TypHeader
                           [(MkFieldType {| stags := tt; str := "firstBit" |}
                                 (TypBit 1));
                            (MkFieldType {| stags := tt; str := "padding" |}
                                 (TypBit 7))]) Directionless))]) StmUnit)
         (BlockEmpty tt)).

Definition MyVerifyChecksum := DeclControl tt
    {| stags := tt; str := "MyVerifyChecksum" |} nil
    [(MkParameter false InOut
          (TypTypeName (BareName {| stags := tt; str := "headers" |})) 
          None {| stags := tt; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName (BareName {| stags := tt; str := "metadata" |})) 
          None {| stags := tt; str := "meta" |})] nil nil (BlockEmpty tt).

Definition MyComputeChecksum := DeclControl tt
    {| stags := tt; str := "MyComputeChecksum" |} nil
    [(MkParameter false InOut
          (TypTypeName (BareName {| stags := tt; str := "headers" |})) 
          None {| stags := tt; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName (BareName {| stags := tt; str := "metadata" |})) 
          None {| stags := tt; str := "meta" |})] nil nil (BlockEmpty tt).

Definition main := DeclInstantiation tt
    (TypSpecializedType
         (TypTypeName (BareName {| stags := tt; str := "V1Switch" |})) nil)
    [(MkExpression tt
          (ExpNamelessInstantiation
               (TypSpecializedType
                    (TypTypeName
                     (BareName {| stags := tt; str := "MyParser" |})) nil)
               nil)
          (TypParser
           (MkControlType nil
                [(MkParameter false Directionless
                      (TypExtern {| stags := tt; str := "packet_in" |}) 
                      None {| stags := tt; str := "packet" |});
                 (MkParameter false Out
                      (TypStruct
                       [(MkFieldType {| stags := tt; str := "myHeader" |}
                             (TypHeader
                              [(MkFieldType
                                    {| stags := tt; str := "firstBit" |}
                                    (TypBit 1));
                               (MkFieldType
                                    {| stags := tt; str := "padding" |}
                                    (TypBit 7))]))]) None
                      {| stags := tt; str := "hdr" |});
                 (MkParameter false InOut (TypStruct nil) None
                      {| stags := tt; str := "meta" |});
                 (MkParameter false InOut
                      (TypStruct
                       [(MkFieldType {| stags := tt; str := "ingress_port" |}
                             (TypBit 9));
                        (MkFieldType {| stags := tt; str := "egress_spec" |}
                             (TypBit 9));
                        (MkFieldType {| stags := tt; str := "egress_port" |}
                             (TypBit 9));
                        (MkFieldType
                             {| stags := tt; str := "instance_type" |}
                             (TypBit 32));
                        (MkFieldType
                             {| stags := tt; str := "packet_length" |}
                             (TypBit 32));
                        (MkFieldType
                             {| stags := tt; str := "enq_timestamp" |}
                             (TypBit 32));
                        (MkFieldType {| stags := tt; str := "enq_qdepth" |}
                             (TypBit 19));
                        (MkFieldType
                             {| stags := tt; str := "deq_timedelta" |}
                             (TypBit 32));
                        (MkFieldType {| stags := tt; str := "deq_qdepth" |}
                             (TypBit 19));
                        (MkFieldType
                             {| stags := tt;
                                str := "ingress_global_timestamp" |}
                             (TypBit 48));
                        (MkFieldType
                             {| stags := tt;
                                str := "egress_global_timestamp" |}
                             (TypBit 48));
                        (MkFieldType {| stags := tt; str := "mcast_grp" |}
                             (TypBit 16));
                        (MkFieldType {| stags := tt; str := "egress_rid" |}
                             (TypBit 16));
                        (MkFieldType
                             {| stags := tt; str := "checksum_error" |}
                             (TypBit 1));
                        (MkFieldType {| stags := tt; str := "parser_error" |}
                             TypError);
                        (MkFieldType {| stags := tt; str := "priority" |}
                             (TypBit 3))]) None
                      {| stags := tt; str := "standard_metadata" |})]))
          Directionless);
     (MkExpression tt
          (ExpNamelessInstantiation
               (TypSpecializedType
                    (TypTypeName
                     (BareName {| stags := tt; str := "MyVerifyChecksum" |}))
                    nil) nil)
          (TypControl
           (MkControlType nil
                [(MkParameter false InOut
                      (TypStruct
                       [(MkFieldType {| stags := tt; str := "myHeader" |}
                             (TypHeader
                              [(MkFieldType
                                    {| stags := tt; str := "firstBit" |}
                                    (TypBit 1));
                               (MkFieldType
                                    {| stags := tt; str := "padding" |}
                                    (TypBit 7))]))]) None
                      {| stags := tt; str := "hdr" |});
                 (MkParameter false InOut (TypStruct nil) None
                      {| stags := tt; str := "meta" |})])) Directionless);
     (MkExpression tt
          (ExpNamelessInstantiation
               (TypSpecializedType
                    (TypTypeName
                     (BareName {| stags := tt; str := "MyIngress" |})) nil)
               nil)
          (TypControl
           (MkControlType nil
                [(MkParameter false InOut
                      (TypStruct
                       [(MkFieldType {| stags := tt; str := "myHeader" |}
                             (TypHeader
                              [(MkFieldType
                                    {| stags := tt; str := "firstBit" |}
                                    (TypBit 1));
                               (MkFieldType
                                    {| stags := tt; str := "padding" |}
                                    (TypBit 7))]))]) None
                      {| stags := tt; str := "hdr" |});
                 (MkParameter false InOut (TypStruct nil) None
                      {| stags := tt; str := "meta" |});
                 (MkParameter false InOut
                      (TypStruct
                       [(MkFieldType {| stags := tt; str := "ingress_port" |}
                             (TypBit 9));
                        (MkFieldType {| stags := tt; str := "egress_spec" |}
                             (TypBit 9));
                        (MkFieldType {| stags := tt; str := "egress_port" |}
                             (TypBit 9));
                        (MkFieldType
                             {| stags := tt; str := "instance_type" |}
                             (TypBit 32));
                        (MkFieldType
                             {| stags := tt; str := "packet_length" |}
                             (TypBit 32));
                        (MkFieldType
                             {| stags := tt; str := "enq_timestamp" |}
                             (TypBit 32));
                        (MkFieldType {| stags := tt; str := "enq_qdepth" |}
                             (TypBit 19));
                        (MkFieldType
                             {| stags := tt; str := "deq_timedelta" |}
                             (TypBit 32));
                        (MkFieldType {| stags := tt; str := "deq_qdepth" |}
                             (TypBit 19));
                        (MkFieldType
                             {| stags := tt;
                                str := "ingress_global_timestamp" |}
                             (TypBit 48));
                        (MkFieldType
                             {| stags := tt;
                                str := "egress_global_timestamp" |}
                             (TypBit 48));
                        (MkFieldType {| stags := tt; str := "mcast_grp" |}
                             (TypBit 16));
                        (MkFieldType {| stags := tt; str := "egress_rid" |}
                             (TypBit 16));
                        (MkFieldType
                             {| stags := tt; str := "checksum_error" |}
                             (TypBit 1));
                        (MkFieldType {| stags := tt; str := "parser_error" |}
                             TypError);
                        (MkFieldType {| stags := tt; str := "priority" |}
                             (TypBit 3))]) None
                      {| stags := tt; str := "standard_metadata" |})]))
          Directionless);
     (MkExpression tt
          (ExpNamelessInstantiation
               (TypSpecializedType
                    (TypTypeName
                     (BareName {| stags := tt; str := "MyEgress" |})) nil)
               nil)
          (TypControl
           (MkControlType nil
                [(MkParameter false InOut
                      (TypStruct
                       [(MkFieldType {| stags := tt; str := "myHeader" |}
                             (TypHeader
                              [(MkFieldType
                                    {| stags := tt; str := "firstBit" |}
                                    (TypBit 1));
                               (MkFieldType
                                    {| stags := tt; str := "padding" |}
                                    (TypBit 7))]))]) None
                      {| stags := tt; str := "hdr" |});
                 (MkParameter false InOut (TypStruct nil) None
                      {| stags := tt; str := "meta" |});
                 (MkParameter false InOut
                      (TypStruct
                       [(MkFieldType {| stags := tt; str := "ingress_port" |}
                             (TypBit 9));
                        (MkFieldType {| stags := tt; str := "egress_spec" |}
                             (TypBit 9));
                        (MkFieldType {| stags := tt; str := "egress_port" |}
                             (TypBit 9));
                        (MkFieldType
                             {| stags := tt; str := "instance_type" |}
                             (TypBit 32));
                        (MkFieldType
                             {| stags := tt; str := "packet_length" |}
                             (TypBit 32));
                        (MkFieldType
                             {| stags := tt; str := "enq_timestamp" |}
                             (TypBit 32));
                        (MkFieldType {| stags := tt; str := "enq_qdepth" |}
                             (TypBit 19));
                        (MkFieldType
                             {| stags := tt; str := "deq_timedelta" |}
                             (TypBit 32));
                        (MkFieldType {| stags := tt; str := "deq_qdepth" |}
                             (TypBit 19));
                        (MkFieldType
                             {| stags := tt;
                                str := "ingress_global_timestamp" |}
                             (TypBit 48));
                        (MkFieldType
                             {| stags := tt;
                                str := "egress_global_timestamp" |}
                             (TypBit 48));
                        (MkFieldType {| stags := tt; str := "mcast_grp" |}
                             (TypBit 16));
                        (MkFieldType {| stags := tt; str := "egress_rid" |}
                             (TypBit 16));
                        (MkFieldType
                             {| stags := tt; str := "checksum_error" |}
                             (TypBit 1));
                        (MkFieldType {| stags := tt; str := "parser_error" |}
                             TypError);
                        (MkFieldType {| stags := tt; str := "priority" |}
                             (TypBit 3))]) None
                      {| stags := tt; str := "standard_metadata" |})]))
          Directionless);
     (MkExpression tt
          (ExpNamelessInstantiation
               (TypSpecializedType
                    (TypTypeName
                     (BareName {| stags := tt; str := "MyComputeChecksum" |}))
                    nil) nil)
          (TypControl
           (MkControlType nil
                [(MkParameter false InOut
                      (TypStruct
                       [(MkFieldType {| stags := tt; str := "myHeader" |}
                             (TypHeader
                              [(MkFieldType
                                    {| stags := tt; str := "firstBit" |}
                                    (TypBit 1));
                               (MkFieldType
                                    {| stags := tt; str := "padding" |}
                                    (TypBit 7))]))]) None
                      {| stags := tt; str := "hdr" |});
                 (MkParameter false InOut (TypStruct nil) None
                      {| stags := tt; str := "meta" |})])) Directionless);
     (MkExpression tt
          (ExpNamelessInstantiation
               (TypSpecializedType
                    (TypTypeName
                     (BareName {| stags := tt; str := "MyDeparser" |})) nil)
               nil)
          (TypControl
           (MkControlType nil
                [(MkParameter false Directionless
                      (TypExtern {| stags := tt; str := "packet_out" |}) 
                      None {| stags := tt; str := "packet" |});
                 (MkParameter false In
                      (TypStruct
                       [(MkFieldType {| stags := tt; str := "myHeader" |}
                             (TypHeader
                              [(MkFieldType
                                    {| stags := tt; str := "firstBit" |}
                                    (TypBit 1));
                               (MkFieldType
                                    {| stags := tt; str := "padding" |}
                                    (TypBit 7))]))]) None
                      {| stags := tt; str := "hdr" |})])) Directionless)]
    {| stags := tt; str := "main" |} None.

Definition program := [decl1; packet_in; packet_out; verify; NoAction; decl2;
                       decl3; standard_metadata_t; CounterType; MeterType;
                       counter; direct_counter; meter; direct_meter;
                       register; action_profile; random; digest;
                       HashAlgorithm; mark_to_drop; mark_to_drop_2; hash;
                       action_selector; CloneType; Checksum16;
                       verify_checksum; update_checksum;
                       verify_checksum_with_payload;
                       update_checksum_with_payload; resubmit; recirculate;
                       clone; clone3; truncate; assert; assume; Parser;
                       VerifyChecksum; Ingress; Egress; ComputeChecksum;
                       Deparser; V1Switch; egressSpec_t; myHeader_t;
                       metadata; headers; MyParser; MyIngress; MyEgress;
                       MyDeparser; MyVerifyChecksum; MyComputeChecksum; main].


