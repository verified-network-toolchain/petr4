Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Strings.String.

Require Import Petr4.P4String.
Require Import Petr4.Syntax.
Require Import Petr4.Typed.

Open Scope string_scope.

Import ListNotations.

Definition decl1 := DeclError tt
    [{| tags := tt; str := "NoError" |};
     {| tags := tt; str := "PacketTooShort" |};
     {| tags := tt; str := "NoMatch" |};
     {| tags := tt; str := "StackOutOfBounds" |};
     {| tags := tt; str := "HeaderTooShort" |};
     {| tags := tt; str := "ParserTimeout" |};
     {| tags := tt; str := "ParserInvalidArgument" |}].

Definition packet_in := DeclExternObject tt
    {| tags := tt; str := "packet_in" |} nil
    [(ProtoMethod tt (TypBit 32) {| tags := tt; str := "length" |} nil nil);
     (ProtoMethod tt TypVoid {| tags := tt; str := "advance" |} nil
          [(MkParameter false In (TypBit 32) None
                {| tags := tt; str := "sizeInBits" |})]);
     (ProtoMethod tt (TypTypeName (BareName {| tags := tt; str := "T1" |}))
          {| tags := tt; str := "lookahead" |}
          [{| tags := tt; str := "T1" |}] nil);
     (ProtoMethod tt TypVoid {| tags := tt; str := "extract" |}
          [{| tags := tt; str := "T0" |}]
          [(MkParameter false Out
                (TypTypeName (BareName {| tags := tt; str := "T0" |})) 
                None {| tags := tt; str := "variableSizeHeader" |});
           (MkParameter false In (TypBit 32) None
                {| tags := tt; str := "variableFieldSizeInBits" |})]);
     (ProtoMethod tt TypVoid {| tags := tt; str := "extract" |}
          [{| tags := tt; str := "T" |}]
          [(MkParameter false Out
                (TypTypeName (BareName {| tags := tt; str := "T" |})) 
                None {| tags := tt; str := "hdr" |})])].

Definition packet_out := DeclExternObject tt
    {| tags := tt; str := "packet_out" |} nil
    [(ProtoMethod tt TypVoid {| tags := tt; str := "emit" |}
          [{| tags := tt; str := "T2" |}]
          [(MkParameter false In
                (TypTypeName (BareName {| tags := tt; str := "T2" |})) 
                None {| tags := tt; str := "hdr" |})])].

Definition verify := DeclExternFunction tt TypVoid
    {| tags := tt; str := "verify" |} nil
    [(MkParameter false In TypBool None {| tags := tt; str := "check" |});
     (MkParameter false In TypError None {| tags := tt; str := "toSignal" |})].

Definition NoAction := DeclAction tt {| tags := tt; str := "NoAction" |} nil
    nil (BlockEmpty tt).

Definition decl2 := DeclMatchKind tt
    [{| tags := tt; str := "exact" |}; {| tags := tt; str := "ternary" |};
     {| tags := tt; str := "lpm" |}].

Definition decl3 := DeclMatchKind tt
    [{| tags := tt; str := "range" |}; {| tags := tt; str := "selector" |}].

Definition standard_metadata_t := DeclStruct tt
    {| tags := tt; str := "standard_metadata_t" |}
    [(MkDeclarationField tt (TypBit 9)
          {| tags := tt; str := "ingress_port" |});
     (MkDeclarationField tt (TypBit 9)
          {| tags := tt; str := "egress_spec" |});
     (MkDeclarationField tt (TypBit 9)
          {| tags := tt; str := "egress_port" |});
     (MkDeclarationField tt (TypBit 32)
          {| tags := tt; str := "instance_type" |});
     (MkDeclarationField tt (TypBit 32)
          {| tags := tt; str := "packet_length" |});
     (MkDeclarationField tt (TypBit 32)
          {| tags := tt; str := "enq_timestamp" |});
     (MkDeclarationField tt (TypBit 19)
          {| tags := tt; str := "enq_qdepth" |});
     (MkDeclarationField tt (TypBit 32)
          {| tags := tt; str := "deq_timedelta" |});
     (MkDeclarationField tt (TypBit 19)
          {| tags := tt; str := "deq_qdepth" |});
     (MkDeclarationField tt (TypBit 48)
          {| tags := tt; str := "ingress_global_timestamp" |});
     (MkDeclarationField tt (TypBit 48)
          {| tags := tt; str := "egress_global_timestamp" |});
     (MkDeclarationField tt (TypBit 16) {| tags := tt; str := "mcast_grp" |});
     (MkDeclarationField tt (TypBit 16)
          {| tags := tt; str := "egress_rid" |});
     (MkDeclarationField tt (TypBit 1)
          {| tags := tt; str := "checksum_error" |});
     (MkDeclarationField tt TypError {| tags := tt; str := "parser_error" |});
     (MkDeclarationField tt (TypBit 3) {| tags := tt; str := "priority" |})].

Definition CounterType := DeclEnum tt {| tags := tt; str := "CounterType" |}
    [{| tags := tt; str := "packets" |}; {| tags := tt; str := "bytes" |};
     {| tags := tt; str := "packets_and_bytes" |}].

Definition MeterType := DeclEnum tt {| tags := tt; str := "MeterType" |}
    [{| tags := tt; str := "packets" |}; {| tags := tt; str := "bytes" |}].

Definition counter := DeclExternObject tt {| tags := tt; str := "counter" |}
    nil
    [(ProtoConstructor tt {| tags := tt; str := "counter" |}
          [(MkParameter false Directionless (TypBit 32) None
                {| tags := tt; str := "size" |});
           (MkParameter false Directionless
                (TypTypeName
                 (BareName {| tags := tt; str := "CounterType" |})) None
                {| tags := tt; str := "type" |})]);
     (ProtoMethod tt TypVoid {| tags := tt; str := "count" |} nil
          [(MkParameter false In (TypBit 32) None
                {| tags := tt; str := "index" |})])].

Definition direct_counter := DeclExternObject tt
    {| tags := tt; str := "direct_counter" |} nil
    [(ProtoConstructor tt {| tags := tt; str := "direct_counter" |}
          [(MkParameter false Directionless
                (TypTypeName
                 (BareName {| tags := tt; str := "CounterType" |})) None
                {| tags := tt; str := "type" |})]);
     (ProtoMethod tt TypVoid {| tags := tt; str := "count" |} nil nil)].

Definition meter := DeclExternObject tt {| tags := tt; str := "meter" |} nil
    [(ProtoConstructor tt {| tags := tt; str := "meter" |}
          [(MkParameter false Directionless (TypBit 32) None
                {| tags := tt; str := "size" |});
           (MkParameter false Directionless
                (TypTypeName (BareName {| tags := tt; str := "MeterType" |}))
                None {| tags := tt; str := "type" |})]);
     (ProtoMethod tt TypVoid {| tags := tt; str := "execute_meter" |}
          [{| tags := tt; str := "T3" |}]
          [(MkParameter false In (TypBit 32) None
                {| tags := tt; str := "index" |});
           (MkParameter false Out
                (TypTypeName (BareName {| tags := tt; str := "T3" |})) 
                None {| tags := tt; str := "result" |})])].

Definition direct_meter := DeclExternObject tt
    {| tags := tt; str := "direct_meter" |} [{| tags := tt; str := "T4" |}]
    [(ProtoConstructor tt {| tags := tt; str := "direct_meter" |}
          [(MkParameter false Directionless
                (TypTypeName (BareName {| tags := tt; str := "MeterType" |}))
                None {| tags := tt; str := "type" |})]);
     (ProtoMethod tt TypVoid {| tags := tt; str := "read" |} nil
          [(MkParameter false Out
                (TypTypeName (BareName {| tags := tt; str := "T4" |})) 
                None {| tags := tt; str := "result" |})])].

Definition register := DeclExternObject tt
    {| tags := tt; str := "register" |} [{| tags := tt; str := "T5" |}]
    [(ProtoConstructor tt {| tags := tt; str := "register" |}
          [(MkParameter false Directionless (TypBit 32) None
                {| tags := tt; str := "size" |})]);
     (ProtoMethod tt TypVoid {| tags := tt; str := "write" |} nil
          [(MkParameter false In (TypBit 32) None
                {| tags := tt; str := "index" |});
           (MkParameter false In
                (TypTypeName (BareName {| tags := tt; str := "T5" |})) 
                None {| tags := tt; str := "value" |})]);
     (ProtoMethod tt TypVoid {| tags := tt; str := "read" |} nil
          [(MkParameter false Out
                (TypTypeName (BareName {| tags := tt; str := "T5" |})) 
                None {| tags := tt; str := "result" |});
           (MkParameter false In (TypBit 32) None
                {| tags := tt; str := "index" |})])].

Definition action_profile := DeclExternObject tt
    {| tags := tt; str := "action_profile" |} nil
    [(ProtoConstructor tt {| tags := tt; str := "action_profile" |}
          [(MkParameter false Directionless (TypBit 32) None
                {| tags := tt; str := "size" |})])].

Definition random := DeclExternFunction tt TypVoid
    {| tags := tt; str := "random" |} [{| tags := tt; str := "T6" |}]
    [(MkParameter false Out
          (TypTypeName (BareName {| tags := tt; str := "T6" |})) None
          {| tags := tt; str := "result" |});
     (MkParameter false In
          (TypTypeName (BareName {| tags := tt; str := "T6" |})) None
          {| tags := tt; str := "lo" |});
     (MkParameter false In
          (TypTypeName (BareName {| tags := tt; str := "T6" |})) None
          {| tags := tt; str := "hi" |})].

Definition digest := DeclExternFunction tt TypVoid
    {| tags := tt; str := "digest" |} [{| tags := tt; str := "T7" |}]
    [(MkParameter false In (TypBit 32) None
          {| tags := tt; str := "receiver" |});
     (MkParameter false In
          (TypTypeName (BareName {| tags := tt; str := "T7" |})) None
          {| tags := tt; str := "data" |})].

Definition HashAlgorithm := DeclEnum tt
    {| tags := tt; str := "HashAlgorithm" |}
    [{| tags := tt; str := "crc32" |};
     {| tags := tt; str := "crc32_custom" |};
     {| tags := tt; str := "crc16" |};
     {| tags := tt; str := "crc16_custom" |};
     {| tags := tt; str := "random" |}; {| tags := tt; str := "identity" |};
     {| tags := tt; str := "csum16" |}; {| tags := tt; str := "xor16" |}].

Definition mark_to_drop := DeclExternFunction tt TypVoid
    {| tags := tt; str := "mark_to_drop" |} nil nil.

Definition mark_to_drop_2 := DeclExternFunction tt TypVoid
    {| tags := tt; str := "mark_to_drop" |} nil
    [(MkParameter false InOut
          (TypTypeName
           (BareName {| tags := tt; str := "standard_metadata_t" |})) 
          None {| tags := tt; str := "standard_metadata" |})].

Definition hash := DeclExternFunction tt TypVoid
    {| tags := tt; str := "hash" |}
    [{| tags := tt; str := "O" |}; {| tags := tt; str := "T8" |};
     {| tags := tt; str := "D" |}; {| tags := tt; str := "M" |}]
    [(MkParameter false Out
          (TypTypeName (BareName {| tags := tt; str := "O" |})) None
          {| tags := tt; str := "result" |});
     (MkParameter false In
          (TypTypeName (BareName {| tags := tt; str := "HashAlgorithm" |}))
          None {| tags := tt; str := "algo" |});
     (MkParameter false In
          (TypTypeName (BareName {| tags := tt; str := "T8" |})) None
          {| tags := tt; str := "base" |});
     (MkParameter false In
          (TypTypeName (BareName {| tags := tt; str := "D" |})) None
          {| tags := tt; str := "data" |});
     (MkParameter false In
          (TypTypeName (BareName {| tags := tt; str := "M" |})) None
          {| tags := tt; str := "max" |})].

Definition action_selector := DeclExternObject tt
    {| tags := tt; str := "action_selector" |} nil
    [(ProtoConstructor tt {| tags := tt; str := "action_selector" |}
          [(MkParameter false Directionless
                (TypTypeName
                 (BareName {| tags := tt; str := "HashAlgorithm" |})) 
                None {| tags := tt; str := "algorithm" |});
           (MkParameter false Directionless (TypBit 32) None
                {| tags := tt; str := "size" |});
           (MkParameter false Directionless (TypBit 32) None
                {| tags := tt; str := "outputWidth" |})])].

Definition CloneType := DeclEnum tt {| tags := tt; str := "CloneType" |}
    [{| tags := tt; str := "I2E" |}; {| tags := tt; str := "E2E" |}].

Definition Checksum16 := DeclExternObject tt
    {| tags := tt; str := "Checksum16" |} nil
    [(ProtoConstructor tt {| tags := tt; str := "Checksum16" |} nil);
     (ProtoMethod tt (TypBit 16) {| tags := tt; str := "get" |}
          [{| tags := tt; str := "D9" |}]
          [(MkParameter false In
                (TypTypeName (BareName {| tags := tt; str := "D9" |})) 
                None {| tags := tt; str := "data" |})])].

Definition verify_checksum := DeclExternFunction tt TypVoid
    {| tags := tt; str := "verify_checksum" |}
    [{| tags := tt; str := "T10" |}; {| tags := tt; str := "O11" |}]
    [(MkParameter false In TypBool None {| tags := tt; str := "condition" |});
     (MkParameter false In
          (TypTypeName (BareName {| tags := tt; str := "T10" |})) None
          {| tags := tt; str := "data" |});
     (MkParameter false InOut
          (TypTypeName (BareName {| tags := tt; str := "O11" |})) None
          {| tags := tt; str := "checksum" |});
     (MkParameter false Directionless
          (TypTypeName (BareName {| tags := tt; str := "HashAlgorithm" |}))
          None {| tags := tt; str := "algo" |})].

Definition update_checksum := DeclExternFunction tt TypVoid
    {| tags := tt; str := "update_checksum" |}
    [{| tags := tt; str := "T12" |}; {| tags := tt; str := "O13" |}]
    [(MkParameter false In TypBool None {| tags := tt; str := "condition" |});
     (MkParameter false In
          (TypTypeName (BareName {| tags := tt; str := "T12" |})) None
          {| tags := tt; str := "data" |});
     (MkParameter false InOut
          (TypTypeName (BareName {| tags := tt; str := "O13" |})) None
          {| tags := tt; str := "checksum" |});
     (MkParameter false Directionless
          (TypTypeName (BareName {| tags := tt; str := "HashAlgorithm" |}))
          None {| tags := tt; str := "algo" |})].

Definition verify_checksum_with_payload := DeclExternFunction tt TypVoid
    {| tags := tt; str := "verify_checksum_with_payload" |}
    [{| tags := tt; str := "T14" |}; {| tags := tt; str := "O15" |}]
    [(MkParameter false In TypBool None {| tags := tt; str := "condition" |});
     (MkParameter false In
          (TypTypeName (BareName {| tags := tt; str := "T14" |})) None
          {| tags := tt; str := "data" |});
     (MkParameter false InOut
          (TypTypeName (BareName {| tags := tt; str := "O15" |})) None
          {| tags := tt; str := "checksum" |});
     (MkParameter false Directionless
          (TypTypeName (BareName {| tags := tt; str := "HashAlgorithm" |}))
          None {| tags := tt; str := "algo" |})].

Definition update_checksum_with_payload := DeclExternFunction tt TypVoid
    {| tags := tt; str := "update_checksum_with_payload" |}
    [{| tags := tt; str := "T16" |}; {| tags := tt; str := "O17" |}]
    [(MkParameter false In TypBool None {| tags := tt; str := "condition" |});
     (MkParameter false In
          (TypTypeName (BareName {| tags := tt; str := "T16" |})) None
          {| tags := tt; str := "data" |});
     (MkParameter false InOut
          (TypTypeName (BareName {| tags := tt; str := "O17" |})) None
          {| tags := tt; str := "checksum" |});
     (MkParameter false Directionless
          (TypTypeName (BareName {| tags := tt; str := "HashAlgorithm" |}))
          None {| tags := tt; str := "algo" |})].

Definition resubmit := DeclExternFunction tt TypVoid
    {| tags := tt; str := "resubmit" |} [{| tags := tt; str := "T18" |}]
    [(MkParameter false In
          (TypTypeName (BareName {| tags := tt; str := "T18" |})) None
          {| tags := tt; str := "data" |})].

Definition recirculate := DeclExternFunction tt TypVoid
    {| tags := tt; str := "recirculate" |} [{| tags := tt; str := "T19" |}]
    [(MkParameter false In
          (TypTypeName (BareName {| tags := tt; str := "T19" |})) None
          {| tags := tt; str := "data" |})].

Definition clone := DeclExternFunction tt TypVoid
    {| tags := tt; str := "clone" |} nil
    [(MkParameter false In
          (TypTypeName (BareName {| tags := tt; str := "CloneType" |})) 
          None {| tags := tt; str := "type" |});
     (MkParameter false In (TypBit 32) None
          {| tags := tt; str := "session" |})].

Definition clone3 := DeclExternFunction tt TypVoid
    {| tags := tt; str := "clone3" |} [{| tags := tt; str := "T20" |}]
    [(MkParameter false In
          (TypTypeName (BareName {| tags := tt; str := "CloneType" |})) 
          None {| tags := tt; str := "type" |});
     (MkParameter false In (TypBit 32) None
          {| tags := tt; str := "session" |});
     (MkParameter false In
          (TypTypeName (BareName {| tags := tt; str := "T20" |})) None
          {| tags := tt; str := "data" |})].

Definition truncate := DeclExternFunction tt TypVoid
    {| tags := tt; str := "truncate" |} nil
    [(MkParameter false In (TypBit 32) None
          {| tags := tt; str := "length" |})].

Definition assert := DeclExternFunction tt TypVoid
    {| tags := tt; str := "assert" |} nil
    [(MkParameter false In TypBool None {| tags := tt; str := "check" |})].

Definition assume := DeclExternFunction tt TypVoid
    {| tags := tt; str := "assume" |} nil
    [(MkParameter false In TypBool None {| tags := tt; str := "check" |})].

Definition Parser := DeclParserType tt {| tags := tt; str := "Parser" |}
    [{| tags := tt; str := "H" |}; {| tags := tt; str := "M21" |}]
    [(MkParameter false Directionless
          (TypTypeName (BareName {| tags := tt; str := "packet_in" |})) 
          None {| tags := tt; str := "b" |});
     (MkParameter false Out
          (TypTypeName (BareName {| tags := tt; str := "H" |})) None
          {| tags := tt; str := "parsedHdr" |});
     (MkParameter false InOut
          (TypTypeName (BareName {| tags := tt; str := "M21" |})) None
          {| tags := tt; str := "meta" |});
     (MkParameter false InOut
          (TypTypeName
           (BareName {| tags := tt; str := "standard_metadata_t" |})) 
          None {| tags := tt; str := "standard_metadata" |})].

Definition VerifyChecksum := DeclControlType tt
    {| tags := tt; str := "VerifyChecksum" |}
    [{| tags := tt; str := "H22" |}; {| tags := tt; str := "M23" |}]
    [(MkParameter false InOut
          (TypTypeName (BareName {| tags := tt; str := "H22" |})) None
          {| tags := tt; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName (BareName {| tags := tt; str := "M23" |})) None
          {| tags := tt; str := "meta" |})].

Definition Ingress := DeclControlType tt {| tags := tt; str := "Ingress" |}
    [{| tags := tt; str := "H24" |}; {| tags := tt; str := "M25" |}]
    [(MkParameter false InOut
          (TypTypeName (BareName {| tags := tt; str := "H24" |})) None
          {| tags := tt; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName (BareName {| tags := tt; str := "M25" |})) None
          {| tags := tt; str := "meta" |});
     (MkParameter false InOut
          (TypTypeName
           (BareName {| tags := tt; str := "standard_metadata_t" |})) 
          None {| tags := tt; str := "standard_metadata" |})].

Definition Egress := DeclControlType tt {| tags := tt; str := "Egress" |}
    [{| tags := tt; str := "H26" |}; {| tags := tt; str := "M27" |}]
    [(MkParameter false InOut
          (TypTypeName (BareName {| tags := tt; str := "H26" |})) None
          {| tags := tt; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName (BareName {| tags := tt; str := "M27" |})) None
          {| tags := tt; str := "meta" |});
     (MkParameter false InOut
          (TypTypeName
           (BareName {| tags := tt; str := "standard_metadata_t" |})) 
          None {| tags := tt; str := "standard_metadata" |})].

Definition ComputeChecksum := DeclControlType tt
    {| tags := tt; str := "ComputeChecksum" |}
    [{| tags := tt; str := "H28" |}; {| tags := tt; str := "M29" |}]
    [(MkParameter false InOut
          (TypTypeName (BareName {| tags := tt; str := "H28" |})) None
          {| tags := tt; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName (BareName {| tags := tt; str := "M29" |})) None
          {| tags := tt; str := "meta" |})].

Definition Deparser := DeclControlType tt {| tags := tt; str := "Deparser" |}
    [{| tags := tt; str := "H30" |}]
    [(MkParameter false Directionless
          (TypTypeName (BareName {| tags := tt; str := "packet_out" |})) 
          None {| tags := tt; str := "b" |});
     (MkParameter false In
          (TypTypeName (BareName {| tags := tt; str := "H30" |})) None
          {| tags := tt; str := "hdr" |})].

Definition V1Switch := DeclPackageType tt {| tags := tt; str := "V1Switch" |}
    [{| tags := tt; str := "H31" |}; {| tags := tt; str := "M32" |}]
    [(MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName (BareName {| tags := tt; str := "Parser" |}))
               [(TypTypeName (BareName {| tags := tt; str := "H31" |}));
                (TypTypeName (BareName {| tags := tt; str := "M32" |}))])
          None {| tags := tt; str := "p" |});
     (MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName
                (BareName {| tags := tt; str := "VerifyChecksum" |}))
               [(TypTypeName (BareName {| tags := tt; str := "H31" |}));
                (TypTypeName (BareName {| tags := tt; str := "M32" |}))])
          None {| tags := tt; str := "vr" |});
     (MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName (BareName {| tags := tt; str := "Ingress" |}))
               [(TypTypeName (BareName {| tags := tt; str := "H31" |}));
                (TypTypeName (BareName {| tags := tt; str := "M32" |}))])
          None {| tags := tt; str := "ig" |});
     (MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName (BareName {| tags := tt; str := "Egress" |}))
               [(TypTypeName (BareName {| tags := tt; str := "H31" |}));
                (TypTypeName (BareName {| tags := tt; str := "M32" |}))])
          None {| tags := tt; str := "eg" |});
     (MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName
                (BareName {| tags := tt; str := "ComputeChecksum" |}))
               [(TypTypeName (BareName {| tags := tt; str := "H31" |}));
                (TypTypeName (BareName {| tags := tt; str := "M32" |}))])
          None {| tags := tt; str := "ck" |});
     (MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName (BareName {| tags := tt; str := "Deparser" |}))
               [(TypTypeName (BareName {| tags := tt; str := "H31" |}))])
          None {| tags := tt; str := "dep" |})].

Definition egressSpec_t := DeclTypeDef tt
    {| tags := tt; str := "egressSpec_t" |} (inl (TypBit 9)).

Definition myHeader_t := DeclHeader tt {| tags := tt; str := "myHeader_t" |}
    [(MkDeclarationField tt (TypBit 1) {| tags := tt; str := "firstBit" |});
     (MkDeclarationField tt (TypBit 7) {| tags := tt; str := "padding" |})].

Definition metadata := DeclStruct tt {| tags := tt; str := "metadata" |} nil.

Definition headers := DeclStruct tt {| tags := tt; str := "headers" |}
    [(MkDeclarationField tt
          (TypHeader
           [(MkFieldType {| tags := tt; str := "firstBit" |} (TypBit 1));
            (MkFieldType {| tags := tt; str := "padding" |} (TypBit 7))])
          {| tags := tt; str := "myHeader" |})].

Definition MyParser := DeclParser tt {| tags := tt; str := "MyParser" |} nil
    [(MkParameter false Directionless
          (TypTypeName (BareName {| tags := tt; str := "packet_in" |})) 
          None {| tags := tt; str := "packet" |});
     (MkParameter false Out
          (TypTypeName (BareName {| tags := tt; str := "headers" |})) 
          None {| tags := tt; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName (BareName {| tags := tt; str := "metadata" |})) 
          None {| tags := tt; str := "meta" |});
     (MkParameter false InOut
          (TypTypeName
           (BareName {| tags := tt; str := "standard_metadata_t" |})) 
          None {| tags := tt; str := "standard_metadata" |})] nil nil
    [(MkParserState tt {| tags := tt; str := "start" |}
          [(MkStatement tt
                (StatMethodCall
                     (MkExpression tt
                          (ExpExpressionMember
                               (MkExpression tt
                                    (ExpName
                                     (BareName
                                      {| tags := tt; str := "packet" |}))
                                    (TypTypeName
                                     (BareName
                                      {| tags := tt; str := "packet_in" |}))
                                    Directionless)
                               {| tags := tt; str := "extract" |})
                          (TypFunction
                           (MkFunctionType [{| tags := tt; str := "T" |}]
                                [(MkParameter false Out
                                      (TypTypeName
                                       (BareName
                                        {| tags := tt; str := "T" |})) 
                                      None {| tags := tt; str := "hdr" |})]
                                FunExtern TypVoid)) Directionless)
                     [(TypHeader
                       [(MkFieldType {| tags := tt; str := "firstBit" |}
                             (TypBit 1));
                        (MkFieldType {| tags := tt; str := "padding" |}
                             (TypBit 7))])]
                     [(Some
                       (MkExpression tt
                            (ExpExpressionMember
                                 (MkExpression tt
                                      (ExpName
                                       (BareName
                                        {| tags := tt; str := "hdr" |}))
                                      (TypTypeName
                                       (BareName
                                        {| tags := tt; str := "headers" |}))
                                      Out)
                                 {| tags := tt; str := "myHeader" |})
                            (TypHeader
                             [(MkFieldType
                                   {| tags := tt; str := "firstBit" |}
                                   (TypBit 1));
                              (MkFieldType {| tags := tt; str := "padding" |}
                                   (TypBit 7))]) Directionless))]) StmUnit)]
          (ParserDirect tt {| tags := tt; str := "accept" |}))].

Require Import Petr4.P4Int.
Definition x := {| tags := tt; value := 2; width_signed := None |}.

Definition MyIngress := DeclControl tt {| tags := tt; str := "MyIngress" |}
    nil
    [(MkParameter false InOut
          (TypTypeName (BareName {| tags := tt; str := "headers" |})) 
          None {| tags := tt; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName (BareName {| tags := tt; str := "metadata" |})) 
          None {| tags := tt; str := "meta" |});
     (MkParameter false InOut
          (TypTypeName
           (BareName {| tags := tt; str := "standard_metadata_t" |})) 
          None {| tags := tt; str := "standard_metadata" |})] nil
    [(DeclAction tt {| tags := tt; str := "drop" |} nil nil
          (BlockCons
               (MkStatement tt
                    (StatMethodCall
                         (MkExpression tt
                              (ExpName
                               (BareName
                                {| tags := tt; str := "mark_to_drop" |}))
                              (TypFunction
                               (MkFunctionType nil
                                    [(MkParameter false InOut
                                          (TypTypeName
                                           (BareName
                                            {| tags := tt;
                                               str := "standard_metadata_t" |}))
                                          None
                                          {| tags := tt;
                                             str := "standard_metadata" |})]
                                    FunExtern TypVoid)) Directionless) nil
                         [(Some
                           (MkExpression tt
                                (ExpName
                                 (BareName
                                  {| tags := tt;
                                     str := "standard_metadata" |}))
                                (TypTypeName
                                 (BareName
                                  {| tags := tt;
                                     str := "standard_metadata_t" |})) InOut))])
                    StmUnit) (BlockEmpty tt)));
     (DeclAction tt {| tags := tt; str := "do_forward" |} nil
          [(MkParameter false Directionless
                (TypTypeName
                 (BareName {| tags := tt; str := "egressSpec_t" |})) 
                None {| tags := tt; str := "port" |})]
          (BlockCons
               (MkStatement tt
                    (StatAssignment
                         (MkExpression tt
                              (ExpExpressionMember
                                   (MkExpression tt
                                        (ExpName
                                         (BareName
                                          {| tags := tt;
                                             str := "standard_metadata" |}))
                                        (TypTypeName
                                         (BareName
                                          {| tags := tt;
                                             str := "standard_metadata_t" |}))
                                        InOut)
                                   {| tags := tt; str := "egress_spec" |})
                              (TypBit 9) Directionless)
                         (MkExpression tt
                              (ExpName
                               (BareName {| tags := tt; str := "port" |}))
                              (TypTypeName
                               (BareName
                                {| tags := tt; str := "egressSpec_t" |}))
                              Directionless)) StmUnit) (BlockEmpty tt)));
     (DeclTable tt {| tags := tt; str := "forward" |}
          [(MkTableKey tt
                (MkExpression tt
                     (ExpExpressionMember
                          (MkExpression tt
                               (ExpExpressionMember
                                    (MkExpression tt
                                         (ExpName
                                          (BareName
                                           {| tags := tt; str := "hdr" |}))
                                         (TypTypeName
                                          (BareName
                                           {| tags := tt; str := "headers" |}))
                                         InOut)
                                    {| tags := tt; str := "myHeader" |})
                               (TypHeader
                                [(MkFieldType
                                      {| tags := tt; str := "firstBit" |}
                                      (TypBit 1));
                                 (MkFieldType
                                      {| tags := tt; str := "padding" |}
                                      (TypBit 7))]) Directionless)
                          {| tags := tt; str := "firstBit" |}) (TypBit 1)
                     Directionless) {| tags := tt; str := "exact" |})]
          [(MkTableActionRef tt
                (MkTablePreActionRef
                     (BareName {| tags := tt; str := "do_forward" |}) nil)
                (TypAction nil
                     [(MkParameter false Directionless
                           (TypTypeName
                            (BareName
                             {| tags := tt; str := "egressSpec_t" |})) 
                           None {| tags := tt; str := "port" |})]));
           (MkTableActionRef tt
                (MkTablePreActionRef
                     (BareName {| tags := tt; str := "drop" |}) nil)
                (TypAction nil nil))] None
          (Some
           (MkTableActionRef tt
                (MkTablePreActionRef
                     (BareName {| tags := tt; str := "drop" |}) nil) 
                TypVoid))
          (Some {| tags := tt; value := 2; width_signed := None |}) nil)]
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
                                                        {| tags := tt;
                                                           str := "hdr" |}))
                                                      (TypTypeName
                                                       (BareName
                                                        {| tags := tt;
                                                           str := "headers" |}))
                                                      InOut)
                                                 {| tags := tt;
                                                    str := "myHeader" |})
                                            (TypHeader
                                             [(MkFieldType
                                                   {| tags := tt;
                                                      str := "firstBit" |}
                                                   (TypBit 1));
                                              (MkFieldType
                                                   {| tags := tt;
                                                      str := "padding" |}
                                                   (TypBit 7))])
                                            Directionless)
                                       {| tags := tt; str := "isValid" |})
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
                                                         {| tags := tt;
                                                            str := "forward" |}))
                                                       (TypTable
                                                        {| tags := tt;
                                                           str := "apply_result_forward" |})
                                                       Directionless)
                                                  {| tags := tt;
                                                     str := "apply" |})
                                             (TypFunction
                                              (MkFunctionType nil nil
                                                   FunTable
                                                   (TypTypeName
                                                    (BareName
                                                     {| tags := tt;
                                                        str := "apply_result_forward" |}))))
                                             Directionless) nil nil) StmUnit)
                              (BlockEmpty tt))) StmUnit) None) StmUnit)
         (BlockEmpty tt)).

Definition MyEgress := DeclControl tt {| tags := tt; str := "MyEgress" |} nil
    [(MkParameter false InOut
          (TypTypeName (BareName {| tags := tt; str := "headers" |})) 
          None {| tags := tt; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName (BareName {| tags := tt; str := "metadata" |})) 
          None {| tags := tt; str := "meta" |});
     (MkParameter false InOut
          (TypTypeName
           (BareName {| tags := tt; str := "standard_metadata_t" |})) 
          None {| tags := tt; str := "standard_metadata" |})] nil nil
    (BlockEmpty tt).

Definition MyDeparser := DeclControl tt {| tags := tt; str := "MyDeparser" |}
    nil
    [(MkParameter false Directionless
          (TypTypeName (BareName {| tags := tt; str := "packet_out" |})) 
          None {| tags := tt; str := "packet" |});
     (MkParameter false In
          (TypTypeName (BareName {| tags := tt; str := "headers" |})) 
          None {| tags := tt; str := "hdr" |})] nil nil
    (BlockCons
         (MkStatement tt
              (StatMethodCall
                   (MkExpression tt
                        (ExpExpressionMember
                             (MkExpression tt
                                  (ExpName
                                   (BareName
                                    {| tags := tt; str := "packet" |}))
                                  (TypTypeName
                                   (BareName
                                    {| tags := tt; str := "packet_out" |}))
                                  Directionless)
                             {| tags := tt; str := "emit" |})
                        (TypFunction
                         (MkFunctionType [{| tags := tt; str := "T2" |}]
                              [(MkParameter false In
                                    (TypTypeName
                                     (BareName {| tags := tt; str := "T2" |}))
                                    None {| tags := tt; str := "hdr" |})]
                              FunExtern TypVoid)) Directionless)
                   [(TypHeader
                     [(MkFieldType {| tags := tt; str := "firstBit" |}
                           (TypBit 1));
                      (MkFieldType {| tags := tt; str := "padding" |}
                           (TypBit 7))])]
                   [(Some
                     (MkExpression tt
                          (ExpExpressionMember
                               (MkExpression tt
                                    (ExpName
                                     (BareName
                                      {| tags := tt; str := "hdr" |}))
                                    (TypTypeName
                                     (BareName
                                      {| tags := tt; str := "headers" |}))
                                    In) {| tags := tt; str := "myHeader" |})
                          (TypHeader
                           [(MkFieldType {| tags := tt; str := "firstBit" |}
                                 (TypBit 1));
                            (MkFieldType {| tags := tt; str := "padding" |}
                                 (TypBit 7))]) Directionless))]) StmUnit)
         (BlockEmpty tt)).

Definition MyVerifyChecksum := DeclControl tt
    {| tags := tt; str := "MyVerifyChecksum" |} nil
    [(MkParameter false InOut
          (TypTypeName (BareName {| tags := tt; str := "headers" |})) 
          None {| tags := tt; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName (BareName {| tags := tt; str := "metadata" |})) 
          None {| tags := tt; str := "meta" |})] nil nil (BlockEmpty tt).

Definition MyComputeChecksum := DeclControl tt
    {| tags := tt; str := "MyComputeChecksum" |} nil
    [(MkParameter false InOut
          (TypTypeName (BareName {| tags := tt; str := "headers" |})) 
          None {| tags := tt; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName (BareName {| tags := tt; str := "metadata" |})) 
          None {| tags := tt; str := "meta" |})] nil nil (BlockEmpty tt).

Definition main := DeclInstantiation tt
    (TypSpecializedType
         (TypTypeName (BareName {| tags := tt; str := "V1Switch" |})) nil)
    [(MkExpression tt
          (ExpNamelessInstantiation
               (TypSpecializedType
                    (TypTypeName
                     (BareName {| tags := tt; str := "MyParser" |})) nil)
               nil)
          (TypParser
           (MkControlType nil
                [(MkParameter false Directionless
                      (TypExtern {| tags := tt; str := "packet_in" |}) 
                      None {| tags := tt; str := "packet" |});
                 (MkParameter false Out
                      (TypStruct
                       [(MkFieldType {| tags := tt; str := "myHeader" |}
                             (TypHeader
                              [(MkFieldType
                                    {| tags := tt; str := "firstBit" |}
                                    (TypBit 1));
                               (MkFieldType
                                    {| tags := tt; str := "padding" |}
                                    (TypBit 7))]))]) None
                      {| tags := tt; str := "hdr" |});
                 (MkParameter false InOut (TypStruct nil) None
                      {| tags := tt; str := "meta" |});
                 (MkParameter false InOut
                      (TypStruct
                       [(MkFieldType {| tags := tt; str := "ingress_port" |}
                             (TypBit 9));
                        (MkFieldType {| tags := tt; str := "egress_spec" |}
                             (TypBit 9));
                        (MkFieldType {| tags := tt; str := "egress_port" |}
                             (TypBit 9));
                        (MkFieldType {| tags := tt; str := "instance_type" |}
                             (TypBit 32));
                        (MkFieldType {| tags := tt; str := "packet_length" |}
                             (TypBit 32));
                        (MkFieldType {| tags := tt; str := "enq_timestamp" |}
                             (TypBit 32));
                        (MkFieldType {| tags := tt; str := "enq_qdepth" |}
                             (TypBit 19));
                        (MkFieldType {| tags := tt; str := "deq_timedelta" |}
                             (TypBit 32));
                        (MkFieldType {| tags := tt; str := "deq_qdepth" |}
                             (TypBit 19));
                        (MkFieldType
                             {| tags := tt;
                                str := "ingress_global_timestamp" |}
                             (TypBit 48));
                        (MkFieldType
                             {| tags := tt;
                                str := "egress_global_timestamp" |}
                             (TypBit 48));
                        (MkFieldType {| tags := tt; str := "mcast_grp" |}
                             (TypBit 16));
                        (MkFieldType {| tags := tt; str := "egress_rid" |}
                             (TypBit 16));
                        (MkFieldType
                             {| tags := tt; str := "checksum_error" |}
                             (TypBit 1));
                        (MkFieldType {| tags := tt; str := "parser_error" |}
                             TypError);
                        (MkFieldType {| tags := tt; str := "priority" |}
                             (TypBit 3))]) None
                      {| tags := tt; str := "standard_metadata" |})]))
          Directionless);
     (MkExpression tt
          (ExpNamelessInstantiation
               (TypSpecializedType
                    (TypTypeName
                     (BareName {| tags := tt; str := "MyVerifyChecksum" |}))
                    nil) nil)
          (TypControl
           (MkControlType nil
                [(MkParameter false InOut
                      (TypStruct
                       [(MkFieldType {| tags := tt; str := "myHeader" |}
                             (TypHeader
                              [(MkFieldType
                                    {| tags := tt; str := "firstBit" |}
                                    (TypBit 1));
                               (MkFieldType
                                    {| tags := tt; str := "padding" |}
                                    (TypBit 7))]))]) None
                      {| tags := tt; str := "hdr" |});
                 (MkParameter false InOut (TypStruct nil) None
                      {| tags := tt; str := "meta" |})])) Directionless);
     (MkExpression tt
          (ExpNamelessInstantiation
               (TypSpecializedType
                    (TypTypeName
                     (BareName {| tags := tt; str := "MyIngress" |})) nil)
               nil)
          (TypControl
           (MkControlType nil
                [(MkParameter false InOut
                      (TypStruct
                       [(MkFieldType {| tags := tt; str := "myHeader" |}
                             (TypHeader
                              [(MkFieldType
                                    {| tags := tt; str := "firstBit" |}
                                    (TypBit 1));
                               (MkFieldType
                                    {| tags := tt; str := "padding" |}
                                    (TypBit 7))]))]) None
                      {| tags := tt; str := "hdr" |});
                 (MkParameter false InOut (TypStruct nil) None
                      {| tags := tt; str := "meta" |});
                 (MkParameter false InOut
                      (TypStruct
                       [(MkFieldType {| tags := tt; str := "ingress_port" |}
                             (TypBit 9));
                        (MkFieldType {| tags := tt; str := "egress_spec" |}
                             (TypBit 9));
                        (MkFieldType {| tags := tt; str := "egress_port" |}
                             (TypBit 9));
                        (MkFieldType {| tags := tt; str := "instance_type" |}
                             (TypBit 32));
                        (MkFieldType {| tags := tt; str := "packet_length" |}
                             (TypBit 32));
                        (MkFieldType {| tags := tt; str := "enq_timestamp" |}
                             (TypBit 32));
                        (MkFieldType {| tags := tt; str := "enq_qdepth" |}
                             (TypBit 19));
                        (MkFieldType {| tags := tt; str := "deq_timedelta" |}
                             (TypBit 32));
                        (MkFieldType {| tags := tt; str := "deq_qdepth" |}
                             (TypBit 19));
                        (MkFieldType
                             {| tags := tt;
                                str := "ingress_global_timestamp" |}
                             (TypBit 48));
                        (MkFieldType
                             {| tags := tt;
                                str := "egress_global_timestamp" |}
                             (TypBit 48));
                        (MkFieldType {| tags := tt; str := "mcast_grp" |}
                             (TypBit 16));
                        (MkFieldType {| tags := tt; str := "egress_rid" |}
                             (TypBit 16));
                        (MkFieldType
                             {| tags := tt; str := "checksum_error" |}
                             (TypBit 1));
                        (MkFieldType {| tags := tt; str := "parser_error" |}
                             TypError);
                        (MkFieldType {| tags := tt; str := "priority" |}
                             (TypBit 3))]) None
                      {| tags := tt; str := "standard_metadata" |})]))
          Directionless);
     (MkExpression tt
          (ExpNamelessInstantiation
               (TypSpecializedType
                    (TypTypeName
                     (BareName {| tags := tt; str := "MyEgress" |})) nil)
               nil)
          (TypControl
           (MkControlType nil
                [(MkParameter false InOut
                      (TypStruct
                       [(MkFieldType {| tags := tt; str := "myHeader" |}
                             (TypHeader
                              [(MkFieldType
                                    {| tags := tt; str := "firstBit" |}
                                    (TypBit 1));
                               (MkFieldType
                                    {| tags := tt; str := "padding" |}
                                    (TypBit 7))]))]) None
                      {| tags := tt; str := "hdr" |});
                 (MkParameter false InOut (TypStruct nil) None
                      {| tags := tt; str := "meta" |});
                 (MkParameter false InOut
                      (TypStruct
                       [(MkFieldType {| tags := tt; str := "ingress_port" |}
                             (TypBit 9));
                        (MkFieldType {| tags := tt; str := "egress_spec" |}
                             (TypBit 9));
                        (MkFieldType {| tags := tt; str := "egress_port" |}
                             (TypBit 9));
                        (MkFieldType {| tags := tt; str := "instance_type" |}
                             (TypBit 32));
                        (MkFieldType {| tags := tt; str := "packet_length" |}
                             (TypBit 32));
                        (MkFieldType {| tags := tt; str := "enq_timestamp" |}
                             (TypBit 32));
                        (MkFieldType {| tags := tt; str := "enq_qdepth" |}
                             (TypBit 19));
                        (MkFieldType {| tags := tt; str := "deq_timedelta" |}
                             (TypBit 32));
                        (MkFieldType {| tags := tt; str := "deq_qdepth" |}
                             (TypBit 19));
                        (MkFieldType
                             {| tags := tt;
                                str := "ingress_global_timestamp" |}
                             (TypBit 48));
                        (MkFieldType
                             {| tags := tt;
                                str := "egress_global_timestamp" |}
                             (TypBit 48));
                        (MkFieldType {| tags := tt; str := "mcast_grp" |}
                             (TypBit 16));
                        (MkFieldType {| tags := tt; str := "egress_rid" |}
                             (TypBit 16));
                        (MkFieldType
                             {| tags := tt; str := "checksum_error" |}
                             (TypBit 1));
                        (MkFieldType {| tags := tt; str := "parser_error" |}
                             TypError);
                        (MkFieldType {| tags := tt; str := "priority" |}
                             (TypBit 3))]) None
                      {| tags := tt; str := "standard_metadata" |})]))
          Directionless);
     (MkExpression tt
          (ExpNamelessInstantiation
               (TypSpecializedType
                    (TypTypeName
                     (BareName {| tags := tt; str := "MyComputeChecksum" |}))
                    nil) nil)
          (TypControl
           (MkControlType nil
                [(MkParameter false InOut
                      (TypStruct
                       [(MkFieldType {| tags := tt; str := "myHeader" |}
                             (TypHeader
                              [(MkFieldType
                                    {| tags := tt; str := "firstBit" |}
                                    (TypBit 1));
                               (MkFieldType
                                    {| tags := tt; str := "padding" |}
                                    (TypBit 7))]))]) None
                      {| tags := tt; str := "hdr" |});
                 (MkParameter false InOut (TypStruct nil) None
                      {| tags := tt; str := "meta" |})])) Directionless);
     (MkExpression tt
          (ExpNamelessInstantiation
               (TypSpecializedType
                    (TypTypeName
                     (BareName {| tags := tt; str := "MyDeparser" |})) nil)
               nil)
          (TypControl
           (MkControlType nil
                [(MkParameter false Directionless
                      (TypExtern {| tags := tt; str := "packet_out" |}) 
                      None {| tags := tt; str := "packet" |});
                 (MkParameter false In
                      (TypStruct
                       [(MkFieldType {| tags := tt; str := "myHeader" |}
                             (TypHeader
                              [(MkFieldType
                                    {| tags := tt; str := "firstBit" |}
                                    (TypBit 1));
                               (MkFieldType
                                    {| tags := tt; str := "padding" |}
                                    (TypBit 7))]))]) None
                      {| tags := tt; str := "hdr" |})])) Directionless)]
    {| tags := tt; str := "main" |} None.

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


