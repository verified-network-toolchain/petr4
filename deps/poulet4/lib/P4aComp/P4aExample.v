Require Import Poulet4.P4light.Syntax.P4defs.
Open Scope string_scope.

Import ListNotations.

Definition decl'1 := DeclError NoInfo
    [{| stags := NoInfo; str := "NoError" |};
     {| stags := NoInfo; str := "PacketTooShort" |};
     {| stags := NoInfo; str := "NoMatch" |};
     {| stags := NoInfo; str := "StackOutOfBounds" |};
     {| stags := NoInfo; str := "HeaderTooShort" |};
     {| stags := NoInfo; str := "ParserTimeout" |};
     {| stags := NoInfo; str := "ParserInvalidArgument" |}].

Definition packet_in := DeclExternObject NoInfo
    {| stags := NoInfo; str := "packet_in" |} nil
    [(ProtoMethod NoInfo (TypBit 32%N) {| stags := NoInfo; str := "length" |}
          nil nil);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "advance" |} nil
          [(MkParameter false In (TypBit 32%N) None
                {| stags := NoInfo; str := "sizeInBits" |})]);
     (ProtoMethod NoInfo (TypTypeName {| stags := NoInfo; str := "T1" |})
          {| stags := NoInfo; str := "lookahead" |}
          [{| stags := NoInfo; str := "T1" |}] nil);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "extract" |}
          [{| stags := NoInfo; str := "T0" |}]
          [(MkParameter false Out
                (TypTypeName {| stags := NoInfo; str := "T0" |}) None
                {| stags := NoInfo; str := "variableSizeHeader" |});
           (MkParameter false In (TypBit 32%N) None
                {| stags := NoInfo; str := "variableFieldSizeInBits" |})]);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "extract" |}
          [{| stags := NoInfo; str := "T" |}]
          [(MkParameter false Out
                (TypTypeName {| stags := NoInfo; str := "T" |}) None
                {| stags := NoInfo; str := "hdr" |})])].

Definition packet_out := DeclExternObject NoInfo
    {| stags := NoInfo; str := "packet_out" |} nil
    [(ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "emit" |}
          [{| stags := NoInfo; str := "T2" |}]
          [(MkParameter false In
                (TypTypeName {| stags := NoInfo; str := "T2" |}) None
                {| stags := NoInfo; str := "hdr" |})])].

Definition verify'check'toSignal := DeclExternFunction NoInfo TypVoid
    {| stags := NoInfo; str := "verify" |} nil
    [(MkParameter false In TypBool None
          {| stags := NoInfo; str := "check" |});
     (MkParameter false In TypError None
          {| stags := NoInfo; str := "toSignal" |})].

Definition NoAction := DeclAction NoInfo
    {| stags := NoInfo; str := "NoAction" |} nil nil (BlockEmpty NoInfo).

Definition decl'2 := DeclMatchKind NoInfo
    [{| stags := NoInfo; str := "exact" |};
     {| stags := NoInfo; str := "ternary" |};
     {| stags := NoInfo; str := "lpm" |}].

Definition decl'3 := DeclMatchKind NoInfo
    [{| stags := NoInfo; str := "range" |};
     {| stags := NoInfo; str := "optional" |};
     {| stags := NoInfo; str := "selector" |}].

Definition standard_metadata_t := DeclStruct NoInfo
    {| stags := NoInfo; str := "standard_metadata_t" |}
    [(MkDeclarationField NoInfo (TypBit 9%N)
          {| stags := NoInfo; str := "ingress_port" |});
     (MkDeclarationField NoInfo (TypBit 9%N)
          {| stags := NoInfo; str := "egress_spec" |});
     (MkDeclarationField NoInfo (TypBit 9%N)
          {| stags := NoInfo; str := "egress_port" |});
     (MkDeclarationField NoInfo (TypBit 32%N)
          {| stags := NoInfo; str := "instance_type" |});
     (MkDeclarationField NoInfo (TypBit 32%N)
          {| stags := NoInfo; str := "packet_length" |});
     (MkDeclarationField NoInfo (TypBit 32%N)
          {| stags := NoInfo; str := "enq_timestamp" |});
     (MkDeclarationField NoInfo (TypBit 19%N)
          {| stags := NoInfo; str := "enq_qdepth" |});
     (MkDeclarationField NoInfo (TypBit 32%N)
          {| stags := NoInfo; str := "deq_timedelta" |});
     (MkDeclarationField NoInfo (TypBit 19%N)
          {| stags := NoInfo; str := "deq_qdepth" |});
     (MkDeclarationField NoInfo (TypBit 48%N)
          {| stags := NoInfo; str := "ingress_global_timestamp" |});
     (MkDeclarationField NoInfo (TypBit 48%N)
          {| stags := NoInfo; str := "egress_global_timestamp" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "mcast_grp" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "egress_rid" |});
     (MkDeclarationField NoInfo (TypBit 1%N)
          {| stags := NoInfo; str := "checksum_error" |});
     (MkDeclarationField NoInfo TypError
          {| stags := NoInfo; str := "parser_error" |});
     (MkDeclarationField NoInfo (TypBit 3%N)
          {| stags := NoInfo; str := "priority" |})].

Definition CounterType := DeclEnum NoInfo
    {| stags := NoInfo; str := "CounterType" |}
    [{| stags := NoInfo; str := "packets" |};
     {| stags := NoInfo; str := "bytes" |};
     {| stags := NoInfo; str := "packets_and_bytes" |}].

Definition MeterType := DeclEnum NoInfo
    {| stags := NoInfo; str := "MeterType" |}
    [{| stags := NoInfo; str := "packets" |};
     {| stags := NoInfo; str := "bytes" |}].

Definition counter := DeclExternObject NoInfo
    {| stags := NoInfo; str := "counter" |} nil
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "counter" |}
          [(MkParameter false Directionless (TypBit 32%N) None
                {| stags := NoInfo; str := "size" |});
           (MkParameter false Directionless
                (TypTypeName {| stags := NoInfo; str := "CounterType" |})
                None {| stags := NoInfo; str := "type" |})]);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "count" |} nil
          [(MkParameter false In (TypBit 32%N) None
                {| stags := NoInfo; str := "index" |})])].

Definition direct_counter := DeclExternObject NoInfo
    {| stags := NoInfo; str := "direct_counter" |} nil
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "direct_counter" |}
          [(MkParameter false Directionless
                (TypTypeName {| stags := NoInfo; str := "CounterType" |})
                None {| stags := NoInfo; str := "type" |})]);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "count" |} nil
          nil)].

Definition meter := DeclExternObject NoInfo
    {| stags := NoInfo; str := "meter" |} nil
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "meter" |}
          [(MkParameter false Directionless (TypBit 32%N) None
                {| stags := NoInfo; str := "size" |});
           (MkParameter false Directionless
                (TypTypeName {| stags := NoInfo; str := "MeterType" |}) 
                None {| stags := NoInfo; str := "type" |})]);
     (ProtoMethod NoInfo TypVoid
          {| stags := NoInfo; str := "execute_meter" |}
          [{| stags := NoInfo; str := "T3" |}]
          [(MkParameter false In (TypBit 32%N) None
                {| stags := NoInfo; str := "index" |});
           (MkParameter false Out
                (TypTypeName {| stags := NoInfo; str := "T3" |}) None
                {| stags := NoInfo; str := "result" |})])].

Definition direct_meter := DeclExternObject NoInfo
    {| stags := NoInfo; str := "direct_meter" |}
    [{| stags := NoInfo; str := "T4" |}]
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "direct_meter" |}
          [(MkParameter false Directionless
                (TypTypeName {| stags := NoInfo; str := "MeterType" |}) 
                None {| stags := NoInfo; str := "type" |})]);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "read" |} nil
          [(MkParameter false Out
                (TypTypeName {| stags := NoInfo; str := "T4" |}) None
                {| stags := NoInfo; str := "result" |})])].

Definition register := DeclExternObject NoInfo
    {| stags := NoInfo; str := "register" |}
    [{| stags := NoInfo; str := "T5" |}]
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "register" |}
          [(MkParameter false Directionless (TypBit 32%N) None
                {| stags := NoInfo; str := "size" |})]);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "write" |} nil
          [(MkParameter false In (TypBit 32%N) None
                {| stags := NoInfo; str := "index" |});
           (MkParameter false In
                (TypTypeName {| stags := NoInfo; str := "T5" |}) None
                {| stags := NoInfo; str := "value" |})]);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "read" |} nil
          [(MkParameter false Out
                (TypTypeName {| stags := NoInfo; str := "T5" |}) None
                {| stags := NoInfo; str := "result" |});
           (MkParameter false In (TypBit 32%N) None
                {| stags := NoInfo; str := "index" |})])].

Definition action_profile := DeclExternObject NoInfo
    {| stags := NoInfo; str := "action_profile" |} nil
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "action_profile" |}
          [(MkParameter false Directionless (TypBit 32%N) None
                {| stags := NoInfo; str := "size" |})])].

Definition random'result'lo'hi := DeclExternFunction NoInfo TypVoid
    {| stags := NoInfo; str := "random" |}
    [{| stags := NoInfo; str := "T6" |}]
    [(MkParameter false Out (TypTypeName {| stags := NoInfo; str := "T6" |})
          None {| stags := NoInfo; str := "result" |});
     (MkParameter false In (TypTypeName {| stags := NoInfo; str := "T6" |})
          None {| stags := NoInfo; str := "lo" |});
     (MkParameter false In (TypTypeName {| stags := NoInfo; str := "T6" |})
          None {| stags := NoInfo; str := "hi" |})].

Definition digest'receiver'data := DeclExternFunction NoInfo TypVoid
    {| stags := NoInfo; str := "digest" |}
    [{| stags := NoInfo; str := "T7" |}]
    [(MkParameter false In (TypBit 32%N) None
          {| stags := NoInfo; str := "receiver" |});
     (MkParameter false In (TypTypeName {| stags := NoInfo; str := "T7" |})
          None {| stags := NoInfo; str := "data" |})].

Definition HashAlgorithm := DeclEnum NoInfo
    {| stags := NoInfo; str := "HashAlgorithm" |}
    [{| stags := NoInfo; str := "crc32" |};
     {| stags := NoInfo; str := "crc32_custom" |};
     {| stags := NoInfo; str := "crc16" |};
     {| stags := NoInfo; str := "crc16_custom" |};
     {| stags := NoInfo; str := "random" |};
     {| stags := NoInfo; str := "identity" |};
     {| stags := NoInfo; str := "csum16" |};
     {| stags := NoInfo; str := "xor16" |}].

Definition mark_to_drop := DeclExternFunction NoInfo TypVoid
    {| stags := NoInfo; str := "mark_to_drop" |} nil nil.

Definition mark_to_drop'standard_metadata := DeclExternFunction NoInfo
    TypVoid {| stags := NoInfo; str := "mark_to_drop" |} nil
    [(MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "standard_metadata_t" |})
          None {| stags := NoInfo; str := "standard_metadata" |})].

Definition hash'result'algo'base'data'max := DeclExternFunction NoInfo
    TypVoid {| stags := NoInfo; str := "hash" |}
    [{| stags := NoInfo; str := "O" |}; {| stags := NoInfo; str := "T8" |};
     {| stags := NoInfo; str := "D" |}; {| stags := NoInfo; str := "M" |}]
    [(MkParameter false Out (TypTypeName {| stags := NoInfo; str := "O" |})
          None {| stags := NoInfo; str := "result" |});
     (MkParameter false In
          (TypTypeName {| stags := NoInfo; str := "HashAlgorithm" |}) 
          None {| stags := NoInfo; str := "algo" |});
     (MkParameter false In (TypTypeName {| stags := NoInfo; str := "T8" |})
          None {| stags := NoInfo; str := "base" |});
     (MkParameter false In (TypTypeName {| stags := NoInfo; str := "D" |})
          None {| stags := NoInfo; str := "data" |});
     (MkParameter false In (TypTypeName {| stags := NoInfo; str := "M" |})
          None {| stags := NoInfo; str := "max" |})].

Definition action_selector := DeclExternObject NoInfo
    {| stags := NoInfo; str := "action_selector" |} nil
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "action_selector" |}
          [(MkParameter false Directionless
                (TypTypeName {| stags := NoInfo; str := "HashAlgorithm" |})
                None {| stags := NoInfo; str := "algorithm" |});
           (MkParameter false Directionless (TypBit 32%N) None
                {| stags := NoInfo; str := "size" |});
           (MkParameter false Directionless (TypBit 32%N) None
                {| stags := NoInfo; str := "outputWidth" |})])].

Definition CloneType := DeclEnum NoInfo
    {| stags := NoInfo; str := "CloneType" |}
    [{| stags := NoInfo; str := "I2E" |};
     {| stags := NoInfo; str := "E2E" |}].

Definition Checksum16 := DeclExternObject NoInfo
    {| stags := NoInfo; str := "Checksum16" |} nil
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "Checksum16" |} nil);
     (ProtoMethod NoInfo (TypBit 16%N) {| stags := NoInfo; str := "get" |}
          [{| stags := NoInfo; str := "D9" |}]
          [(MkParameter false In
                (TypTypeName {| stags := NoInfo; str := "D9" |}) None
                {| stags := NoInfo; str := "data" |})])].

Definition verify_checksum'condition'data'checksum'algo := DeclExternFunction
    NoInfo TypVoid {| stags := NoInfo; str := "verify_checksum" |}
    [{| stags := NoInfo; str := "T10" |};
     {| stags := NoInfo; str := "O11" |}]
    [(MkParameter false In TypBool None
          {| stags := NoInfo; str := "condition" |});
     (MkParameter false In (TypTypeName {| stags := NoInfo; str := "T10" |})
          None {| stags := NoInfo; str := "data" |});
     (MkParameter false In (TypTypeName {| stags := NoInfo; str := "O11" |})
          None {| stags := NoInfo; str := "checksum" |});
     (MkParameter false Directionless
          (TypTypeName {| stags := NoInfo; str := "HashAlgorithm" |}) 
          None {| stags := NoInfo; str := "algo" |})].

Definition update_checksum'condition'data'checksum'algo := DeclExternFunction
    NoInfo TypVoid {| stags := NoInfo; str := "update_checksum" |}
    [{| stags := NoInfo; str := "T12" |};
     {| stags := NoInfo; str := "O13" |}]
    [(MkParameter false In TypBool None
          {| stags := NoInfo; str := "condition" |});
     (MkParameter false In (TypTypeName {| stags := NoInfo; str := "T12" |})
          None {| stags := NoInfo; str := "data" |});
     (MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "O13" |}) None
          {| stags := NoInfo; str := "checksum" |});
     (MkParameter false Directionless
          (TypTypeName {| stags := NoInfo; str := "HashAlgorithm" |}) 
          None {| stags := NoInfo; str := "algo" |})].

Definition verify_checksum_with_payload'condition'data'checksum'algo := DeclExternFunction
    NoInfo TypVoid
    {| stags := NoInfo; str := "verify_checksum_with_payload" |}
    [{| stags := NoInfo; str := "T14" |};
     {| stags := NoInfo; str := "O15" |}]
    [(MkParameter false In TypBool None
          {| stags := NoInfo; str := "condition" |});
     (MkParameter false In (TypTypeName {| stags := NoInfo; str := "T14" |})
          None {| stags := NoInfo; str := "data" |});
     (MkParameter false In (TypTypeName {| stags := NoInfo; str := "O15" |})
          None {| stags := NoInfo; str := "checksum" |});
     (MkParameter false Directionless
          (TypTypeName {| stags := NoInfo; str := "HashAlgorithm" |}) 
          None {| stags := NoInfo; str := "algo" |})].

Definition update_checksum_with_payload'condition'data'checksum'algo := DeclExternFunction
    NoInfo TypVoid
    {| stags := NoInfo; str := "update_checksum_with_payload" |}
    [{| stags := NoInfo; str := "T16" |};
     {| stags := NoInfo; str := "O17" |}]
    [(MkParameter false In TypBool None
          {| stags := NoInfo; str := "condition" |});
     (MkParameter false In (TypTypeName {| stags := NoInfo; str := "T16" |})
          None {| stags := NoInfo; str := "data" |});
     (MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "O17" |}) None
          {| stags := NoInfo; str := "checksum" |});
     (MkParameter false Directionless
          (TypTypeName {| stags := NoInfo; str := "HashAlgorithm" |}) 
          None {| stags := NoInfo; str := "algo" |})].

Definition resubmit'data := DeclExternFunction NoInfo TypVoid
    {| stags := NoInfo; str := "resubmit" |}
    [{| stags := NoInfo; str := "T18" |}]
    [(MkParameter false In (TypTypeName {| stags := NoInfo; str := "T18" |})
          None {| stags := NoInfo; str := "data" |})].

Definition recirculate'data := DeclExternFunction NoInfo TypVoid
    {| stags := NoInfo; str := "recirculate" |}
    [{| stags := NoInfo; str := "T19" |}]
    [(MkParameter false In (TypTypeName {| stags := NoInfo; str := "T19" |})
          None {| stags := NoInfo; str := "data" |})].

Definition clone'type'session := DeclExternFunction NoInfo TypVoid
    {| stags := NoInfo; str := "clone" |} nil
    [(MkParameter false In
          (TypTypeName {| stags := NoInfo; str := "CloneType" |}) None
          {| stags := NoInfo; str := "type" |});
     (MkParameter false In (TypBit 32%N) None
          {| stags := NoInfo; str := "session" |})].

Definition clone3'type'session'data := DeclExternFunction NoInfo TypVoid
    {| stags := NoInfo; str := "clone3" |}
    [{| stags := NoInfo; str := "T20" |}]
    [(MkParameter false In
          (TypTypeName {| stags := NoInfo; str := "CloneType" |}) None
          {| stags := NoInfo; str := "type" |});
     (MkParameter false In (TypBit 32%N) None
          {| stags := NoInfo; str := "session" |});
     (MkParameter false In (TypTypeName {| stags := NoInfo; str := "T20" |})
          None {| stags := NoInfo; str := "data" |})].

Definition truncate'length := DeclExternFunction NoInfo TypVoid
    {| stags := NoInfo; str := "truncate" |} nil
    [(MkParameter false In (TypBit 32%N) None
          {| stags := NoInfo; str := "length" |})].

Definition assert'check := DeclExternFunction NoInfo TypVoid
    {| stags := NoInfo; str := "assert" |} nil
    [(MkParameter false In TypBool None
          {| stags := NoInfo; str := "check" |})].

Definition assume'check := DeclExternFunction NoInfo TypVoid
    {| stags := NoInfo; str := "assume" |} nil
    [(MkParameter false In TypBool None
          {| stags := NoInfo; str := "check" |})].

Definition log_msg'msg := DeclExternFunction NoInfo TypVoid
    {| stags := NoInfo; str := "log_msg" |} nil
    [(MkParameter false Directionless TypString None
          {| stags := NoInfo; str := "msg" |})].

Definition log_msg'msg'data := DeclExternFunction NoInfo TypVoid
    {| stags := NoInfo; str := "log_msg" |}
    [{| stags := NoInfo; str := "T21" |}]
    [(MkParameter false Directionless TypString None
          {| stags := NoInfo; str := "msg" |});
     (MkParameter false In (TypTypeName {| stags := NoInfo; str := "T21" |})
          None {| stags := NoInfo; str := "data" |})].

Definition Parser := DeclParserType NoInfo
    {| stags := NoInfo; str := "Parser" |}
    [{| stags := NoInfo; str := "H" |}; {| stags := NoInfo; str := "M22" |}]
    [(MkParameter false Directionless
          (TypTypeName {| stags := NoInfo; str := "packet_in" |}) None
          {| stags := NoInfo; str := "b" |});
     (MkParameter false Out (TypTypeName {| stags := NoInfo; str := "H" |})
          None {| stags := NoInfo; str := "parsedHdr" |});
     (MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "M22" |}) None
          {| stags := NoInfo; str := "meta" |});
     (MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "standard_metadata_t" |})
          None {| stags := NoInfo; str := "standard_metadata" |})].

Definition VerifyChecksum := DeclControlType NoInfo
    {| stags := NoInfo; str := "VerifyChecksum" |}
    [{| stags := NoInfo; str := "H23" |};
     {| stags := NoInfo; str := "M24" |}]
    [(MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "H23" |}) None
          {| stags := NoInfo; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "M24" |}) None
          {| stags := NoInfo; str := "meta" |})].

Definition Ingress := DeclControlType NoInfo
    {| stags := NoInfo; str := "Ingress" |}
    [{| stags := NoInfo; str := "H25" |};
     {| stags := NoInfo; str := "M26" |}]
    [(MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "H25" |}) None
          {| stags := NoInfo; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "M26" |}) None
          {| stags := NoInfo; str := "meta" |});
     (MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "standard_metadata_t" |})
          None {| stags := NoInfo; str := "standard_metadata" |})].

Definition Egress := DeclControlType NoInfo
    {| stags := NoInfo; str := "Egress" |}
    [{| stags := NoInfo; str := "H27" |};
     {| stags := NoInfo; str := "M28" |}]
    [(MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "H27" |}) None
          {| stags := NoInfo; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "M28" |}) None
          {| stags := NoInfo; str := "meta" |});
     (MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "standard_metadata_t" |})
          None {| stags := NoInfo; str := "standard_metadata" |})].

Definition ComputeChecksum := DeclControlType NoInfo
    {| stags := NoInfo; str := "ComputeChecksum" |}
    [{| stags := NoInfo; str := "H29" |};
     {| stags := NoInfo; str := "M30" |}]
    [(MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "H29" |}) None
          {| stags := NoInfo; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "M30" |}) None
          {| stags := NoInfo; str := "meta" |})].

Definition Deparser := DeclControlType NoInfo
    {| stags := NoInfo; str := "Deparser" |}
    [{| stags := NoInfo; str := "H31" |}]
    [(MkParameter false Directionless
          (TypTypeName {| stags := NoInfo; str := "packet_out" |}) None
          {| stags := NoInfo; str := "b" |});
     (MkParameter false In (TypTypeName {| stags := NoInfo; str := "H31" |})
          None {| stags := NoInfo; str := "hdr" |})].

Definition V1Switch := DeclPackageType NoInfo
    {| stags := NoInfo; str := "V1Switch" |}
    [{| stags := NoInfo; str := "H32" |};
     {| stags := NoInfo; str := "M33" |}]
    [(MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "Parser" |})
               [(TypTypeName {| stags := NoInfo; str := "H32" |});
                (TypTypeName {| stags := NoInfo; str := "M33" |})]) None
          {| stags := NoInfo; str := "p" |});
     (MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "VerifyChecksum" |})
               [(TypTypeName {| stags := NoInfo; str := "H32" |});
                (TypTypeName {| stags := NoInfo; str := "M33" |})]) None
          {| stags := NoInfo; str := "vr" |});
     (MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "Ingress" |})
               [(TypTypeName {| stags := NoInfo; str := "H32" |});
                (TypTypeName {| stags := NoInfo; str := "M33" |})]) None
          {| stags := NoInfo; str := "ig" |});
     (MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "Egress" |})
               [(TypTypeName {| stags := NoInfo; str := "H32" |});
                (TypTypeName {| stags := NoInfo; str := "M33" |})]) None
          {| stags := NoInfo; str := "eg" |});
     (MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "ComputeChecksum" |})
               [(TypTypeName {| stags := NoInfo; str := "H32" |});
                (TypTypeName {| stags := NoInfo; str := "M33" |})]) None
          {| stags := NoInfo; str := "ck" |});
     (MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "Deparser" |})
               [(TypTypeName {| stags := NoInfo; str := "H32" |})]) None
          {| stags := NoInfo; str := "dep" |})].

Definition hdr := DeclHeader NoInfo {| stags := NoInfo; str := "hdr" |}
    [(MkDeclarationField NoInfo (TypBit 8%N)
          {| stags := NoInfo; str := "ignored" |});
     (MkDeclarationField NoInfo (TypBit 8%N)
          {| stags := NoInfo; str := "key" |})].

Definition Header_t := DeclStruct NoInfo
    {| stags := NoInfo; str := "Header_t" |}
    [(MkDeclarationField NoInfo
          (TypTypeName {| stags := NoInfo; str := "hdr" |})
          {| stags := NoInfo; str := "h" |})].

Definition Meta_t := DeclStruct NoInfo {| stags := NoInfo; str := "Meta_t" |}
    nil.

Definition p := DeclParser NoInfo {| stags := NoInfo; str := "p" |} nil
    [(MkParameter false Directionless
          (TypTypeName {| stags := NoInfo; str := "packet_in" |}) None
          {| stags := NoInfo; str := "b" |});
     (MkParameter false Out
          (TypTypeName {| stags := NoInfo; str := "Header_t" |}) None
          {| stags := NoInfo; str := "h" |});
     (MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "Meta_t" |}) None
          {| stags := NoInfo; str := "m" |});
     (MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "standard_metadata_t" |})
          None {| stags := NoInfo; str := "sm" |})] nil nil
    [(MkParserState NoInfo {| stags := NoInfo; str := "start" |}
          [(MkStatement NoInfo
                (StatMethodCall
                     (MkExpression NoInfo
                          (ExpExpressionMember
                               (MkExpression NoInfo
                                    (ExpName
                                     (BareName
                                      {| stags := NoInfo; str := "b" |})
                                     NoLocator)
                                    (TypTypeName
                                     {| stags := NoInfo;
                                        str := "packet_in" |}) Directionless)
                               {| stags := NoInfo; str := "extract" |})
                          (TypFunction
                           (MkFunctionType
                                [{| stags := NoInfo; str := "T" |}]
                                [(MkParameter false Out
                                      (TypTypeName
                                       {| stags := NoInfo; str := "T" |})
                                      None
                                      {| stags := NoInfo; str := "hdr" |})]
                                FunExtern TypVoid)) Directionless)
                     [(TypHeader
                       [( {| stags := NoInfo; str := "ignored" |},
                          (TypBit 8%N) );
                        ( {| stags := NoInfo; str := "key" |}, (TypBit 8%N) )])]
                     [(Some
                       (MkExpression NoInfo
                            (ExpExpressionMember
                                 (MkExpression NoInfo
                                      (ExpName
                                       (BareName
                                        {| stags := NoInfo; str := "h" |})
                                       NoLocator)
                                      (TypTypeName
                                       {| stags := NoInfo;
                                          str := "Header_t" |}) Out)
                                 {| stags := NoInfo; str := "h" |})
                            (TypHeader
                             [( {| stags := NoInfo; str := "ignored" |},
                                (TypBit 8%N) );
                              ( {| stags := NoInfo; str := "key" |},
                                (TypBit 8%N) )]) Directionless))]) StmUnit)]
          (ParserDirect NoInfo {| stags := NoInfo; str := "accept" |}))].

Definition prog := Program
    [decl'1; packet_in; packet_out; verify'check'toSignal; NoAction; decl'2;
     decl'3; standard_metadata_t; CounterType; MeterType; counter;
     direct_counter; meter; direct_meter; register; action_profile;
     random'result'lo'hi; digest'receiver'data; HashAlgorithm; mark_to_drop;
     mark_to_drop'standard_metadata; hash'result'algo'base'data'max;
     action_selector; CloneType; Checksum16;
     verify_checksum'condition'data'checksum'algo;
     update_checksum'condition'data'checksum'algo;
     verify_checksum_with_payload'condition'data'checksum'algo;
     update_checksum_with_payload'condition'data'checksum'algo;
     resubmit'data; recirculate'data; clone'type'session;
     clone3'type'session'data; truncate'length; assert'check; assume'check;
     log_msg'msg; log_msg'msg'data; Parser; VerifyChecksum; Ingress; Egress;
     ComputeChecksum; Deparser; V1Switch; hdr; Header_t; Meta_t; p].




Require Import Poulet4.Compile.ToP4cub.
Definition cub_prog0 :=
  Eval compute in 
  translate_program _ NoInfo prog.
Print cub_prog0.

Definition cub_prog : DeclCtx Info :=
{|
    controls := [];
    parsers :=
      [TD.TPParser "p" [] []
         [("b", PAInOut (E.TVar "packet_in"));
         ("h",
         PAOut
           (Sub.E.TStruct
              [("h",
               Sub.E.THeader [("ignored", E.TBit 8); ("key", E.TBit 8)])]));
         ("m", PAInOut (Sub.E.TStruct []));
         ("sm",
         PAInOut
           (Sub.E.TStruct
              [("ingress_port", E.TBit 9); ("egress_spec", E.TBit 9);
              ("egress_port", E.TBit 9); ("instance_type", E.TBit 32);
              ("packet_length", E.TBit 32); ("enq_timestamp", E.TBit 32);
              ("enq_qdepth", E.TBit 19); ("deq_timedelta", E.TBit 32);
              ("deq_qdepth", E.TBit 19);
              ("ingress_global_timestamp", E.TBit 48);
              ("egress_global_timestamp", E.TBit 48);
              ("mcast_grp", E.TBit 16); ("egress_rid", E.TBit 16);
              ("checksum_error", E.TBit 1); ("parser_error", E.TError);
              ("priority", E.TBit 3)]))]
         {|
           Parser.stmt :=
             InferMemberTypes.ST.SSeq
               (InferMemberTypes.ST.SExternMethodCall "packet_in" "extract"
                  []
                  {|
                    paramargs :=
                      [("hdr",
                       PAOut
                         (InferMemberTypes.E.EExprMember
                            (E.THeader
                               [("ignored", E.TBit 8); ("key", E.TBit 8)])
                            "h"
                            (E.EVar
                               (E.TStruct
                                  [("h",
                                   E.THeader
                                     [("ignored", E.TBit 8);
                                     ("key", E.TBit 8)])]) "h" NoInfo) NoInfo))];
                    rtrns := None
                  |} NoInfo) (ST.SSkip NoInfo) NoInfo;
           Parser.trans := Parser.PGoto Parser.STAccept NoInfo
         |}
         [("start",
          {|
            Parser.stmt :=
              InferMemberTypes.ST.SSeq
                (InferMemberTypes.ST.SExternMethodCall "packet_in" "extract"
                   []
                   {|
                     paramargs :=
                       [("hdr",
                        PAOut
                          (InferMemberTypes.E.EExprMember
                             (E.THeader
                                [("ignored", E.TBit 8); ("key", E.TBit 8)])
                             "h"
                             (E.EVar
                                (E.TStruct
                                   [("h",
                                    E.THeader
                                      [("ignored", E.TBit 8);
                                      ("key", E.TBit 8)])]) "h" NoInfo)
                             NoInfo))];
                     rtrns := None
                   |} NoInfo) (ST.SSkip NoInfo) NoInfo;
            Parser.trans := Parser.PGoto Parser.STAccept NoInfo
          |})] NoInfo];
    tables := [];
    actions := [Control.CDAction "NoAction" [] (ST.SSkip NoInfo) NoInfo];
    functions := [];
    package_types :=
      [("V1Switch",
       (["H32"; "M33"],
       [("p", Sub.E.CTType (E.TVar "Parser"));
       ("vr", Sub.E.CTType (E.TVar "VerifyChecksum"));
       ("ig", Sub.E.CTType (E.TVar "Ingress"));
       ("eg", Sub.E.CTType (E.TVar "Egress"));
       ("ck", Sub.E.CTType (E.TVar "ComputeChecksum"));
       ("dep", Sub.E.CTType (E.TVar "Deparser"))], NoInfo))];
    packages := [];
    externs :=
      [TD.TPExtern "_" [] []
         [("log_msg",
          ([],
          {|
            paramargs :=
              [("msg", PAInOut E.TBool); ("data", PAIn (E.TVar "T21"))];
            rtrns := None
          |}))] NoInfo;
      TD.TPExtern "_" [] []
        [("log_msg",
         ([], {| paramargs := [("msg", PAInOut E.TBool)]; rtrns := None |}))]
        NoInfo;
      TD.TPExtern "_" [] []
        [("assume",
         ([], {| paramargs := [("check", PAIn E.TBool)]; rtrns := None |}))]
        NoInfo;
      TD.TPExtern "_" [] []
        [("assert",
         ([], {| paramargs := [("check", PAIn E.TBool)]; rtrns := None |}))]
        NoInfo;
      TD.TPExtern "_" [] []
        [("truncate",
         ([],
         {| paramargs := [("length", PAIn (E.TBit 32))]; rtrns := None |}))]
        NoInfo;
      TD.TPExtern "_" [] []
        [("clone3",
         ([],
         {|
           paramargs :=
             [("type", PAIn (E.TVar "CloneType"));
             ("session", PAIn (E.TBit 32)); ("data", PAIn (E.TVar "T20"))];
           rtrns := None
         |}))] NoInfo;
      TD.TPExtern "_" [] []
        [("clone",
         ([],
         {|
           paramargs :=
             [("type", PAIn (E.TVar "CloneType"));
             ("session", PAIn (E.TBit 32))];
           rtrns := None
         |}))] NoInfo;
      TD.TPExtern "_" [] []
        [("recirculate",
         ([],
         {| paramargs := [("data", PAIn (E.TVar "T19"))]; rtrns := None |}))]
        NoInfo;
      TD.TPExtern "_" [] []
        [("resubmit",
         ([],
         {| paramargs := [("data", PAIn (E.TVar "T18"))]; rtrns := None |}))]
        NoInfo;
      TD.TPExtern "_" [] []
        [("update_checksum_with_payload",
         ([],
         {|
           paramargs :=
             [("condition", PAIn E.TBool); ("data", PAIn (E.TVar "T16"));
             ("checksum", PAInOut (E.TVar "O17"));
             ("algo", PAInOut (E.TVar "HashAlgorithm"))];
           rtrns := None
         |}))] NoInfo;
      TD.TPExtern "_" [] []
        [("verify_checksum_with_payload",
         ([],
         {|
           paramargs :=
             [("condition", PAIn E.TBool); ("data", PAIn (E.TVar "T14"));
             ("checksum", PAIn (E.TVar "O15"));
             ("algo", PAInOut (E.TVar "HashAlgorithm"))];
           rtrns := None
         |}))] NoInfo;
      TD.TPExtern "_" [] []
        [("update_checksum",
         ([],
         {|
           paramargs :=
             [("condition", PAIn E.TBool); ("data", PAIn (E.TVar "T12"));
             ("checksum", PAInOut (E.TVar "O13"));
             ("algo", PAInOut (E.TVar "HashAlgorithm"))];
           rtrns := None
         |}))] NoInfo;
      TD.TPExtern "_" [] []
        [("verify_checksum",
         ([],
         {|
           paramargs :=
             [("condition", PAIn E.TBool); ("data", PAIn (E.TVar "T10"));
             ("checksum", PAIn (E.TVar "O11"));
             ("algo", PAInOut (E.TVar "HashAlgorithm"))];
           rtrns := None
         |}))] NoInfo;
      TD.TPExtern "Checksum16" [] []
        [("Checksum16",
         ([], {| paramargs := []; rtrns := Some (E.TVar "Checksum16") |}));
        ("get",
        ([],
        {|
          paramargs := [("data", PAIn (E.TVar "D9"))];
          rtrns := Some (E.TBit 16)
        |}))] NoInfo;
      TD.TPExtern "action_selector" []
        [("algorithm", Sub.E.CTType (E.TVar "HashAlgorithm"));
        ("size", Sub.E.CTType (E.TBit 32));
        ("outputWidth", Sub.E.CTType (E.TBit 32))]
        [("action_selector",
         ([],
         {|
           paramargs :=
             [("algorithm", PAInOut (E.TVar "HashAlgorithm"));
             ("size", PAInOut (E.TBit 32));
             ("outputWidth", PAInOut (E.TBit 32))];
           rtrns := Some (E.TVar "action_selector")
         |}))] NoInfo;
      TD.TPExtern "_" [] []
        [("hash",
         ([],
         {|
           paramargs :=
             [("result", PAOut (E.TVar "O"));
             ("algo", PAIn (E.TVar "HashAlgorithm"));
             ("base", PAIn (E.TVar "T8")); ("data", PAIn (E.TVar "D"));
             ("max", PAIn (E.TVar "M"))];
           rtrns := None
         |}))] NoInfo;
      TD.TPExtern "_" [] []
        [("mark_to_drop",
         ([],
         {|
           paramargs :=
             [("standard_metadata",
              PAInOut
                (Sub.E.TStruct
                   [("ingress_port", E.TBit 9); ("egress_spec", E.TBit 9);
                   ("egress_port", E.TBit 9); ("instance_type", E.TBit 32);
                   ("packet_length", E.TBit 32);
                   ("enq_timestamp", E.TBit 32); ("enq_qdepth", E.TBit 19);
                   ("deq_timedelta", E.TBit 32); ("deq_qdepth", E.TBit 19);
                   ("ingress_global_timestamp", E.TBit 48);
                   ("egress_global_timestamp", E.TBit 48);
                   ("mcast_grp", E.TBit 16); ("egress_rid", E.TBit 16);
                   ("checksum_error", E.TBit 1); ("parser_error", E.TError);
                   ("priority", E.TBit 3)]))];
           rtrns := None
         |}))] NoInfo;
      TD.TPExtern "_" [] []
        [("mark_to_drop", ([], {| paramargs := []; rtrns := None |}))] NoInfo;
      TD.TPExtern "_" [] []
        [("digest",
         ([],
         {|
           paramargs :=
             [("receiver", PAIn (E.TBit 32)); ("data", PAIn (E.TVar "T7"))];
           rtrns := None
         |}))] NoInfo;
      TD.TPExtern "_" [] []
        [("random",
         ([],
         {|
           paramargs :=
             [("result", PAOut (E.TVar "T6")); ("lo", PAIn (E.TVar "T6"));
             ("hi", PAIn (E.TVar "T6"))];
           rtrns := None
         |}))] NoInfo;
      TD.TPExtern "action_profile" [] [("size", Sub.E.CTType (E.TBit 32))]
        [("action_profile",
         ([],
         {|
           paramargs := [("size", PAInOut (E.TBit 32))];
           rtrns := Some (E.TVar "action_profile")
         |}))] NoInfo;
      TD.TPExtern "register" ["T5"] [("size", Sub.E.CTType (E.TBit 32))]
        [("register",
         ([],
         {|
           paramargs := [("size", PAInOut (E.TBit 32))];
           rtrns := Some (E.TVar "register")
         |}));
        ("write",
        ([],
        {|
          paramargs :=
            [("index", PAIn (E.TBit 32)); ("value", PAIn (E.TVar "T5"))];
          rtrns := None
        |}));
        ("read",
        ([],
        {|
          paramargs :=
            [("result", PAOut (E.TVar "T5")); ("index", PAIn (E.TBit 32))];
          rtrns := None
        |}))] NoInfo;
      TD.TPExtern "direct_meter" ["T4"]
        [("type", Sub.E.CTType (E.TVar "MeterType"))]
        [("direct_meter",
         ([],
         {|
           paramargs := [("type", PAInOut (E.TVar "MeterType"))];
           rtrns := Some (E.TVar "direct_meter")
         |}));
        ("read",
        ([],
        {| paramargs := [("result", PAOut (E.TVar "T4"))]; rtrns := None |}))]
        NoInfo;
      TD.TPExtern "meter" []
        [("size", Sub.E.CTType (E.TBit 32));
        ("type", Sub.E.CTType (E.TVar "MeterType"))]
        [("meter",
         ([],
         {|
           paramargs :=
             [("size", PAInOut (E.TBit 32));
             ("type", PAInOut (E.TVar "MeterType"))];
           rtrns := Some (E.TVar "meter")
         |}));
        ("execute_meter",
        ([],
        {|
          paramargs :=
            [("index", PAIn (E.TBit 32)); ("result", PAOut (E.TVar "T3"))];
          rtrns := None
        |}))] NoInfo;
      TD.TPExtern "direct_counter" []
        [("type", Sub.E.CTType (E.TVar "CounterType"))]
        [("direct_counter",
         ([],
         {|
           paramargs := [("type", PAInOut (E.TVar "CounterType"))];
           rtrns := Some (E.TVar "direct_counter")
         |})); ("count", ([], {| paramargs := []; rtrns := None |}))] NoInfo;
      TD.TPExtern "counter" []
        [("size", Sub.E.CTType (E.TBit 32));
        ("type", Sub.E.CTType (E.TVar "CounterType"))]
        [("counter",
         ([],
         {|
           paramargs :=
             [("size", PAInOut (E.TBit 32));
             ("type", PAInOut (E.TVar "CounterType"))];
           rtrns := Some (E.TVar "counter")
         |}));
        ("count",
        ([], {| paramargs := [("index", PAIn (E.TBit 32))]; rtrns := None |}))]
        NoInfo;
      TD.TPExtern "_" [] []
        [("verify",
         ([],
         {|
           paramargs :=
             [("check", PAIn E.TBool); ("toSignal", PAIn E.TError)];
           rtrns := None
         |}))] NoInfo;
      TD.TPExtern "packet_out" [] []
        [("emit",
         ([],
         {| paramargs := [("hdr", PAIn (E.TVar "T2"))]; rtrns := None |}))]
        NoInfo;
      TD.TPExtern "packet_in" [] []
        [("length", ([], {| paramargs := []; rtrns := Some (E.TBit 32) |}));
        ("advance",
        ([],
        {| paramargs := [("sizeInBits", PAIn (E.TBit 32))]; rtrns := None |}));
        ("lookahead",
        ([], {| paramargs := []; rtrns := Some (E.TVar "T1") |}));
        ("extract",
        ([],
        {|
          paramargs :=
            [("variableSizeHeader", PAOut (E.TVar "T0"));
            ("variableFieldSizeInBits", PAIn (E.TBit 32))];
          rtrns := None
        |}));
        ("extract",
        ([], {| paramargs := [("hdr", PAOut (E.TVar "T"))]; rtrns := None |}))]
        NoInfo];
    types :=
      [("standard_metadata_t",
       E.TStruct
         [("ingress_port", E.TBit 9); ("egress_spec", E.TBit 9);
         ("egress_port", E.TBit 9); ("instance_type", E.TBit 32);
         ("packet_length", E.TBit 32); ("enq_timestamp", E.TBit 32);
         ("enq_qdepth", E.TBit 19); ("deq_timedelta", E.TBit 32);
         ("deq_qdepth", E.TBit 19); ("ingress_global_timestamp", E.TBit 48);
         ("egress_global_timestamp", E.TBit 48); ("mcast_grp", E.TBit 16);
         ("egress_rid", E.TBit 16); ("checksum_error", E.TBit 1);
         ("parser_error", E.TError); ("priority", E.TBit 3)]);
      ("hdr", Sub.E.THeader [("ignored", E.TBit 8); ("key", E.TBit 8)]);
      ("Header_t",
      Sub.E.TStruct
        [("h", Sub.E.THeader [("ignored", E.TBit 8); ("key", E.TBit 8)])]);
      ("Meta_t", Sub.E.TStruct []); ("Meta_t", Sub.E.TStruct []);
      ("Header_t",
      Sub.E.TStruct
        [("h", Sub.E.THeader [("ignored", E.TBit 8); ("key", E.TBit 8)])]);
      ("hdr", Sub.E.THeader [("ignored", E.TBit 8); ("key", E.TBit 8)]);
      ("standard_metadata_t",
      Sub.E.TStruct
        [("ingress_port", E.TBit 9); ("egress_spec", E.TBit 9);
        ("egress_port", E.TBit 9); ("instance_type", E.TBit 32);
        ("packet_length", E.TBit 32); ("enq_timestamp", E.TBit 32);
        ("enq_qdepth", E.TBit 19); ("deq_timedelta", E.TBit 32);
        ("deq_qdepth", E.TBit 19); ("ingress_global_timestamp", E.TBit 48);
        ("egress_global_timestamp", E.TBit 48); ("mcast_grp", E.TBit 16);
        ("egress_rid", E.TBit 16); ("checksum_error", E.TBit 1);
        ("parser_error", E.TError); ("priority", E.TBit 3)])]
  |}.

Definition parser :=
  TD.TPParser "p" [] []
         [("b", PAInOut (E.TVar "packet_in"));
         ("h",
         PAOut
           (Sub.E.TStruct
              [("h",
               Sub.E.THeader [("ignored", E.TBit 8); ("key", E.TBit 8)])]));
         ("m", PAInOut (Sub.E.TStruct []));
         ("sm",
         PAInOut
           (Sub.E.TStruct
              [("ingress_port", E.TBit 9); ("egress_spec", E.TBit 9);
              ("egress_port", E.TBit 9); ("instance_type", E.TBit 32);
              ("packet_length", E.TBit 32); ("enq_timestamp", E.TBit 32);
              ("enq_qdepth", E.TBit 19); ("deq_timedelta", E.TBit 32);
              ("deq_qdepth", E.TBit 19);
              ("ingress_global_timestamp", E.TBit 48);
              ("egress_global_timestamp", E.TBit 48);
              ("mcast_grp", E.TBit 16); ("egress_rid", E.TBit 16);
              ("checksum_error", E.TBit 1); ("parser_error", E.TError);
              ("priority", E.TBit 3)]))]
         {|
           Parser.stmt :=
             InferMemberTypes.ST.SSeq
               (InferMemberTypes.ST.SExternMethodCall "packet_in" "extract"
                  []
                  {|
                    paramargs :=
                      [("hdr",
                       PAOut
                         (InferMemberTypes.E.EExprMember
                            (E.THeader
                               [("ignored", E.TBit 8); ("key", E.TBit 8)])
                            "h"
                            (E.EVar
                               (E.TStruct
                                  [("h",
                                   E.THeader
                                     [("ignored", E.TBit 8);
                                     ("key", E.TBit 8)])]) "h" NoInfo) NoInfo))];
                    rtrns := None
                  |} NoInfo) (ST.SSkip NoInfo) NoInfo;
           Parser.trans := Parser.PGoto Parser.STAccept NoInfo
         |}
         [("start",
          {|
            Parser.stmt :=
              InferMemberTypes.ST.SSeq
                (InferMemberTypes.ST.SExternMethodCall "packet_in" "extract"
                   []
                   {|
                     paramargs :=
                       [("hdr",
                        PAOut
                          (InferMemberTypes.E.EExprMember
                             (E.THeader
                                [("ignored", E.TBit 8); ("key", E.TBit 8)])
                             "h"
                             (E.EVar
                                (E.TStruct
                                   [("h",
                                    E.THeader
                                      [("ignored", E.TBit 8);
                                      ("key", E.TBit 8)])]) "h" NoInfo)
                             NoInfo))];
                     rtrns := None
                   |} NoInfo) (ST.SSkip NoInfo) NoInfo;
            Parser.trans := Parser.PGoto Parser.STAccept NoInfo
          |})] NoInfo.

Require Import Poulet4.P4aComp.P4aComp.
Eval compute in (get_parser _ parser).
(* MISSING: function to convert a list of state blocks, as returned by get_parser, into a full p4 automaton. *)
