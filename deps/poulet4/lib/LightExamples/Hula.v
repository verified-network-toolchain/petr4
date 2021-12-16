Require Import Poulet4.P4defs.
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

Definition egressSpec_t := DeclTypeDef NoInfo
    {| stags := NoInfo; str := "egressSpec_t" |} (inl (TypBit 9%N)).

Definition macAddr_t := DeclTypeDef NoInfo
    {| stags := NoInfo; str := "macAddr_t" |} (inl (TypBit 48%N)).

Definition ip4Addr_t := DeclTypeDef NoInfo
    {| stags := NoInfo; str := "ip4Addr_t" |} (inl (TypBit 32%N)).

Definition qdepth_t := DeclTypeDef NoInfo
    {| stags := NoInfo; str := "qdepth_t" |} (inl (TypBit 15%N)).

Definition digest_t := DeclTypeDef NoInfo
    {| stags := NoInfo; str := "digest_t" |} (inl (TypBit 32%N)).

Definition ethernet_t := DeclHeader NoInfo
    {| stags := NoInfo; str := "ethernet_t" |}
    [(MkDeclarationField NoInfo (TypBit 48%N)
          {| stags := NoInfo; str := "dstAddr" |});
     (MkDeclarationField NoInfo (TypBit 48%N)
          {| stags := NoInfo; str := "srcAddr" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "etherType" |})].

Definition srcRoute_t := DeclHeader NoInfo
    {| stags := NoInfo; str := "srcRoute_t" |}
    [(MkDeclarationField NoInfo (TypBit 1%N)
          {| stags := NoInfo; str := "bos" |});
     (MkDeclarationField NoInfo (TypBit 15%N)
          {| stags := NoInfo; str := "port" |})].

Definition hula_t := DeclHeader NoInfo {| stags := NoInfo; str := "hula_t" |}
    [(MkDeclarationField NoInfo (TypBit 1%N)
          {| stags := NoInfo; str := "dir" |});
     (MkDeclarationField NoInfo (TypBit 15%N)
          {| stags := NoInfo; str := "qdepth" |});
     (MkDeclarationField NoInfo (TypBit 32%N)
          {| stags := NoInfo; str := "digest" |})].

Definition ipv4_t := DeclHeader NoInfo {| stags := NoInfo; str := "ipv4_t" |}
    [(MkDeclarationField NoInfo (TypBit 4%N)
          {| stags := NoInfo; str := "version" |});
     (MkDeclarationField NoInfo (TypBit 4%N)
          {| stags := NoInfo; str := "ihl" |});
     (MkDeclarationField NoInfo (TypBit 8%N)
          {| stags := NoInfo; str := "diffserv" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "totalLen" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "identification" |});
     (MkDeclarationField NoInfo (TypBit 3%N)
          {| stags := NoInfo; str := "flags" |});
     (MkDeclarationField NoInfo (TypBit 13%N)
          {| stags := NoInfo; str := "fragOffset" |});
     (MkDeclarationField NoInfo (TypBit 8%N)
          {| stags := NoInfo; str := "ttl" |});
     (MkDeclarationField NoInfo (TypBit 8%N)
          {| stags := NoInfo; str := "protocol" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "hdrChecksum" |});
     (MkDeclarationField NoInfo (TypBit 32%N)
          {| stags := NoInfo; str := "srcAddr" |});
     (MkDeclarationField NoInfo (TypBit 32%N)
          {| stags := NoInfo; str := "dstAddr" |})].

Definition udp_t := DeclHeader NoInfo {| stags := NoInfo; str := "udp_t" |}
    [(MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "srcPort" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "dstPort" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "length_" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "checksum" |})].

Definition metadata := DeclStruct NoInfo
    {| stags := NoInfo; str := "metadata" |}
    [(MkDeclarationField NoInfo (TypBit 32%N)
          {| stags := NoInfo; str := "index" |})].

Definition headers := DeclStruct NoInfo
    {| stags := NoInfo; str := "headers" |}
    [(MkDeclarationField NoInfo
          (TypHeader
           [( {| stags := NoInfo; str := "dstAddr" |}, (TypBit 48%N) );
            ( {| stags := NoInfo; str := "srcAddr" |}, (TypBit 48%N) );
            ( {| stags := NoInfo; str := "etherType" |}, (TypBit 16%N) )])
          {| stags := NoInfo; str := "ethernet" |});
     (MkDeclarationField NoInfo
          (TypArray
               (TypHeader
                [( {| stags := NoInfo; str := "bos" |}, (TypBit 1%N) );
                 ( {| stags := NoInfo; str := "port" |}, (TypBit 15%N) )])
               9%N) {| stags := NoInfo; str := "srcRoutes" |});
     (MkDeclarationField NoInfo
          (TypHeader
           [( {| stags := NoInfo; str := "version" |}, (TypBit 4%N) );
            ( {| stags := NoInfo; str := "ihl" |}, (TypBit 4%N) );
            ( {| stags := NoInfo; str := "diffserv" |}, (TypBit 8%N) );
            ( {| stags := NoInfo; str := "totalLen" |}, (TypBit 16%N) );
            ( {| stags := NoInfo; str := "identification" |}, (TypBit 16%N) );
            ( {| stags := NoInfo; str := "flags" |}, (TypBit 3%N) );
            ( {| stags := NoInfo; str := "fragOffset" |}, (TypBit 13%N) );
            ( {| stags := NoInfo; str := "ttl" |}, (TypBit 8%N) );
            ( {| stags := NoInfo; str := "protocol" |}, (TypBit 8%N) );
            ( {| stags := NoInfo; str := "hdrChecksum" |}, (TypBit 16%N) );
            ( {| stags := NoInfo; str := "srcAddr" |}, (TypBit 32%N) );
            ( {| stags := NoInfo; str := "dstAddr" |}, (TypBit 32%N) )])
          {| stags := NoInfo; str := "ipv4" |});
     (MkDeclarationField NoInfo
          (TypHeader
           [( {| stags := NoInfo; str := "srcPort" |}, (TypBit 16%N) );
            ( {| stags := NoInfo; str := "dstPort" |}, (TypBit 16%N) );
            ( {| stags := NoInfo; str := "length_" |}, (TypBit 16%N) );
            ( {| stags := NoInfo; str := "checksum" |}, (TypBit 16%N) )])
          {| stags := NoInfo; str := "udp" |});
     (MkDeclarationField NoInfo
          (TypHeader
           [( {| stags := NoInfo; str := "dir" |}, (TypBit 1%N) );
            ( {| stags := NoInfo; str := "qdepth" |}, (TypBit 15%N) );
            ( {| stags := NoInfo; str := "digest" |}, (TypBit 32%N) )])
          {| stags := NoInfo; str := "hula" |})].

Definition MyParser := DeclParser NoInfo
    {| stags := NoInfo; str := "MyParser" |} nil
    [(MkParameter false Directionless
          (TypTypeName {| stags := NoInfo; str := "packet_in" |}) None
          {| stags := NoInfo; str := "packet" |});
     (MkParameter false Out
          (TypTypeName {| stags := NoInfo; str := "headers" |}) None
          {| stags := NoInfo; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "metadata" |}) None
          {| stags := NoInfo; str := "meta" |});
     (MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "standard_metadata_t" |})
          None {| stags := NoInfo; str := "standard_metadata" |})] nil nil
    [(MkParserState NoInfo {| stags := NoInfo; str := "start" |} nil
          (ParserDirect NoInfo
               {| stags := NoInfo; str := "parse_ethernet" |}));
     (MkParserState NoInfo {| stags := NoInfo; str := "parse_ethernet" |}
          [(MkStatement NoInfo
                (StatMethodCall
                     (MkExpression NoInfo
                          (ExpExpressionMember
                               (MkExpression NoInfo
                                    (ExpName
                                     (BareName
                                      {| stags := NoInfo; str := "packet" |})
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
                       [( {| stags := NoInfo; str := "dstAddr" |},
                          (TypBit 48%N) );
                        ( {| stags := NoInfo; str := "srcAddr" |},
                          (TypBit 48%N) );
                        ( {| stags := NoInfo; str := "etherType" |},
                          (TypBit 16%N) )])]
                     [(Some
                       (MkExpression NoInfo
                            (ExpExpressionMember
                                 (MkExpression NoInfo
                                      (ExpName
                                       (BareName
                                        {| stags := NoInfo; str := "hdr" |})
                                       NoLocator)
                                      (TypTypeName
                                       {| stags := NoInfo;
                                          str := "headers" |}) Out)
                                 {| stags := NoInfo; str := "ethernet" |})
                            (TypHeader
                             [( {| stags := NoInfo; str := "dstAddr" |},
                                (TypBit 48%N) );
                              ( {| stags := NoInfo; str := "srcAddr" |},
                                (TypBit 48%N) );
                              ( {| stags := NoInfo; str := "etherType" |},
                                (TypBit 16%N) )]) Directionless))]) StmUnit)]
          (ParserSelect NoInfo
               [(MkExpression NoInfo
                     (ExpExpressionMember
                          (MkExpression NoInfo
                               (ExpExpressionMember
                                    (MkExpression NoInfo
                                         (ExpName
                                          (BareName
                                           {| stags := NoInfo;
                                              str := "hdr" |}) NoLocator)
                                         (TypTypeName
                                          {| stags := NoInfo;
                                             str := "headers" |}) Out)
                                    {| stags := NoInfo; str := "ethernet" |})
                               (TypHeader
                                [( {| stags := NoInfo; str := "dstAddr" |},
                                   (TypBit 48%N) );
                                 ( {| stags := NoInfo; str := "srcAddr" |},
                                   (TypBit 48%N) );
                                 ( {| stags := NoInfo; str := "etherType" |},
                                   (TypBit 16%N) )]) Directionless)
                          {| stags := NoInfo; str := "etherType" |})
                     (TypBit 16%N) Directionless)]
               [(MkParserCase NoInfo
                     [(MkMatch NoInfo
                           (MatchCast
                            (TypSet (TypBit 16%N)) (MkExpression NoInfo
                                                        (ExpInt
                                                         {| itags := NoInfo;
                                                            value := 9029;
                                                            width_signed := (
                                                            Some
                                                            ( 16%N, false )) |})
                                                        (TypBit 16%N)
                                                        Directionless))
                           (TypBit 16%N))]
                     {| stags := NoInfo; str := "parse_hula" |});
                (MkParserCase NoInfo
                     [(MkMatch NoInfo
                           (MatchCast
                            (TypSet (TypBit 16%N)) (MkExpression NoInfo
                                                        (ExpInt
                                                         {| itags := NoInfo;
                                                            value := 2048;
                                                            width_signed := (
                                                            Some
                                                            ( 16%N, false )) |})
                                                        (TypBit 16%N)
                                                        Directionless))
                           (TypBit 16%N))]
                     {| stags := NoInfo; str := "parse_ipv4" |});
                (MkParserCase NoInfo
                     [(MkMatch NoInfo MatchDontCare (TypBit 16%N))]
                     {| stags := NoInfo; str := "accept" |})]));
     (MkParserState NoInfo {| stags := NoInfo; str := "parse_hula" |}
          [(MkStatement NoInfo
                (StatMethodCall
                     (MkExpression NoInfo
                          (ExpExpressionMember
                               (MkExpression NoInfo
                                    (ExpName
                                     (BareName
                                      {| stags := NoInfo; str := "packet" |})
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
                       [( {| stags := NoInfo; str := "dir" |}, (TypBit 1%N) );
                        ( {| stags := NoInfo; str := "qdepth" |},
                          (TypBit 15%N) );
                        ( {| stags := NoInfo; str := "digest" |},
                          (TypBit 32%N) )])]
                     [(Some
                       (MkExpression NoInfo
                            (ExpExpressionMember
                                 (MkExpression NoInfo
                                      (ExpName
                                       (BareName
                                        {| stags := NoInfo; str := "hdr" |})
                                       NoLocator)
                                      (TypTypeName
                                       {| stags := NoInfo;
                                          str := "headers" |}) Out)
                                 {| stags := NoInfo; str := "hula" |})
                            (TypHeader
                             [( {| stags := NoInfo; str := "dir" |},
                                (TypBit 1%N) );
                              ( {| stags := NoInfo; str := "qdepth" |},
                                (TypBit 15%N) );
                              ( {| stags := NoInfo; str := "digest" |},
                                (TypBit 32%N) )]) Directionless))]) StmUnit)]
          (ParserDirect NoInfo
               {| stags := NoInfo; str := "parse_srcRouting" |}));
     (MkParserState NoInfo {| stags := NoInfo; str := "parse_srcRouting" |}
          [(MkStatement NoInfo
                (StatMethodCall
                     (MkExpression NoInfo
                          (ExpExpressionMember
                               (MkExpression NoInfo
                                    (ExpName
                                     (BareName
                                      {| stags := NoInfo; str := "packet" |})
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
                       [( {| stags := NoInfo; str := "bos" |}, (TypBit 1%N) );
                        ( {| stags := NoInfo; str := "port" |},
                          (TypBit 15%N) )])]
                     [(Some
                       (MkExpression NoInfo
                            (ExpExpressionMember
                                 (MkExpression NoInfo
                                      (ExpExpressionMember
                                           (MkExpression NoInfo
                                                (ExpName
                                                 (BareName
                                                  {| stags := NoInfo;
                                                     str := "hdr" |})
                                                 NoLocator)
                                                (TypTypeName
                                                 {| stags := NoInfo;
                                                    str := "headers" |}) Out)
                                           {| stags := NoInfo;
                                              str := "srcRoutes" |})
                                      (TypArray
                                           (TypHeader
                                            [( {| stags := NoInfo;
                                                  str := "bos" |},
                                               (TypBit 1%N) );
                                             ( {| stags := NoInfo;
                                                  str := "port" |},
                                               (TypBit 15%N) )]) 9%N)
                                      Directionless)
                                 {| stags := NoInfo; str := "next" |})
                            (TypHeader
                             [( {| stags := NoInfo; str := "bos" |},
                                (TypBit 1%N) );
                              ( {| stags := NoInfo; str := "port" |},
                                (TypBit 15%N) )]) Directionless))]) StmUnit)]
          (ParserSelect NoInfo
               [(MkExpression NoInfo
                     (ExpExpressionMember
                          (MkExpression NoInfo
                               (ExpExpressionMember
                                    (MkExpression NoInfo
                                         (ExpExpressionMember
                                              (MkExpression NoInfo
                                                   (ExpName
                                                    (BareName
                                                     {| stags := NoInfo;
                                                        str := "hdr" |})
                                                    NoLocator)
                                                   (TypTypeName
                                                    {| stags := NoInfo;
                                                       str := "headers" |})
                                                   Out)
                                              {| stags := NoInfo;
                                                 str := "srcRoutes" |})
                                         (TypArray
                                              (TypHeader
                                               [( {| stags := NoInfo;
                                                     str := "bos" |},
                                                  (TypBit 1%N) );
                                                ( {| stags := NoInfo;
                                                     str := "port" |},
                                                  (TypBit 15%N) )]) 9%N)
                                         Directionless)
                                    {| stags := NoInfo; str := "last" |})
                               (TypHeader
                                [( {| stags := NoInfo; str := "bos" |},
                                   (TypBit 1%N) );
                                 ( {| stags := NoInfo; str := "port" |},
                                   (TypBit 15%N) )]) Directionless)
                          {| stags := NoInfo; str := "bos" |}) (TypBit 1%N)
                     Directionless)]
               [(MkParserCase NoInfo
                     [(MkMatch NoInfo
                           (MatchCast
                            (TypSet (TypBit 1%N)) (MkExpression NoInfo
                                                       (ExpInt
                                                        {| itags := NoInfo;
                                                           value := 1;
                                                           width_signed := (
                                                           Some
                                                           ( 1%N, false )) |})
                                                       (TypBit 1%N)
                                                       Directionless))
                           (TypBit 1%N))]
                     {| stags := NoInfo; str := "parse_ipv4" |});
                (MkParserCase NoInfo
                     [(MkMatch NoInfo MatchDontCare (TypBit 1%N))]
                     {| stags := NoInfo; str := "parse_srcRouting" |})]));
     (MkParserState NoInfo {| stags := NoInfo; str := "parse_ipv4" |}
          [(MkStatement NoInfo
                (StatMethodCall
                     (MkExpression NoInfo
                          (ExpExpressionMember
                               (MkExpression NoInfo
                                    (ExpName
                                     (BareName
                                      {| stags := NoInfo; str := "packet" |})
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
                       [( {| stags := NoInfo; str := "version" |},
                          (TypBit 4%N) );
                        ( {| stags := NoInfo; str := "ihl" |}, (TypBit 4%N) );
                        ( {| stags := NoInfo; str := "diffserv" |},
                          (TypBit 8%N) );
                        ( {| stags := NoInfo; str := "totalLen" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "identification" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "flags" |},
                          (TypBit 3%N) );
                        ( {| stags := NoInfo; str := "fragOffset" |},
                          (TypBit 13%N) );
                        ( {| stags := NoInfo; str := "ttl" |}, (TypBit 8%N) );
                        ( {| stags := NoInfo; str := "protocol" |},
                          (TypBit 8%N) );
                        ( {| stags := NoInfo; str := "hdrChecksum" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "srcAddr" |},
                          (TypBit 32%N) );
                        ( {| stags := NoInfo; str := "dstAddr" |},
                          (TypBit 32%N) )])]
                     [(Some
                       (MkExpression NoInfo
                            (ExpExpressionMember
                                 (MkExpression NoInfo
                                      (ExpName
                                       (BareName
                                        {| stags := NoInfo; str := "hdr" |})
                                       NoLocator)
                                      (TypTypeName
                                       {| stags := NoInfo;
                                          str := "headers" |}) Out)
                                 {| stags := NoInfo; str := "ipv4" |})
                            (TypHeader
                             [( {| stags := NoInfo; str := "version" |},
                                (TypBit 4%N) );
                              ( {| stags := NoInfo; str := "ihl" |},
                                (TypBit 4%N) );
                              ( {| stags := NoInfo; str := "diffserv" |},
                                (TypBit 8%N) );
                              ( {| stags := NoInfo; str := "totalLen" |},
                                (TypBit 16%N) );
                              ( {| stags := NoInfo;
                                   str := "identification" |},
                                (TypBit 16%N) );
                              ( {| stags := NoInfo; str := "flags" |},
                                (TypBit 3%N) );
                              ( {| stags := NoInfo; str := "fragOffset" |},
                                (TypBit 13%N) );
                              ( {| stags := NoInfo; str := "ttl" |},
                                (TypBit 8%N) );
                              ( {| stags := NoInfo; str := "protocol" |},
                                (TypBit 8%N) );
                              ( {| stags := NoInfo; str := "hdrChecksum" |},
                                (TypBit 16%N) );
                              ( {| stags := NoInfo; str := "srcAddr" |},
                                (TypBit 32%N) );
                              ( {| stags := NoInfo; str := "dstAddr" |},
                                (TypBit 32%N) )]) Directionless))]) StmUnit)]
          (ParserSelect NoInfo
               [(MkExpression NoInfo
                     (ExpExpressionMember
                          (MkExpression NoInfo
                               (ExpExpressionMember
                                    (MkExpression NoInfo
                                         (ExpName
                                          (BareName
                                           {| stags := NoInfo;
                                              str := "hdr" |}) NoLocator)
                                         (TypTypeName
                                          {| stags := NoInfo;
                                             str := "headers" |}) Out)
                                    {| stags := NoInfo; str := "ipv4" |})
                               (TypHeader
                                [( {| stags := NoInfo; str := "version" |},
                                   (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "ihl" |},
                                   (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "diffserv" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo; str := "totalLen" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo;
                                      str := "identification" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "flags" |},
                                   (TypBit 3%N) );
                                 ( {| stags := NoInfo; str := "fragOffset" |},
                                   (TypBit 13%N) );
                                 ( {| stags := NoInfo; str := "ttl" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo; str := "protocol" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo;
                                      str := "hdrChecksum" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "srcAddr" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "dstAddr" |},
                                   (TypBit 32%N) )]) Directionless)
                          {| stags := NoInfo; str := "protocol" |})
                     (TypBit 8%N) Directionless)]
               [(MkParserCase NoInfo
                     [(MkMatch NoInfo
                           (MatchCast
                            (TypSet (TypBit 8%N)) (MkExpression NoInfo
                                                       (ExpInt
                                                        {| itags := NoInfo;
                                                           value := 17;
                                                           width_signed := (
                                                           Some
                                                           ( 8%N, false )) |})
                                                       (TypBit 8%N)
                                                       Directionless))
                           (TypBit 8%N))]
                     {| stags := NoInfo; str := "parse_udp" |});
                (MkParserCase NoInfo
                     [(MkMatch NoInfo MatchDontCare (TypBit 8%N))]
                     {| stags := NoInfo; str := "accept" |})]));
     (MkParserState NoInfo {| stags := NoInfo; str := "parse_udp" |}
          [(MkStatement NoInfo
                (StatMethodCall
                     (MkExpression NoInfo
                          (ExpExpressionMember
                               (MkExpression NoInfo
                                    (ExpName
                                     (BareName
                                      {| stags := NoInfo; str := "packet" |})
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
                       [( {| stags := NoInfo; str := "srcPort" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "dstPort" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "length_" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "checksum" |},
                          (TypBit 16%N) )])]
                     [(Some
                       (MkExpression NoInfo
                            (ExpExpressionMember
                                 (MkExpression NoInfo
                                      (ExpName
                                       (BareName
                                        {| stags := NoInfo; str := "hdr" |})
                                       NoLocator)
                                      (TypTypeName
                                       {| stags := NoInfo;
                                          str := "headers" |}) Out)
                                 {| stags := NoInfo; str := "udp" |})
                            (TypHeader
                             [( {| stags := NoInfo; str := "srcPort" |},
                                (TypBit 16%N) );
                              ( {| stags := NoInfo; str := "dstPort" |},
                                (TypBit 16%N) );
                              ( {| stags := NoInfo; str := "length_" |},
                                (TypBit 16%N) );
                              ( {| stags := NoInfo; str := "checksum" |},
                                (TypBit 16%N) )]) Directionless))]) StmUnit)]
          (ParserDirect NoInfo {| stags := NoInfo; str := "accept" |}))].

Definition MyVerifyChecksum := DeclControl NoInfo
    {| stags := NoInfo; str := "MyVerifyChecksum" |} nil
    [(MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "headers" |}) None
          {| stags := NoInfo; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "metadata" |}) None
          {| stags := NoInfo; str := "meta" |})] nil nil (BlockEmpty NoInfo).

Definition MyIngress := DeclControl NoInfo
    {| stags := NoInfo; str := "MyIngress" |} nil
    [(MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "headers" |}) None
          {| stags := NoInfo; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "metadata" |}) None
          {| stags := NoInfo; str := "meta" |});
     (MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "standard_metadata_t" |})
          None {| stags := NoInfo; str := "standard_metadata" |})] nil
    [(DeclInstantiation NoInfo
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "register" |})
               [(TypTypeName {| stags := NoInfo; str := "qdepth_t" |})])
          [(MkExpression NoInfo
                (ExpInt
                 {| itags := NoInfo; value := 32;
                    width_signed := (Some ( 32%N, false )) |}) (TypBit 32%N)
                Directionless)]
          {| stags := NoInfo; str := "srcindex_qdepth_reg" |} nil);
     (DeclInstantiation NoInfo
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "register" |})
               [(TypTypeName {| stags := NoInfo; str := "digest_t" |})])
          [(MkExpression NoInfo
                (ExpInt
                 {| itags := NoInfo; value := 32;
                    width_signed := (Some ( 32%N, false )) |}) (TypBit 32%N)
                Directionless)]
          {| stags := NoInfo; str := "srcindex_digest_reg" |} nil);
     (DeclInstantiation NoInfo
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "register" |})
               [(TypBit 16%N)])
          [(MkExpression NoInfo
                (ExpInt
                 {| itags := NoInfo; value := 32;
                    width_signed := (Some ( 32%N, false )) |}) (TypBit 32%N)
                Directionless)]
          {| stags := NoInfo; str := "dstindex_nhop_reg" |} nil);
     (DeclInstantiation NoInfo
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "register" |})
               [(TypBit 16%N)])
          [(MkExpression NoInfo
                (ExpInt
                 {| itags := NoInfo; value := 65536;
                    width_signed := (Some ( 32%N, false )) |}) (TypBit 32%N)
                Directionless)] {| stags := NoInfo; str := "flow_port_reg" |}
          nil);
     (DeclAction NoInfo {| stags := NoInfo; str := "drop" |} nil nil
          (BlockCons
               (MkStatement NoInfo
                    (StatMethodCall
                         (MkExpression NoInfo
                              (ExpName
                               (BareName
                                {| stags := NoInfo; str := "mark_to_drop" |})
                               NoLocator)
                              (TypFunction
                               (MkFunctionType nil nil FunExtern TypVoid))
                              Directionless) nil nil) StmUnit)
               (BlockEmpty NoInfo)));
     (DeclAction NoInfo {| stags := NoInfo; str := "nop" |} nil nil
          (BlockEmpty NoInfo));
     (DeclAction NoInfo {| stags := NoInfo; str := "update_ttl" |} nil nil
          (BlockCons
               (MkStatement NoInfo
                    (StatAssignment
                         (MkExpression NoInfo
                              (ExpExpressionMember
                                   (MkExpression NoInfo
                                        (ExpExpressionMember
                                             (MkExpression NoInfo
                                                  (ExpName
                                                   (BareName
                                                    {| stags := NoInfo;
                                                       str := "hdr" |})
                                                   NoLocator)
                                                  (TypTypeName
                                                   {| stags := NoInfo;
                                                      str := "headers" |})
                                                  InOut)
                                             {| stags := NoInfo;
                                                str := "ipv4" |})
                                        (TypHeader
                                         [( {| stags := NoInfo;
                                               str := "version" |},
                                            (TypBit 4%N) );
                                          ( {| stags := NoInfo;
                                               str := "ihl" |},
                                            (TypBit 4%N) );
                                          ( {| stags := NoInfo;
                                               str := "diffserv" |},
                                            (TypBit 8%N) );
                                          ( {| stags := NoInfo;
                                               str := "totalLen" |},
                                            (TypBit 16%N) );
                                          ( {| stags := NoInfo;
                                               str := "identification" |},
                                            (TypBit 16%N) );
                                          ( {| stags := NoInfo;
                                               str := "flags" |},
                                            (TypBit 3%N) );
                                          ( {| stags := NoInfo;
                                               str := "fragOffset" |},
                                            (TypBit 13%N) );
                                          ( {| stags := NoInfo;
                                               str := "ttl" |},
                                            (TypBit 8%N) );
                                          ( {| stags := NoInfo;
                                               str := "protocol" |},
                                            (TypBit 8%N) );
                                          ( {| stags := NoInfo;
                                               str := "hdrChecksum" |},
                                            (TypBit 16%N) );
                                          ( {| stags := NoInfo;
                                               str := "srcAddr" |},
                                            (TypBit 32%N) );
                                          ( {| stags := NoInfo;
                                               str := "dstAddr" |},
                                            (TypBit 32%N) )]) Directionless)
                                   {| stags := NoInfo; str := "ttl" |})
                              (TypBit 8%N) Directionless)
                         (MkExpression NoInfo
                              (ExpBinaryOp Minus
                                   ( (MkExpression NoInfo
                                          (ExpExpressionMember
                                               (MkExpression NoInfo
                                                    (ExpExpressionMember
                                                         (MkExpression NoInfo
                                                              (ExpName
                                                               (BareName
                                                                {| stags := NoInfo;
                                                                   str := "hdr" |})
                                                               NoLocator)
                                                              (TypTypeName
                                                               {| stags := NoInfo;
                                                                  str := "headers" |})
                                                              InOut)
                                                         {| stags := NoInfo;
                                                            str := "ipv4" |})
                                                    (TypHeader
                                                     [( {| stags := NoInfo;
                                                           str := "version" |},
                                                        (TypBit 4%N) );
                                                      ( {| stags := NoInfo;
                                                           str := "ihl" |},
                                                        (TypBit 4%N) );
                                                      ( {| stags := NoInfo;
                                                           str := "diffserv" |},
                                                        (TypBit 8%N) );
                                                      ( {| stags := NoInfo;
                                                           str := "totalLen" |},
                                                        (TypBit 16%N) );
                                                      ( {| stags := NoInfo;
                                                           str := "identification" |},
                                                        (TypBit 16%N) );
                                                      ( {| stags := NoInfo;
                                                           str := "flags" |},
                                                        (TypBit 3%N) );
                                                      ( {| stags := NoInfo;
                                                           str := "fragOffset" |},
                                                        (TypBit 13%N) );
                                                      ( {| stags := NoInfo;
                                                           str := "ttl" |},
                                                        (TypBit 8%N) );
                                                      ( {| stags := NoInfo;
                                                           str := "protocol" |},
                                                        (TypBit 8%N) );
                                                      ( {| stags := NoInfo;
                                                           str := "hdrChecksum" |},
                                                        (TypBit 16%N) );
                                                      ( {| stags := NoInfo;
                                                           str := "srcAddr" |},
                                                        (TypBit 32%N) );
                                                      ( {| stags := NoInfo;
                                                           str := "dstAddr" |},
                                                        (TypBit 32%N) )])
                                                    Directionless)
                                               {| stags := NoInfo;
                                                  str := "ttl" |})
                                          (TypBit 8%N) Directionless),
                                     (MkExpression NoInfo
                                          (ExpInt
                                           {| itags := NoInfo; value := 1;
                                              width_signed := (Some
                                                               ( 8%N, false )) |})
                                          (TypBit 8%N) Directionless) ))
                              (TypBit 8%N) Directionless)) StmUnit)
               (BlockEmpty NoInfo)));
     (DeclAction NoInfo {| stags := NoInfo; str := "set_dmac" |} nil
          [(MkParameter false Directionless
                (TypTypeName {| stags := NoInfo; str := "macAddr_t" |}) 
                None {| stags := NoInfo; str := "dstAddr" |})]
          (BlockCons
               (MkStatement NoInfo
                    (StatAssignment
                         (MkExpression NoInfo
                              (ExpExpressionMember
                                   (MkExpression NoInfo
                                        (ExpExpressionMember
                                             (MkExpression NoInfo
                                                  (ExpName
                                                   (BareName
                                                    {| stags := NoInfo;
                                                       str := "hdr" |})
                                                   NoLocator)
                                                  (TypTypeName
                                                   {| stags := NoInfo;
                                                      str := "headers" |})
                                                  InOut)
                                             {| stags := NoInfo;
                                                str := "ethernet" |})
                                        (TypHeader
                                         [( {| stags := NoInfo;
                                               str := "dstAddr" |},
                                            (TypBit 48%N) );
                                          ( {| stags := NoInfo;
                                               str := "srcAddr" |},
                                            (TypBit 48%N) );
                                          ( {| stags := NoInfo;
                                               str := "etherType" |},
                                            (TypBit 16%N) )]) Directionless)
                                   {| stags := NoInfo; str := "srcAddr" |})
                              (TypBit 48%N) Directionless)
                         (MkExpression NoInfo
                              (ExpExpressionMember
                                   (MkExpression NoInfo
                                        (ExpExpressionMember
                                             (MkExpression NoInfo
                                                  (ExpName
                                                   (BareName
                                                    {| stags := NoInfo;
                                                       str := "hdr" |})
                                                   NoLocator)
                                                  (TypTypeName
                                                   {| stags := NoInfo;
                                                      str := "headers" |})
                                                  InOut)
                                             {| stags := NoInfo;
                                                str := "ethernet" |})
                                        (TypHeader
                                         [( {| stags := NoInfo;
                                               str := "dstAddr" |},
                                            (TypBit 48%N) );
                                          ( {| stags := NoInfo;
                                               str := "srcAddr" |},
                                            (TypBit 48%N) );
                                          ( {| stags := NoInfo;
                                               str := "etherType" |},
                                            (TypBit 16%N) )]) Directionless)
                                   {| stags := NoInfo; str := "dstAddr" |})
                              (TypBit 48%N) Directionless)) StmUnit)
               (BlockCons
                    (MkStatement NoInfo
                         (StatAssignment
                              (MkExpression NoInfo
                                   (ExpExpressionMember
                                        (MkExpression NoInfo
                                             (ExpExpressionMember
                                                  (MkExpression NoInfo
                                                       (ExpName
                                                        (BareName
                                                         {| stags := NoInfo;
                                                            str := "hdr" |})
                                                        NoLocator)
                                                       (TypTypeName
                                                        {| stags := NoInfo;
                                                           str := "headers" |})
                                                       InOut)
                                                  {| stags := NoInfo;
                                                     str := "ethernet" |})
                                             (TypHeader
                                              [( {| stags := NoInfo;
                                                    str := "dstAddr" |},
                                                 (TypBit 48%N) );
                                               ( {| stags := NoInfo;
                                                    str := "srcAddr" |},
                                                 (TypBit 48%N) );
                                               ( {| stags := NoInfo;
                                                    str := "etherType" |},
                                                 (TypBit 16%N) )])
                                             Directionless)
                                        {| stags := NoInfo;
                                           str := "dstAddr" |}) (TypBit 48%N)
                                   Directionless)
                              (MkExpression NoInfo
                                   (ExpName
                                    (BareName
                                     {| stags := NoInfo; str := "dstAddr" |})
                                    NoLocator)
                                   (TypTypeName
                                    {| stags := NoInfo; str := "macAddr_t" |})
                                   In)) StmUnit) (BlockEmpty NoInfo))));
     (DeclAction NoInfo {| stags := NoInfo; str := "srcRoute_nhop" |} nil nil
          (BlockCons
               (MkStatement NoInfo
                    (StatAssignment
                         (MkExpression NoInfo
                              (ExpExpressionMember
                                   (MkExpression NoInfo
                                        (ExpName
                                         (BareName
                                          {| stags := NoInfo;
                                             str := "standard_metadata" |})
                                         NoLocator)
                                        (TypTypeName
                                         {| stags := NoInfo;
                                            str := "standard_metadata_t" |})
                                        InOut)
                                   {| stags := NoInfo;
                                      str := "egress_spec" |}) (TypBit 9%N)
                              Directionless)
                         (MkExpression NoInfo
                              (ExpCast (TypBit 9%N)
                                   (MkExpression NoInfo
                                        (ExpExpressionMember
                                             (MkExpression NoInfo
                                                  (ExpArrayAccess
                                                       (MkExpression NoInfo
                                                            (ExpExpressionMember
                                                                 (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "hdr" |})
                                                                    NoLocator)
                                                                    (TypTypeName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "headers" |})
                                                                    InOut)
                                                                 {| stags := NoInfo;
                                                                    str := "srcRoutes" |})
                                                            (TypArray
                                                                 (TypHeader
                                                                  [( 
                                                                   {| 
                                                                   stags := NoInfo;
                                                                   str := "bos" |},
                                                                   (TypBit
                                                                    1%N) );
                                                                   ( 
                                                                   {| 
                                                                   stags := NoInfo;
                                                                   str := "port" |},
                                                                   (TypBit
                                                                    15%N) )])
                                                                 9%N)
                                                            Directionless)
                                                       (MkExpression NoInfo
                                                            (ExpInt
                                                             {| itags := NoInfo;
                                                                value := 0;
                                                                width_signed := 
                                                                None |})
                                                            TypInteger
                                                            Directionless))
                                                  (TypHeader
                                                   [( {| stags := NoInfo;
                                                         str := "bos" |},
                                                      (TypBit 1%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "port" |},
                                                      (TypBit 15%N) )])
                                                  Directionless)
                                             {| stags := NoInfo;
                                                str := "port" |})
                                        (TypBit 15%N) Directionless))
                              (TypBit 9%N) Directionless)) StmUnit)
               (BlockCons
                    (MkStatement NoInfo
                         (StatMethodCall
                              (MkExpression NoInfo
                                   (ExpExpressionMember
                                        (MkExpression NoInfo
                                             (ExpExpressionMember
                                                  (MkExpression NoInfo
                                                       (ExpName
                                                        (BareName
                                                         {| stags := NoInfo;
                                                            str := "hdr" |})
                                                        NoLocator)
                                                       (TypTypeName
                                                        {| stags := NoInfo;
                                                           str := "headers" |})
                                                       InOut)
                                                  {| stags := NoInfo;
                                                     str := "srcRoutes" |})
                                             (TypArray
                                                  (TypHeader
                                                   [( {| stags := NoInfo;
                                                         str := "bos" |},
                                                      (TypBit 1%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "port" |},
                                                      (TypBit 15%N) )]) 9%N)
                                             Directionless)
                                        {| stags := NoInfo;
                                           str := "pop_front" |})
                                   (TypFunction
                                    (MkFunctionType nil
                                         [(MkParameter false Directionless
                                               TypInteger None
                                               {| stags := NoInfo;
                                                  str := "count" |})]
                                         FunBuiltin TypVoid)) Directionless)
                              nil
                              [(Some
                                (MkExpression NoInfo
                                     (ExpInt
                                      {| itags := NoInfo; value := 1;
                                         width_signed := None |}) TypInteger
                                     Directionless))]) StmUnit)
                    (BlockEmpty NoInfo))));
     (DeclAction NoInfo {| stags := NoInfo; str := "hula_dst" |} nil
          [(MkParameter false Directionless (TypBit 32%N) None
                {| stags := NoInfo; str := "index" |})]
          (BlockCons
               (MkStatement NoInfo
                    (StatAssignment
                         (MkExpression NoInfo
                              (ExpExpressionMember
                                   (MkExpression NoInfo
                                        (ExpName
                                         (BareName
                                          {| stags := NoInfo;
                                             str := "meta" |}) NoLocator)
                                        (TypTypeName
                                         {| stags := NoInfo;
                                            str := "metadata" |}) InOut)
                                   {| stags := NoInfo; str := "index" |})
                              (TypBit 32%N) Directionless)
                         (MkExpression NoInfo
                              (ExpName
                               (BareName
                                {| stags := NoInfo; str := "index" |})
                               NoLocator) (TypBit 32%N) In)) StmUnit)
               (BlockEmpty NoInfo)));
     (DeclAction NoInfo {| stags := NoInfo; str := "hula_set_nhop" |} nil
          [(MkParameter false Directionless (TypBit 32%N) None
                {| stags := NoInfo; str := "index" |})]
          (BlockCons
               (MkStatement NoInfo
                    (StatMethodCall
                         (MkExpression NoInfo
                              (ExpExpressionMember
                                   (MkExpression NoInfo
                                        (ExpName
                                         (BareName
                                          {| stags := NoInfo;
                                             str := "dstindex_nhop_reg" |})
                                         NoLocator)
                                        (TypSpecializedType
                                             (TypExtern
                                              {| stags := NoInfo;
                                                 str := "register" |})
                                             [(TypBit 16%N)]) Directionless)
                                   {| stags := NoInfo; str := "write" |})
                              (TypFunction
                               (MkFunctionType nil
                                    [(MkParameter false In (TypBit 32%N) 
                                          None
                                          {| stags := NoInfo;
                                             str := "index" |});
                                     (MkParameter false In (TypBit 16%N) 
                                          None
                                          {| stags := NoInfo;
                                             str := "value" |})] FunExtern
                                    TypVoid)) Directionless) nil
                         [(Some
                           (MkExpression NoInfo
                                (ExpName
                                 (BareName
                                  {| stags := NoInfo; str := "index" |})
                                 NoLocator) (TypBit 32%N) In));
                          (Some
                           (MkExpression NoInfo
                                (ExpCast (TypBit 16%N)
                                     (MkExpression NoInfo
                                          (ExpExpressionMember
                                               (MkExpression NoInfo
                                                    (ExpName
                                                     (BareName
                                                      {| stags := NoInfo;
                                                         str := "standard_metadata" |})
                                                     NoLocator)
                                                    (TypTypeName
                                                     {| stags := NoInfo;
                                                        str := "standard_metadata_t" |})
                                                    InOut)
                                               {| stags := NoInfo;
                                                  str := "ingress_port" |})
                                          (TypBit 9%N) Directionless))
                                (TypBit 16%N) Directionless))]) StmUnit)
               (BlockEmpty NoInfo)));
     (DeclAction NoInfo {| stags := NoInfo; str := "hula_get_nhop" |} nil
          [(MkParameter false Directionless (TypBit 32%N) None
                {| stags := NoInfo; str := "index" |})]
          (BlockCons
               (MkStatement NoInfo
                    (StatVariable (TypBit 16%N)
                         {| stags := NoInfo; str := "tmp" |} None NoLocator)
                    StmUnit)
               (BlockCons
                    (MkStatement NoInfo
                         (StatMethodCall
                              (MkExpression NoInfo
                                   (ExpExpressionMember
                                        (MkExpression NoInfo
                                             (ExpName
                                              (BareName
                                               {| stags := NoInfo;
                                                  str := "dstindex_nhop_reg" |})
                                              NoLocator)
                                             (TypSpecializedType
                                                  (TypExtern
                                                   {| stags := NoInfo;
                                                      str := "register" |})
                                                  [(TypBit 16%N)])
                                             Directionless)
                                        {| stags := NoInfo; str := "read" |})
                                   (TypFunction
                                    (MkFunctionType nil
                                         [(MkParameter false Out
                                               (TypBit 16%N) None
                                               {| stags := NoInfo;
                                                  str := "result" |});
                                          (MkParameter false In (TypBit 32%N)
                                               None
                                               {| stags := NoInfo;
                                                  str := "index" |})]
                                         FunExtern TypVoid)) Directionless)
                              nil
                              [(Some
                                (MkExpression NoInfo
                                     (ExpName
                                      (BareName
                                       {| stags := NoInfo; str := "tmp" |})
                                      NoLocator) (TypBit 16%N) InOut));
                               (Some
                                (MkExpression NoInfo
                                     (ExpName
                                      (BareName
                                       {| stags := NoInfo; str := "index" |})
                                      NoLocator) (TypBit 32%N) In))])
                         StmUnit)
                    (BlockCons
                         (MkStatement NoInfo
                              (StatAssignment
                                   (MkExpression NoInfo
                                        (ExpExpressionMember
                                             (MkExpression NoInfo
                                                  (ExpName
                                                   (BareName
                                                    {| stags := NoInfo;
                                                       str := "standard_metadata" |})
                                                   NoLocator)
                                                  (TypTypeName
                                                   {| stags := NoInfo;
                                                      str := "standard_metadata_t" |})
                                                  InOut)
                                             {| stags := NoInfo;
                                                str := "egress_spec" |})
                                        (TypBit 9%N) Directionless)
                                   (MkExpression NoInfo
                                        (ExpCast (TypBit 9%N)
                                             (MkExpression NoInfo
                                                  (ExpName
                                                   (BareName
                                                    {| stags := NoInfo;
                                                       str := "tmp" |})
                                                   NoLocator) (TypBit 16%N)
                                                  InOut)) (TypBit 9%N)
                                        Directionless)) StmUnit)
                         (BlockEmpty NoInfo)))));
     (DeclAction NoInfo
          {| stags := NoInfo; str := "change_best_path_at_dst" |} nil nil
          (BlockCons
               (MkStatement NoInfo
                    (StatMethodCall
                         (MkExpression NoInfo
                              (ExpExpressionMember
                                   (MkExpression NoInfo
                                        (ExpName
                                         (BareName
                                          {| stags := NoInfo;
                                             str := "srcindex_qdepth_reg" |})
                                         NoLocator)
                                        (TypSpecializedType
                                             (TypExtern
                                              {| stags := NoInfo;
                                                 str := "register" |})
                                             [(TypBit 15%N)]) Directionless)
                                   {| stags := NoInfo; str := "write" |})
                              (TypFunction
                               (MkFunctionType nil
                                    [(MkParameter false In (TypBit 32%N) 
                                          None
                                          {| stags := NoInfo;
                                             str := "index" |});
                                     (MkParameter false In (TypBit 15%N) 
                                          None
                                          {| stags := NoInfo;
                                             str := "value" |})] FunExtern
                                    TypVoid)) Directionless) nil
                         [(Some
                           (MkExpression NoInfo
                                (ExpExpressionMember
                                     (MkExpression NoInfo
                                          (ExpName
                                           (BareName
                                            {| stags := NoInfo;
                                               str := "meta" |}) NoLocator)
                                          (TypTypeName
                                           {| stags := NoInfo;
                                              str := "metadata" |}) InOut)
                                     {| stags := NoInfo; str := "index" |})
                                (TypBit 32%N) Directionless));
                          (Some
                           (MkExpression NoInfo
                                (ExpExpressionMember
                                     (MkExpression NoInfo
                                          (ExpExpressionMember
                                               (MkExpression NoInfo
                                                    (ExpName
                                                     (BareName
                                                      {| stags := NoInfo;
                                                         str := "hdr" |})
                                                     NoLocator)
                                                    (TypTypeName
                                                     {| stags := NoInfo;
                                                        str := "headers" |})
                                                    InOut)
                                               {| stags := NoInfo;
                                                  str := "hula" |})
                                          (TypHeader
                                           [( {| stags := NoInfo;
                                                 str := "dir" |},
                                              (TypBit 1%N) );
                                            ( {| stags := NoInfo;
                                                 str := "qdepth" |},
                                              (TypBit 15%N) );
                                            ( {| stags := NoInfo;
                                                 str := "digest" |},
                                              (TypBit 32%N) )])
                                          Directionless)
                                     {| stags := NoInfo; str := "qdepth" |})
                                (TypBit 15%N) Directionless))]) StmUnit)
               (BlockCons
                    (MkStatement NoInfo
                         (StatMethodCall
                              (MkExpression NoInfo
                                   (ExpExpressionMember
                                        (MkExpression NoInfo
                                             (ExpName
                                              (BareName
                                               {| stags := NoInfo;
                                                  str := "srcindex_digest_reg" |})
                                              NoLocator)
                                             (TypSpecializedType
                                                  (TypExtern
                                                   {| stags := NoInfo;
                                                      str := "register" |})
                                                  [(TypBit 32%N)])
                                             Directionless)
                                        {| stags := NoInfo; str := "write" |})
                                   (TypFunction
                                    (MkFunctionType nil
                                         [(MkParameter false In (TypBit 32%N)
                                               None
                                               {| stags := NoInfo;
                                                  str := "index" |});
                                          (MkParameter false In (TypBit 32%N)
                                               None
                                               {| stags := NoInfo;
                                                  str := "value" |})]
                                         FunExtern TypVoid)) Directionless)
                              nil
                              [(Some
                                (MkExpression NoInfo
                                     (ExpExpressionMember
                                          (MkExpression NoInfo
                                               (ExpName
                                                (BareName
                                                 {| stags := NoInfo;
                                                    str := "meta" |})
                                                NoLocator)
                                               (TypTypeName
                                                {| stags := NoInfo;
                                                   str := "metadata" |})
                                               InOut)
                                          {| stags := NoInfo;
                                             str := "index" |}) (TypBit 32%N)
                                     Directionless));
                               (Some
                                (MkExpression NoInfo
                                     (ExpExpressionMember
                                          (MkExpression NoInfo
                                               (ExpExpressionMember
                                                    (MkExpression NoInfo
                                                         (ExpName
                                                          (BareName
                                                           {| stags := NoInfo;
                                                              str := "hdr" |})
                                                          NoLocator)
                                                         (TypTypeName
                                                          {| stags := NoInfo;
                                                             str := "headers" |})
                                                         InOut)
                                                    {| stags := NoInfo;
                                                       str := "hula" |})
                                               (TypHeader
                                                [( {| stags := NoInfo;
                                                      str := "dir" |},
                                                   (TypBit 1%N) );
                                                 ( {| stags := NoInfo;
                                                      str := "qdepth" |},
                                                   (TypBit 15%N) );
                                                 ( {| stags := NoInfo;
                                                      str := "digest" |},
                                                   (TypBit 32%N) )])
                                               Directionless)
                                          {| stags := NoInfo;
                                             str := "digest" |})
                                     (TypBit 32%N) Directionless))]) StmUnit)
                    (BlockEmpty NoInfo))));
     (DeclAction NoInfo {| stags := NoInfo; str := "return_hula_to_src" |}
          nil nil
          (BlockCons
               (MkStatement NoInfo
                    (StatAssignment
                         (MkExpression NoInfo
                              (ExpExpressionMember
                                   (MkExpression NoInfo
                                        (ExpExpressionMember
                                             (MkExpression NoInfo
                                                  (ExpName
                                                   (BareName
                                                    {| stags := NoInfo;
                                                       str := "hdr" |})
                                                   NoLocator)
                                                  (TypTypeName
                                                   {| stags := NoInfo;
                                                      str := "headers" |})
                                                  InOut)
                                             {| stags := NoInfo;
                                                str := "hula" |})
                                        (TypHeader
                                         [( {| stags := NoInfo;
                                               str := "dir" |},
                                            (TypBit 1%N) );
                                          ( {| stags := NoInfo;
                                               str := "qdepth" |},
                                            (TypBit 15%N) );
                                          ( {| stags := NoInfo;
                                               str := "digest" |},
                                            (TypBit 32%N) )]) Directionless)
                                   {| stags := NoInfo; str := "dir" |})
                              (TypBit 1%N) Directionless)
                         (MkExpression NoInfo
                              (ExpInt
                               {| itags := NoInfo; value := 1;
                                  width_signed := (Some ( 1%N, false )) |})
                              (TypBit 1%N) Directionless)) StmUnit)
               (BlockCons
                    (MkStatement NoInfo
                         (StatAssignment
                              (MkExpression NoInfo
                                   (ExpExpressionMember
                                        (MkExpression NoInfo
                                             (ExpName
                                              (BareName
                                               {| stags := NoInfo;
                                                  str := "standard_metadata" |})
                                              NoLocator)
                                             (TypTypeName
                                              {| stags := NoInfo;
                                                 str := "standard_metadata_t" |})
                                             InOut)
                                        {| stags := NoInfo;
                                           str := "egress_spec" |})
                                   (TypBit 9%N) Directionless)
                              (MkExpression NoInfo
                                   (ExpExpressionMember
                                        (MkExpression NoInfo
                                             (ExpName
                                              (BareName
                                               {| stags := NoInfo;
                                                  str := "standard_metadata" |})
                                              NoLocator)
                                             (TypTypeName
                                              {| stags := NoInfo;
                                                 str := "standard_metadata_t" |})
                                             InOut)
                                        {| stags := NoInfo;
                                           str := "ingress_port" |})
                                   (TypBit 9%N) Directionless)) StmUnit)
                    (BlockEmpty NoInfo))));
     (DeclTable NoInfo {| stags := NoInfo; str := "hula_fwd" |}
          [(MkTableKey NoInfo
                (MkExpression NoInfo
                     (ExpExpressionMember
                          (MkExpression NoInfo
                               (ExpExpressionMember
                                    (MkExpression NoInfo
                                         (ExpName
                                          (BareName
                                           {| stags := NoInfo;
                                              str := "hdr" |}) NoLocator)
                                         (TypTypeName
                                          {| stags := NoInfo;
                                             str := "headers" |}) InOut)
                                    {| stags := NoInfo; str := "ipv4" |})
                               (TypHeader
                                [( {| stags := NoInfo; str := "version" |},
                                   (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "ihl" |},
                                   (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "diffserv" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo; str := "totalLen" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo;
                                      str := "identification" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "flags" |},
                                   (TypBit 3%N) );
                                 ( {| stags := NoInfo; str := "fragOffset" |},
                                   (TypBit 13%N) );
                                 ( {| stags := NoInfo; str := "ttl" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo; str := "protocol" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo;
                                      str := "hdrChecksum" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "srcAddr" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "dstAddr" |},
                                   (TypBit 32%N) )]) Directionless)
                          {| stags := NoInfo; str := "dstAddr" |})
                     (TypBit 32%N) Directionless)
                {| stags := NoInfo; str := "exact" |});
           (MkTableKey NoInfo
                (MkExpression NoInfo
                     (ExpExpressionMember
                          (MkExpression NoInfo
                               (ExpExpressionMember
                                    (MkExpression NoInfo
                                         (ExpName
                                          (BareName
                                           {| stags := NoInfo;
                                              str := "hdr" |}) NoLocator)
                                         (TypTypeName
                                          {| stags := NoInfo;
                                             str := "headers" |}) InOut)
                                    {| stags := NoInfo; str := "ipv4" |})
                               (TypHeader
                                [( {| stags := NoInfo; str := "version" |},
                                   (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "ihl" |},
                                   (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "diffserv" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo; str := "totalLen" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo;
                                      str := "identification" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "flags" |},
                                   (TypBit 3%N) );
                                 ( {| stags := NoInfo; str := "fragOffset" |},
                                   (TypBit 13%N) );
                                 ( {| stags := NoInfo; str := "ttl" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo; str := "protocol" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo;
                                      str := "hdrChecksum" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "srcAddr" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "dstAddr" |},
                                   (TypBit 32%N) )]) Directionless)
                          {| stags := NoInfo; str := "srcAddr" |})
                     (TypBit 32%N) Directionless)
                {| stags := NoInfo; str := "exact" |})]
          [(MkTableActionRef NoInfo
                (MkTablePreActionRef
                     (BareName {| stags := NoInfo; str := "hula_dst" |}) nil)
                (TypAction nil
                     [(MkParameter false Directionless (TypBit 32%N) 
                           None {| stags := NoInfo; str := "index" |})]));
           (MkTableActionRef NoInfo
                (MkTablePreActionRef
                     (BareName {| stags := NoInfo; str := "srcRoute_nhop" |})
                     nil) (TypAction nil nil))] None
          (Some
           (MkTableActionRef NoInfo
                (MkTablePreActionRef
                     (BareName {| stags := NoInfo; str := "srcRoute_nhop" |})
                     nil) (TypAction nil nil))) (Some 33%N) nil);
     (DeclTable NoInfo {| stags := NoInfo; str := "hula_bwd" |}
          [(MkTableKey NoInfo
                (MkExpression NoInfo
                     (ExpExpressionMember
                          (MkExpression NoInfo
                               (ExpExpressionMember
                                    (MkExpression NoInfo
                                         (ExpName
                                          (BareName
                                           {| stags := NoInfo;
                                              str := "hdr" |}) NoLocator)
                                         (TypTypeName
                                          {| stags := NoInfo;
                                             str := "headers" |}) InOut)
                                    {| stags := NoInfo; str := "ipv4" |})
                               (TypHeader
                                [( {| stags := NoInfo; str := "version" |},
                                   (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "ihl" |},
                                   (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "diffserv" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo; str := "totalLen" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo;
                                      str := "identification" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "flags" |},
                                   (TypBit 3%N) );
                                 ( {| stags := NoInfo; str := "fragOffset" |},
                                   (TypBit 13%N) );
                                 ( {| stags := NoInfo; str := "ttl" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo; str := "protocol" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo;
                                      str := "hdrChecksum" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "srcAddr" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "dstAddr" |},
                                   (TypBit 32%N) )]) Directionless)
                          {| stags := NoInfo; str := "dstAddr" |})
                     (TypBit 32%N) Directionless)
                {| stags := NoInfo; str := "lpm" |})]
          [(MkTableActionRef NoInfo
                (MkTablePreActionRef
                     (BareName {| stags := NoInfo; str := "hula_set_nhop" |})
                     nil)
                (TypAction nil
                     [(MkParameter false Directionless (TypBit 32%N) 
                           None {| stags := NoInfo; str := "index" |})]))]
          None None (Some 32%N) nil);
     (DeclTable NoInfo {| stags := NoInfo; str := "hula_src" |}
          [(MkTableKey NoInfo
                (MkExpression NoInfo
                     (ExpExpressionMember
                          (MkExpression NoInfo
                               (ExpExpressionMember
                                    (MkExpression NoInfo
                                         (ExpName
                                          (BareName
                                           {| stags := NoInfo;
                                              str := "hdr" |}) NoLocator)
                                         (TypTypeName
                                          {| stags := NoInfo;
                                             str := "headers" |}) InOut)
                                    {| stags := NoInfo; str := "ipv4" |})
                               (TypHeader
                                [( {| stags := NoInfo; str := "version" |},
                                   (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "ihl" |},
                                   (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "diffserv" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo; str := "totalLen" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo;
                                      str := "identification" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "flags" |},
                                   (TypBit 3%N) );
                                 ( {| stags := NoInfo; str := "fragOffset" |},
                                   (TypBit 13%N) );
                                 ( {| stags := NoInfo; str := "ttl" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo; str := "protocol" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo;
                                      str := "hdrChecksum" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "srcAddr" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "dstAddr" |},
                                   (TypBit 32%N) )]) Directionless)
                          {| stags := NoInfo; str := "srcAddr" |})
                     (TypBit 32%N) Directionless)
                {| stags := NoInfo; str := "exact" |})]
          [(MkTableActionRef NoInfo
                (MkTablePreActionRef
                     (BareName {| stags := NoInfo; str := "drop" |}) nil)
                (TypAction nil nil));
           (MkTableActionRef NoInfo
                (MkTablePreActionRef
                     (BareName {| stags := NoInfo; str := "srcRoute_nhop" |})
                     nil) (TypAction nil nil))] None
          (Some
           (MkTableActionRef NoInfo
                (MkTablePreActionRef
                     (BareName {| stags := NoInfo; str := "srcRoute_nhop" |})
                     nil) (TypAction nil nil))) (Some 2%N) nil);
     (DeclTable NoInfo {| stags := NoInfo; str := "hula_nhop" |}
          [(MkTableKey NoInfo
                (MkExpression NoInfo
                     (ExpExpressionMember
                          (MkExpression NoInfo
                               (ExpExpressionMember
                                    (MkExpression NoInfo
                                         (ExpName
                                          (BareName
                                           {| stags := NoInfo;
                                              str := "hdr" |}) NoLocator)
                                         (TypTypeName
                                          {| stags := NoInfo;
                                             str := "headers" |}) InOut)
                                    {| stags := NoInfo; str := "ipv4" |})
                               (TypHeader
                                [( {| stags := NoInfo; str := "version" |},
                                   (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "ihl" |},
                                   (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "diffserv" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo; str := "totalLen" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo;
                                      str := "identification" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "flags" |},
                                   (TypBit 3%N) );
                                 ( {| stags := NoInfo; str := "fragOffset" |},
                                   (TypBit 13%N) );
                                 ( {| stags := NoInfo; str := "ttl" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo; str := "protocol" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo;
                                      str := "hdrChecksum" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "srcAddr" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "dstAddr" |},
                                   (TypBit 32%N) )]) Directionless)
                          {| stags := NoInfo; str := "dstAddr" |})
                     (TypBit 32%N) Directionless)
                {| stags := NoInfo; str := "lpm" |})]
          [(MkTableActionRef NoInfo
                (MkTablePreActionRef
                     (BareName {| stags := NoInfo; str := "hula_get_nhop" |})
                     nil)
                (TypAction nil
                     [(MkParameter false Directionless (TypBit 32%N) 
                           None {| stags := NoInfo; str := "index" |})]));
           (MkTableActionRef NoInfo
                (MkTablePreActionRef
                     (BareName {| stags := NoInfo; str := "drop" |}) nil)
                (TypAction nil nil))] None
          (Some
           (MkTableActionRef NoInfo
                (MkTablePreActionRef
                     (BareName {| stags := NoInfo; str := "drop" |}) nil)
                (TypAction nil nil))) (Some 32%N) nil);
     (DeclTable NoInfo {| stags := NoInfo; str := "dmac" |}
          [(MkTableKey NoInfo
                (MkExpression NoInfo
                     (ExpExpressionMember
                          (MkExpression NoInfo
                               (ExpName
                                (BareName
                                 {| stags := NoInfo;
                                    str := "standard_metadata" |}) NoLocator)
                               (TypTypeName
                                {| stags := NoInfo;
                                   str := "standard_metadata_t" |}) InOut)
                          {| stags := NoInfo; str := "egress_spec" |})
                     (TypBit 9%N) Directionless)
                {| stags := NoInfo; str := "exact" |})]
          [(MkTableActionRef NoInfo
                (MkTablePreActionRef
                     (BareName {| stags := NoInfo; str := "set_dmac" |}) nil)
                (TypAction nil
                     [(MkParameter false Directionless
                           (TypTypeName
                            {| stags := NoInfo; str := "macAddr_t" |}) 
                           None {| stags := NoInfo; str := "dstAddr" |})]));
           (MkTableActionRef NoInfo
                (MkTablePreActionRef
                     (BareName {| stags := NoInfo; str := "nop" |}) nil)
                (TypAction nil nil))] None
          (Some
           (MkTableActionRef NoInfo
                (MkTablePreActionRef
                     (BareName {| stags := NoInfo; str := "nop" |}) nil)
                (TypAction nil nil))) (Some 16%N) nil)]
    (BlockCons
         (MkStatement NoInfo
              (StatConditional
                   (MkExpression NoInfo
                        (ExpFunctionCall
                             (MkExpression NoInfo
                                  (ExpExpressionMember
                                       (MkExpression NoInfo
                                            (ExpExpressionMember
                                                 (MkExpression NoInfo
                                                      (ExpName
                                                       (BareName
                                                        {| stags := NoInfo;
                                                           str := "hdr" |})
                                                       NoLocator)
                                                      (TypTypeName
                                                       {| stags := NoInfo;
                                                          str := "headers" |})
                                                      InOut)
                                                 {| stags := NoInfo;
                                                    str := "hula" |})
                                            (TypHeader
                                             [( {| stags := NoInfo;
                                                   str := "dir" |},
                                                (TypBit 1%N) );
                                              ( {| stags := NoInfo;
                                                   str := "qdepth" |},
                                                (TypBit 15%N) );
                                              ( {| stags := NoInfo;
                                                   str := "digest" |},
                                                (TypBit 32%N) )])
                                            Directionless)
                                       {| stags := NoInfo;
                                          str := "isValid" |})
                                  (TypFunction
                                   (MkFunctionType nil nil FunBuiltin
                                        TypBool)) Directionless) nil nil)
                        TypBool Directionless)
                   (MkStatement NoInfo
                        (StatBlock
                         (BlockCons
                              (MkStatement NoInfo
                                   (StatConditional
                                        (MkExpression NoInfo
                                             (ExpBinaryOp Eq
                                                  ( (MkExpression NoInfo
                                                         (ExpExpressionMember
                                                              (MkExpression
                                                                   NoInfo
                                                                   (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "hdr" |})
                                                                    NoLocator)
                                                                    (TypTypeName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "headers" |})
                                                                    InOut)
                                                                    {| stags := NoInfo;
                                                                    str := "hula" |})
                                                                   (TypHeader
                                                                    [
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "dir" |},
                                                                    (
                                                                    TypBit
                                                                    1%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "qdepth" |},
                                                                    (
                                                                    TypBit
                                                                    15%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "digest" |},
                                                                    (
                                                                    TypBit
                                                                    32%N) )])
                                                                   Directionless)
                                                              {| stags := NoInfo;
                                                                 str := "dir" |})
                                                         (TypBit 1%N)
                                                         Directionless),
                                                    (MkExpression NoInfo
                                                         (ExpCast
                                                              (TypBit 1%N)
                                                              (MkExpression
                                                                   NoInfo
                                                                   (ExpInt
                                                                    {| 
                                                                    itags := NoInfo;
                                                                    value := 0;
                                                                    width_signed := 
                                                                    None |})
                                                                   TypInteger
                                                                   Directionless))
                                                         (TypBit 1%N)
                                                         Directionless) ))
                                             TypBool Directionless)
                                        (MkStatement NoInfo
                                             (StatBlock
                                              (BlockCons
                                                   (MkStatement NoInfo
                                                        (StatSwitch
                                                             (MkExpression
                                                                  NoInfo
                                                                  (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpFunctionCall
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "hula_fwd" |})
                                                                    NoLocator)
                                                                    (TypTable
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "apply_result_hula_fwd" |})
                                                                    Directionless)
                                                                    {| stags := NoInfo;
                                                                    str := "apply" |})
                                                                    (TypFunction
                                                                    (MkFunctionType
                                                                    nil nil
                                                                    FunTable
                                                                    (TypTypeName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "apply_result_hula_fwd" |})))
                                                                    Directionless)
                                                                    nil nil)
                                                                    (TypStruct
                                                                    [( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "hit" |},
                                                                    TypBool );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "miss" |},
                                                                    TypBool );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "action_run" |},
                                                                    (
                                                                    TypEnum
                                                                    {| stags := NoInfo;
                                                                    str := "action_list_hula_fwd" |}
                                                                    None
                                                                    [{| 
                                                                    stags := NoInfo;
                                                                    str := "hula_dst" |};
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "srcRoute_nhop" |}]) )])
                                                                    Directionless)
                                                                    {| stags := NoInfo;
                                                                    str := "action_run" |})
                                                                  (TypEnum
                                                                    {| stags := NoInfo;
                                                                    str := "action_list_hula_fwd" |}
                                                                    None
                                                                    [{| 
                                                                    stags := NoInfo;
                                                                    str := "hula_dst" |};
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "srcRoute_nhop" |}])
                                                                  Directionless)
                                                             [(StatSwCaseAction
                                                                   NoInfo
                                                                   (StatSwLabName
                                                                    NoInfo
                                                                    {| stags := NoInfo;
                                                                    str := "hula_dst" |})
                                                                   (BlockCons
                                                                    (MkStatement
                                                                    NoInfo
                                                                    (StatVariable
                                                                    (TypTypeName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "qdepth_t" |})
                                                                    {| stags := NoInfo;
                                                                    str := "old_qdepth" |}
                                                                    None
                                                                    NoLocator)
                                                                    StmUnit)
                                                                    (BlockCons
                                                                    (MkStatement
                                                                    NoInfo
                                                                    (StatMethodCall
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "srcindex_qdepth_reg" |})
                                                                    NoLocator)
                                                                    (TypSpecializedType
                                                                    (TypExtern
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "register" |})
                                                                    [(
                                                                    TypBit
                                                                    15%N)])
                                                                    Directionless)
                                                                    {| stags := NoInfo;
                                                                    str := "read" |})
                                                                    (TypFunction
                                                                    (MkFunctionType
                                                                    nil
                                                                    [(
                                                                    MkParameter
                                                                    false Out
                                                                    (TypBit
                                                                    15%N)
                                                                    None
                                                                    {| stags := NoInfo;
                                                                    str := "result" |});
                                                                    (MkParameter
                                                                    false In
                                                                    (TypBit
                                                                    32%N)
                                                                    None
                                                                    {| stags := NoInfo;
                                                                    str := "index" |})]
                                                                    FunExtern
                                                                    TypVoid))
                                                                    Directionless)
                                                                    nil
                                                                    [(
                                                                    Some
                                                                    (
                                                                    MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "old_qdepth" |})
                                                                    NoLocator)
                                                                    (TypTypeName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "qdepth_t" |})
                                                                    InOut));
                                                                    (Some
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "meta" |})
                                                                    NoLocator)
                                                                    (TypTypeName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "metadata" |})
                                                                    InOut)
                                                                    {| stags := NoInfo;
                                                                    str := "index" |})
                                                                    (TypBit
                                                                    32%N)
                                                                    Directionless))])
                                                                    StmUnit)
                                                                    (BlockCons
                                                                    (MkStatement
                                                                    NoInfo
                                                                    (StatConditional
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpBinaryOp
                                                                    Gt
                                                                    ( (
                                                                    MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "old_qdepth" |})
                                                                    NoLocator)
                                                                    (TypTypeName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "qdepth_t" |})
                                                                    InOut),
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "hdr" |})
                                                                    NoLocator)
                                                                    (TypTypeName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "headers" |})
                                                                    InOut)
                                                                    {| stags := NoInfo;
                                                                    str := "hula" |})
                                                                    (TypHeader
                                                                    [( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "dir" |},
                                                                    (
                                                                    TypBit
                                                                    1%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "qdepth" |},
                                                                    (
                                                                    TypBit
                                                                    15%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "digest" |},
                                                                    (
                                                                    TypBit
                                                                    32%N) )])
                                                                    Directionless)
                                                                    {| stags := NoInfo;
                                                                    str := "qdepth" |})
                                                                    (TypBit
                                                                    15%N)
                                                                    Directionless) ))
                                                                    TypBool
                                                                    Directionless)
                                                                    (MkStatement
                                                                    NoInfo
                                                                    (StatBlock
                                                                    (BlockCons
                                                                    (MkStatement
                                                                    NoInfo
                                                                    (StatMethodCall
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "change_best_path_at_dst" |})
                                                                    NoLocator)
                                                                    (TypAction
                                                                    nil nil)
                                                                    Directionless)
                                                                    nil nil)
                                                                    StmUnit)
                                                                    (BlockCons
                                                                    (MkStatement
                                                                    NoInfo
                                                                    (StatMethodCall
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "return_hula_to_src" |})
                                                                    NoLocator)
                                                                    (TypAction
                                                                    nil nil)
                                                                    Directionless)
                                                                    nil nil)
                                                                    StmUnit)
                                                                    (BlockEmpty
                                                                    NoInfo))))
                                                                    StmUnit)
                                                                    (Some
                                                                    (MkStatement
                                                                    NoInfo
                                                                    (StatBlock
                                                                    (BlockCons
                                                                    (MkStatement
                                                                    NoInfo
                                                                    (StatVariable
                                                                    (TypTypeName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "digest_t" |})
                                                                    {| stags := NoInfo;
                                                                    str := "old_digest" |}
                                                                    None
                                                                    NoLocator)
                                                                    StmUnit)
                                                                    (BlockCons
                                                                    (MkStatement
                                                                    NoInfo
                                                                    (StatMethodCall
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "srcindex_digest_reg" |})
                                                                    NoLocator)
                                                                    (TypSpecializedType
                                                                    (TypExtern
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "register" |})
                                                                    [(
                                                                    TypBit
                                                                    32%N)])
                                                                    Directionless)
                                                                    {| stags := NoInfo;
                                                                    str := "read" |})
                                                                    (TypFunction
                                                                    (MkFunctionType
                                                                    nil
                                                                    [(
                                                                    MkParameter
                                                                    false Out
                                                                    (TypBit
                                                                    32%N)
                                                                    None
                                                                    {| stags := NoInfo;
                                                                    str := "result" |});
                                                                    (MkParameter
                                                                    false In
                                                                    (TypBit
                                                                    32%N)
                                                                    None
                                                                    {| stags := NoInfo;
                                                                    str := "index" |})]
                                                                    FunExtern
                                                                    TypVoid))
                                                                    Directionless)
                                                                    nil
                                                                    [(
                                                                    Some
                                                                    (
                                                                    MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "old_digest" |})
                                                                    NoLocator)
                                                                    (TypTypeName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "digest_t" |})
                                                                    InOut));
                                                                    (Some
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "meta" |})
                                                                    NoLocator)
                                                                    (TypTypeName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "metadata" |})
                                                                    InOut)
                                                                    {| stags := NoInfo;
                                                                    str := "index" |})
                                                                    (TypBit
                                                                    32%N)
                                                                    Directionless))])
                                                                    StmUnit)
                                                                    (BlockCons
                                                                    (MkStatement
                                                                    NoInfo
                                                                    (StatConditional
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpBinaryOp
                                                                    Eq
                                                                    ( (
                                                                    MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "old_digest" |})
                                                                    NoLocator)
                                                                    (TypTypeName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "digest_t" |})
                                                                    InOut),
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "hdr" |})
                                                                    NoLocator)
                                                                    (TypTypeName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "headers" |})
                                                                    InOut)
                                                                    {| stags := NoInfo;
                                                                    str := "hula" |})
                                                                    (TypHeader
                                                                    [( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "dir" |},
                                                                    (
                                                                    TypBit
                                                                    1%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "qdepth" |},
                                                                    (
                                                                    TypBit
                                                                    15%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "digest" |},
                                                                    (
                                                                    TypBit
                                                                    32%N) )])
                                                                    Directionless)
                                                                    {| stags := NoInfo;
                                                                    str := "digest" |})
                                                                    (TypBit
                                                                    32%N)
                                                                    Directionless) ))
                                                                    TypBool
                                                                    Directionless)
                                                                    (MkStatement
                                                                    NoInfo
                                                                    (StatBlock
                                                                    (BlockCons
                                                                    (MkStatement
                                                                    NoInfo
                                                                    (StatMethodCall
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "srcindex_qdepth_reg" |})
                                                                    NoLocator)
                                                                    (TypSpecializedType
                                                                    (TypExtern
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "register" |})
                                                                    [(
                                                                    TypBit
                                                                    15%N)])
                                                                    Directionless)
                                                                    {| stags := NoInfo;
                                                                    str := "write" |})
                                                                    (TypFunction
                                                                    (MkFunctionType
                                                                    nil
                                                                    [(
                                                                    MkParameter
                                                                    false In
                                                                    (TypBit
                                                                    32%N)
                                                                    None
                                                                    {| stags := NoInfo;
                                                                    str := "index" |});
                                                                    (MkParameter
                                                                    false In
                                                                    (TypBit
                                                                    15%N)
                                                                    None
                                                                    {| stags := NoInfo;
                                                                    str := "value" |})]
                                                                    FunExtern
                                                                    TypVoid))
                                                                    Directionless)
                                                                    nil
                                                                    [(
                                                                    Some
                                                                    (
                                                                    MkExpression
                                                                    NoInfo
                                                                    (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "meta" |})
                                                                    NoLocator)
                                                                    (TypTypeName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "metadata" |})
                                                                    InOut)
                                                                    {| stags := NoInfo;
                                                                    str := "index" |})
                                                                    (TypBit
                                                                    32%N)
                                                                    Directionless));
                                                                    (Some
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "hdr" |})
                                                                    NoLocator)
                                                                    (TypTypeName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "headers" |})
                                                                    InOut)
                                                                    {| stags := NoInfo;
                                                                    str := "hula" |})
                                                                    (TypHeader
                                                                    [( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "dir" |},
                                                                    (
                                                                    TypBit
                                                                    1%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "qdepth" |},
                                                                    (
                                                                    TypBit
                                                                    15%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "digest" |},
                                                                    (
                                                                    TypBit
                                                                    32%N) )])
                                                                    Directionless)
                                                                    {| stags := NoInfo;
                                                                    str := "qdepth" |})
                                                                    (TypBit
                                                                    15%N)
                                                                    Directionless))])
                                                                    StmUnit)
                                                                    (BlockEmpty
                                                                    NoInfo)))
                                                                    StmUnit)
                                                                    None)
                                                                    StmUnit)
                                                                    (BlockCons
                                                                    (MkStatement
                                                                    NoInfo
                                                                    (StatMethodCall
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "drop" |})
                                                                    NoLocator)
                                                                    (TypAction
                                                                    nil nil)
                                                                    Directionless)
                                                                    nil nil)
                                                                    StmUnit)
                                                                    (BlockEmpty
                                                                    NoInfo))))))
                                                                    StmUnit)))
                                                                    StmUnit)
                                                                    (BlockEmpty
                                                                    NoInfo)))))])
                                                        StmUnit)
                                                   (BlockEmpty NoInfo)))
                                             StmUnit)
                                        (Some
                                         (MkStatement NoInfo
                                              (StatBlock
                                               (BlockCons
                                                    (MkStatement NoInfo
                                                         (StatMethodCall
                                                              (MkExpression
                                                                   NoInfo
                                                                   (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "hula_bwd" |})
                                                                    NoLocator)
                                                                    (TypTable
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "apply_result_hula_bwd" |})
                                                                    Directionless)
                                                                    {| stags := NoInfo;
                                                                    str := "apply" |})
                                                                   (TypFunction
                                                                    (
                                                                    MkFunctionType
                                                                    nil nil
                                                                    FunTable
                                                                    (TypTypeName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "apply_result_hula_bwd" |})))
                                                                   Directionless)
                                                              nil nil)
                                                         StmUnit)
                                                    (BlockCons
                                                         (MkStatement NoInfo
                                                              (StatMethodCall
                                                                   (MkExpression
                                                                    NoInfo
                                                                    (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "hula_src" |})
                                                                    NoLocator)
                                                                    (TypTable
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "apply_result_hula_src" |})
                                                                    Directionless)
                                                                    {| stags := NoInfo;
                                                                    str := "apply" |})
                                                                    (TypFunction
                                                                    (MkFunctionType
                                                                    nil nil
                                                                    FunTable
                                                                    (TypTypeName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "apply_result_hula_src" |})))
                                                                    Directionless)
                                                                   nil nil)
                                                              StmUnit)
                                                         (BlockEmpty NoInfo))))
                                              StmUnit))) StmUnit)
                              (BlockEmpty NoInfo))) StmUnit)
                   (Some
                    (MkStatement NoInfo
                         (StatConditional
                              (MkExpression NoInfo
                                   (ExpFunctionCall
                                        (MkExpression NoInfo
                                             (ExpExpressionMember
                                                  (MkExpression NoInfo
                                                       (ExpExpressionMember
                                                            (MkExpression
                                                                 NoInfo
                                                                 (ExpName
                                                                  (BareName
                                                                   {| 
                                                                   stags := NoInfo;
                                                                   str := "hdr" |})
                                                                  NoLocator)
                                                                 (TypTypeName
                                                                  {| 
                                                                  stags := NoInfo;
                                                                  str := "headers" |})
                                                                 InOut)
                                                            {| stags := NoInfo;
                                                               str := "ipv4" |})
                                                       (TypHeader
                                                        [( {| stags := NoInfo;
                                                              str := "version" |},
                                                           (TypBit 4%N) );
                                                         ( {| stags := NoInfo;
                                                              str := "ihl" |},
                                                           (TypBit 4%N) );
                                                         ( {| stags := NoInfo;
                                                              str := "diffserv" |},
                                                           (TypBit 8%N) );
                                                         ( {| stags := NoInfo;
                                                              str := "totalLen" |},
                                                           (TypBit 16%N) );
                                                         ( {| stags := NoInfo;
                                                              str := "identification" |},
                                                           (TypBit 16%N) );
                                                         ( {| stags := NoInfo;
                                                              str := "flags" |},
                                                           (TypBit 3%N) );
                                                         ( {| stags := NoInfo;
                                                              str := "fragOffset" |},
                                                           (TypBit 13%N) );
                                                         ( {| stags := NoInfo;
                                                              str := "ttl" |},
                                                           (TypBit 8%N) );
                                                         ( {| stags := NoInfo;
                                                              str := "protocol" |},
                                                           (TypBit 8%N) );
                                                         ( {| stags := NoInfo;
                                                              str := "hdrChecksum" |},
                                                           (TypBit 16%N) );
                                                         ( {| stags := NoInfo;
                                                              str := "srcAddr" |},
                                                           (TypBit 32%N) );
                                                         ( {| stags := NoInfo;
                                                              str := "dstAddr" |},
                                                           (TypBit 32%N) )])
                                                       Directionless)
                                                  {| stags := NoInfo;
                                                     str := "isValid" |})
                                             (TypFunction
                                              (MkFunctionType nil nil
                                                   FunBuiltin TypBool))
                                             Directionless) nil nil) 
                                   TypBool Directionless)
                              (MkStatement NoInfo
                                   (StatBlock
                                    (BlockCons
                                         (MkStatement NoInfo
                                              (StatVariable (TypBit 16%N)
                                                   {| stags := NoInfo;
                                                      str := "flow_hash" |}
                                                   None NoLocator) StmUnit)
                                         (BlockCons
                                              (MkStatement NoInfo
                                                   (StatMethodCall
                                                        (MkExpression NoInfo
                                                             (ExpName
                                                              (BareName
                                                               {| stags := NoInfo;
                                                                  str := "hash" |})
                                                              NoLocator)
                                                             (TypFunction
                                                              (MkFunctionType
                                                                   [{| 
                                                                    stags := NoInfo;
                                                                    str := "O" |};
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "T8" |};
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "D" |};
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "M" |}]
                                                                   [(
                                                                    MkParameter
                                                                    false Out
                                                                    (TypTypeName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "O" |})
                                                                    None
                                                                    {| stags := NoInfo;
                                                                    str := "result" |});
                                                                    (
                                                                    MkParameter
                                                                    false In
                                                                    (TypTypeName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "HashAlgorithm" |})
                                                                    None
                                                                    {| stags := NoInfo;
                                                                    str := "algo" |});
                                                                    (
                                                                    MkParameter
                                                                    false In
                                                                    (TypTypeName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "T8" |})
                                                                    None
                                                                    {| stags := NoInfo;
                                                                    str := "base" |});
                                                                    (
                                                                    MkParameter
                                                                    false In
                                                                    (TypTypeName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "D" |})
                                                                    None
                                                                    {| stags := NoInfo;
                                                                    str := "data" |});
                                                                    (
                                                                    MkParameter
                                                                    false In
                                                                    (TypTypeName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "M" |})
                                                                    None
                                                                    {| stags := NoInfo;
                                                                    str := "max" |})]
                                                                   FunExtern
                                                                   TypVoid))
                                                             Directionless)
                                                        [(TypBit 16%N);
                                                         (TypBit 16%N);
                                                         (TypList
                                                          [(TypBit 32%N);
                                                           (TypBit 32%N);
                                                           (TypBit 16%N)]);
                                                         (TypBit 32%N)]
                                                        [(Some
                                                          (MkExpression
                                                               NoInfo
                                                               (ExpName
                                                                (BareName
                                                                 {| stags := NoInfo;
                                                                    str := "flow_hash" |})
                                                                NoLocator)
                                                               (TypBit 16%N)
                                                               InOut));
                                                         (Some
                                                          (MkExpression
                                                               NoInfo
                                                               (ExpTypeMember
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "HashAlgorithm" |}
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "crc16" |})
                                                               (TypEnum
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "HashAlgorithm" |}
                                                                    None
                                                                    [
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "crc32" |};
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "crc32_custom" |};
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "crc16" |};
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "crc16_custom" |};
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "random" |};
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "identity" |};
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "csum16" |};
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "xor16" |}])
                                                               Directionless));
                                                         (Some
                                                          (MkExpression
                                                               NoInfo
                                                               (ExpInt
                                                                {| itags := NoInfo;
                                                                   value := 0;
                                                                   width_signed := (
                                                                   Some
                                                                   ( 
                                                                   16%N,
                                                                   false )) |})
                                                               (TypBit 16%N)
                                                               Directionless));
                                                         (Some
                                                          (MkExpression
                                                               NoInfo
                                                               (ExpList
                                                                [(MkExpression
                                                                    NoInfo
                                                                    (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "hdr" |})
                                                                    NoLocator)
                                                                    (TypTypeName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "headers" |})
                                                                    InOut)
                                                                    {| stags := NoInfo;
                                                                    str := "ipv4" |})
                                                                    (TypHeader
                                                                    [( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "version" |},
                                                                    (
                                                                    TypBit
                                                                    4%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "ihl" |},
                                                                    (
                                                                    TypBit
                                                                    4%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "diffserv" |},
                                                                    (
                                                                    TypBit
                                                                    8%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "totalLen" |},
                                                                    (
                                                                    TypBit
                                                                    16%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "identification" |},
                                                                    (
                                                                    TypBit
                                                                    16%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "flags" |},
                                                                    (
                                                                    TypBit
                                                                    3%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "fragOffset" |},
                                                                    (
                                                                    TypBit
                                                                    13%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "ttl" |},
                                                                    (
                                                                    TypBit
                                                                    8%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "protocol" |},
                                                                    (
                                                                    TypBit
                                                                    8%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "hdrChecksum" |},
                                                                    (
                                                                    TypBit
                                                                    16%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "srcAddr" |},
                                                                    (
                                                                    TypBit
                                                                    32%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "dstAddr" |},
                                                                    (
                                                                    TypBit
                                                                    32%N) )])
                                                                    Directionless)
                                                                    {| stags := NoInfo;
                                                                    str := "srcAddr" |})
                                                                    (TypBit
                                                                    32%N)
                                                                    Directionless);
                                                                 (MkExpression
                                                                    NoInfo
                                                                    (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "hdr" |})
                                                                    NoLocator)
                                                                    (TypTypeName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "headers" |})
                                                                    InOut)
                                                                    {| stags := NoInfo;
                                                                    str := "ipv4" |})
                                                                    (TypHeader
                                                                    [( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "version" |},
                                                                    (
                                                                    TypBit
                                                                    4%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "ihl" |},
                                                                    (
                                                                    TypBit
                                                                    4%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "diffserv" |},
                                                                    (
                                                                    TypBit
                                                                    8%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "totalLen" |},
                                                                    (
                                                                    TypBit
                                                                    16%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "identification" |},
                                                                    (
                                                                    TypBit
                                                                    16%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "flags" |},
                                                                    (
                                                                    TypBit
                                                                    3%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "fragOffset" |},
                                                                    (
                                                                    TypBit
                                                                    13%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "ttl" |},
                                                                    (
                                                                    TypBit
                                                                    8%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "protocol" |},
                                                                    (
                                                                    TypBit
                                                                    8%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "hdrChecksum" |},
                                                                    (
                                                                    TypBit
                                                                    16%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "srcAddr" |},
                                                                    (
                                                                    TypBit
                                                                    32%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "dstAddr" |},
                                                                    (
                                                                    TypBit
                                                                    32%N) )])
                                                                    Directionless)
                                                                    {| stags := NoInfo;
                                                                    str := "dstAddr" |})
                                                                    (TypBit
                                                                    32%N)
                                                                    Directionless);
                                                                 (MkExpression
                                                                    NoInfo
                                                                    (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "hdr" |})
                                                                    NoLocator)
                                                                    (TypTypeName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "headers" |})
                                                                    InOut)
                                                                    {| stags := NoInfo;
                                                                    str := "udp" |})
                                                                    (TypHeader
                                                                    [( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "srcPort" |},
                                                                    (
                                                                    TypBit
                                                                    16%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "dstPort" |},
                                                                    (
                                                                    TypBit
                                                                    16%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "length_" |},
                                                                    (
                                                                    TypBit
                                                                    16%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "checksum" |},
                                                                    (
                                                                    TypBit
                                                                    16%N) )])
                                                                    Directionless)
                                                                    {| stags := NoInfo;
                                                                    str := "srcPort" |})
                                                                    (TypBit
                                                                    16%N)
                                                                    Directionless)])
                                                               (TypList
                                                                [(TypBit
                                                                  32%N);
                                                                 (TypBit
                                                                  32%N);
                                                                 (TypBit
                                                                  16%N)])
                                                               Directionless));
                                                         (Some
                                                          (MkExpression
                                                               NoInfo
                                                               (ExpInt
                                                                {| itags := NoInfo;
                                                                   value := 65536;
                                                                   width_signed := (
                                                                   Some
                                                                   ( 
                                                                   32%N,
                                                                   false )) |})
                                                               (TypBit 32%N)
                                                               Directionless))])
                                                   StmUnit)
                                              (BlockCons
                                                   (MkStatement NoInfo
                                                        (StatVariable
                                                             (TypBit 16%N)
                                                             {| stags := NoInfo;
                                                                str := "port" |}
                                                             None NoLocator)
                                                        StmUnit)
                                                   (BlockCons
                                                        (MkStatement NoInfo
                                                             (StatMethodCall
                                                                  (MkExpression
                                                                    NoInfo
                                                                    (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "flow_port_reg" |})
                                                                    NoLocator)
                                                                    (TypSpecializedType
                                                                    (TypExtern
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "register" |})
                                                                    [(
                                                                    TypBit
                                                                    16%N)])
                                                                    Directionless)
                                                                    {| stags := NoInfo;
                                                                    str := "read" |})
                                                                    (TypFunction
                                                                    (MkFunctionType
                                                                    nil
                                                                    [(
                                                                    MkParameter
                                                                    false Out
                                                                    (TypBit
                                                                    16%N)
                                                                    None
                                                                    {| stags := NoInfo;
                                                                    str := "result" |});
                                                                    (MkParameter
                                                                    false In
                                                                    (TypBit
                                                                    32%N)
                                                                    None
                                                                    {| stags := NoInfo;
                                                                    str := "index" |})]
                                                                    FunExtern
                                                                    TypVoid))
                                                                    Directionless)
                                                                  nil
                                                                  [(Some
                                                                    (
                                                                    MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "port" |})
                                                                    NoLocator)
                                                                    (TypBit
                                                                    16%N)
                                                                    InOut));
                                                                   (Some
                                                                    (
                                                                    MkExpression
                                                                    NoInfo
                                                                    (ExpCast
                                                                    (TypBit
                                                                    32%N)
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "flow_hash" |})
                                                                    NoLocator)
                                                                    (TypBit
                                                                    16%N)
                                                                    InOut))
                                                                    (TypBit
                                                                    32%N)
                                                                    Directionless))])
                                                             StmUnit)
                                                        (BlockCons
                                                             (MkStatement
                                                                  NoInfo
                                                                  (StatConditional
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpBinaryOp
                                                                    Eq
                                                                    ( (
                                                                    MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "port" |})
                                                                    NoLocator)
                                                                    (TypBit
                                                                    16%N)
                                                                    InOut),
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpCast
                                                                    (TypBit
                                                                    16%N)
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpInt
                                                                    {| 
                                                                    itags := NoInfo;
                                                                    value := 0;
                                                                    width_signed := 
                                                                    None |})
                                                                    TypInteger
                                                                    Directionless))
                                                                    (TypBit
                                                                    16%N)
                                                                    Directionless) ))
                                                                    TypBool
                                                                    Directionless)
                                                                    (MkStatement
                                                                    NoInfo
                                                                    (StatBlock
                                                                    (BlockCons
                                                                    (MkStatement
                                                                    NoInfo
                                                                    (StatMethodCall
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "hula_nhop" |})
                                                                    NoLocator)
                                                                    (TypTable
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "apply_result_hula_nhop" |})
                                                                    Directionless)
                                                                    {| stags := NoInfo;
                                                                    str := "apply" |})
                                                                    (TypFunction
                                                                    (MkFunctionType
                                                                    nil nil
                                                                    FunTable
                                                                    (TypTypeName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "apply_result_hula_nhop" |})))
                                                                    Directionless)
                                                                    nil nil)
                                                                    StmUnit)
                                                                    (BlockCons
                                                                    (MkStatement
                                                                    NoInfo
                                                                    (StatMethodCall
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "flow_port_reg" |})
                                                                    NoLocator)
                                                                    (TypSpecializedType
                                                                    (TypExtern
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "register" |})
                                                                    [(
                                                                    TypBit
                                                                    16%N)])
                                                                    Directionless)
                                                                    {| stags := NoInfo;
                                                                    str := "write" |})
                                                                    (TypFunction
                                                                    (MkFunctionType
                                                                    nil
                                                                    [(
                                                                    MkParameter
                                                                    false In
                                                                    (TypBit
                                                                    32%N)
                                                                    None
                                                                    {| stags := NoInfo;
                                                                    str := "index" |});
                                                                    (MkParameter
                                                                    false In
                                                                    (TypBit
                                                                    16%N)
                                                                    None
                                                                    {| stags := NoInfo;
                                                                    str := "value" |})]
                                                                    FunExtern
                                                                    TypVoid))
                                                                    Directionless)
                                                                    nil
                                                                    [(
                                                                    Some
                                                                    (
                                                                    MkExpression
                                                                    NoInfo
                                                                    (ExpCast
                                                                    (TypBit
                                                                    32%N)
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "flow_hash" |})
                                                                    NoLocator)
                                                                    (TypBit
                                                                    16%N)
                                                                    InOut))
                                                                    (TypBit
                                                                    32%N)
                                                                    Directionless));
                                                                    (Some
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpCast
                                                                    (TypBit
                                                                    16%N)
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "standard_metadata" |})
                                                                    NoLocator)
                                                                    (TypTypeName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "standard_metadata_t" |})
                                                                    InOut)
                                                                    {| stags := NoInfo;
                                                                    str := "egress_spec" |})
                                                                    (TypBit
                                                                    9%N)
                                                                    Directionless))
                                                                    (TypBit
                                                                    16%N)
                                                                    Directionless))])
                                                                    StmUnit)
                                                                    (BlockEmpty
                                                                    NoInfo))))
                                                                    StmUnit)
                                                                    (Some
                                                                    (MkStatement
                                                                    NoInfo
                                                                    (StatBlock
                                                                    (BlockCons
                                                                    (MkStatement
                                                                    NoInfo
                                                                    (StatAssignment
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "standard_metadata" |})
                                                                    NoLocator)
                                                                    (TypTypeName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "standard_metadata_t" |})
                                                                    InOut)
                                                                    {| stags := NoInfo;
                                                                    str := "egress_spec" |})
                                                                    (TypBit
                                                                    9%N)
                                                                    Directionless)
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpCast
                                                                    (TypBit
                                                                    9%N)
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "port" |})
                                                                    NoLocator)
                                                                    (TypBit
                                                                    16%N)
                                                                    InOut))
                                                                    (TypBit
                                                                    9%N)
                                                                    Directionless))
                                                                    StmUnit)
                                                                    (BlockEmpty
                                                                    NoInfo)))
                                                                    StmUnit)))
                                                                  StmUnit)
                                                             (BlockCons
                                                                  (MkStatement
                                                                    NoInfo
                                                                    (StatMethodCall
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "dmac" |})
                                                                    NoLocator)
                                                                    (TypTable
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "apply_result_dmac" |})
                                                                    Directionless)
                                                                    {| stags := NoInfo;
                                                                    str := "apply" |})
                                                                    (TypFunction
                                                                    (MkFunctionType
                                                                    nil nil
                                                                    FunTable
                                                                    (TypTypeName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "apply_result_dmac" |})))
                                                                    Directionless)
                                                                    nil nil)
                                                                    StmUnit)
                                                                  (BlockEmpty
                                                                   NoInfo))))))))
                                   StmUnit)
                              (Some
                               (MkStatement NoInfo
                                    (StatBlock
                                     (BlockCons
                                          (MkStatement NoInfo
                                               (StatMethodCall
                                                    (MkExpression NoInfo
                                                         (ExpName
                                                          (BareName
                                                           {| stags := NoInfo;
                                                              str := "drop" |})
                                                          NoLocator)
                                                         (TypAction nil nil)
                                                         Directionless) nil
                                                    nil) StmUnit)
                                          (BlockEmpty NoInfo))) StmUnit)))
                         StmUnit))) StmUnit)
         (BlockCons
              (MkStatement NoInfo
                   (StatConditional
                        (MkExpression NoInfo
                             (ExpFunctionCall
                                  (MkExpression NoInfo
                                       (ExpExpressionMember
                                            (MkExpression NoInfo
                                                 (ExpExpressionMember
                                                      (MkExpression NoInfo
                                                           (ExpName
                                                            (BareName
                                                             {| stags := NoInfo;
                                                                str := "hdr" |})
                                                            NoLocator)
                                                           (TypTypeName
                                                            {| stags := NoInfo;
                                                               str := "headers" |})
                                                           InOut)
                                                      {| stags := NoInfo;
                                                         str := "ipv4" |})
                                                 (TypHeader
                                                  [( {| stags := NoInfo;
                                                        str := "version" |},
                                                     (TypBit 4%N) );
                                                   ( {| stags := NoInfo;
                                                        str := "ihl" |},
                                                     (TypBit 4%N) );
                                                   ( {| stags := NoInfo;
                                                        str := "diffserv" |},
                                                     (TypBit 8%N) );
                                                   ( {| stags := NoInfo;
                                                        str := "totalLen" |},
                                                     (TypBit 16%N) );
                                                   ( {| stags := NoInfo;
                                                        str := "identification" |},
                                                     (TypBit 16%N) );
                                                   ( {| stags := NoInfo;
                                                        str := "flags" |},
                                                     (TypBit 3%N) );
                                                   ( {| stags := NoInfo;
                                                        str := "fragOffset" |},
                                                     (TypBit 13%N) );
                                                   ( {| stags := NoInfo;
                                                        str := "ttl" |},
                                                     (TypBit 8%N) );
                                                   ( {| stags := NoInfo;
                                                        str := "protocol" |},
                                                     (TypBit 8%N) );
                                                   ( {| stags := NoInfo;
                                                        str := "hdrChecksum" |},
                                                     (TypBit 16%N) );
                                                   ( {| stags := NoInfo;
                                                        str := "srcAddr" |},
                                                     (TypBit 32%N) );
                                                   ( {| stags := NoInfo;
                                                        str := "dstAddr" |},
                                                     (TypBit 32%N) )])
                                                 Directionless)
                                            {| stags := NoInfo;
                                               str := "isValid" |})
                                       (TypFunction
                                        (MkFunctionType nil nil FunBuiltin
                                             TypBool)) Directionless) nil
                                  nil) TypBool Directionless)
                        (MkStatement NoInfo
                             (StatBlock
                              (BlockCons
                                   (MkStatement NoInfo
                                        (StatMethodCall
                                             (MkExpression NoInfo
                                                  (ExpName
                                                   (BareName
                                                    {| stags := NoInfo;
                                                       str := "update_ttl" |})
                                                   NoLocator)
                                                  (TypAction nil nil)
                                                  Directionless) nil nil)
                                        StmUnit) (BlockEmpty NoInfo)))
                             StmUnit) None) StmUnit) (BlockEmpty NoInfo))).

Definition MyEgress := DeclControl NoInfo
    {| stags := NoInfo; str := "MyEgress" |} nil
    [(MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "headers" |}) None
          {| stags := NoInfo; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "metadata" |}) None
          {| stags := NoInfo; str := "meta" |});
     (MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "standard_metadata_t" |})
          None {| stags := NoInfo; str := "standard_metadata" |})] nil nil
    (BlockCons
         (MkStatement NoInfo
              (StatConditional
                   (MkExpression NoInfo
                        (ExpBinaryOp And
                             ( (MkExpression NoInfo
                                    (ExpFunctionCall
                                         (MkExpression NoInfo
                                              (ExpExpressionMember
                                                   (MkExpression NoInfo
                                                        (ExpExpressionMember
                                                             (MkExpression
                                                                  NoInfo
                                                                  (ExpName
                                                                   (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "hdr" |})
                                                                   NoLocator)
                                                                  (TypTypeName
                                                                   {| 
                                                                   stags := NoInfo;
                                                                   str := "headers" |})
                                                                  InOut)
                                                             {| stags := NoInfo;
                                                                str := "hula" |})
                                                        (TypHeader
                                                         [( {| stags := NoInfo;
                                                               str := "dir" |},
                                                            (TypBit 1%N) );
                                                          ( {| stags := NoInfo;
                                                               str := "qdepth" |},
                                                            (TypBit 15%N) );
                                                          ( {| stags := NoInfo;
                                                               str := "digest" |},
                                                            (TypBit 32%N) )])
                                                        Directionless)
                                                   {| stags := NoInfo;
                                                      str := "isValid" |})
                                              (TypFunction
                                               (MkFunctionType nil nil
                                                    FunBuiltin TypBool))
                                              Directionless) nil nil) 
                                    TypBool Directionless),
                               (MkExpression NoInfo
                                    (ExpBinaryOp Eq
                                         ( (MkExpression NoInfo
                                                (ExpExpressionMember
                                                     (MkExpression NoInfo
                                                          (ExpExpressionMember
                                                               (MkExpression
                                                                    NoInfo
                                                                    (
                                                                    ExpName
                                                                    (
                                                                    BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "hdr" |})
                                                                    NoLocator)
                                                                    (
                                                                    TypTypeName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "headers" |})
                                                                    InOut)
                                                               {| stags := NoInfo;
                                                                  str := "hula" |})
                                                          (TypHeader
                                                           [( {| stags := NoInfo;
                                                                 str := "dir" |},
                                                              (TypBit 1%N) );
                                                            ( {| stags := NoInfo;
                                                                 str := "qdepth" |},
                                                              (TypBit 15%N) );
                                                            ( {| stags := NoInfo;
                                                                 str := "digest" |},
                                                              (TypBit 32%N) )])
                                                          Directionless)
                                                     {| stags := NoInfo;
                                                        str := "dir" |})
                                                (TypBit 1%N) Directionless),
                                           (MkExpression NoInfo
                                                (ExpCast (TypBit 1%N)
                                                     (MkExpression NoInfo
                                                          (ExpInt
                                                           {| itags := NoInfo;
                                                              value := 0;
                                                              width_signed := 
                                                              None |})
                                                          TypInteger
                                                          Directionless))
                                                (TypBit 1%N) Directionless) ))
                                    TypBool Directionless) )) TypBool
                        Directionless)
                   (MkStatement NoInfo
                        (StatBlock
                         (BlockCons
                              (MkStatement NoInfo
                                   (StatConditional
                                        (MkExpression NoInfo
                                             (ExpBinaryOp Lt
                                                  ( (MkExpression NoInfo
                                                         (ExpExpressionMember
                                                              (MkExpression
                                                                   NoInfo
                                                                   (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "hdr" |})
                                                                    NoLocator)
                                                                    (TypTypeName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "headers" |})
                                                                    InOut)
                                                                    {| stags := NoInfo;
                                                                    str := "hula" |})
                                                                   (TypHeader
                                                                    [
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "dir" |},
                                                                    (
                                                                    TypBit
                                                                    1%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "qdepth" |},
                                                                    (
                                                                    TypBit
                                                                    15%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "digest" |},
                                                                    (
                                                                    TypBit
                                                                    32%N) )])
                                                                   Directionless)
                                                              {| stags := NoInfo;
                                                                 str := "qdepth" |})
                                                         (TypBit 15%N)
                                                         Directionless),
                                                    (MkExpression NoInfo
                                                         (ExpCast
                                                              (TypTypeName
                                                               {| stags := NoInfo;
                                                                  str := "qdepth_t" |})
                                                              (MkExpression
                                                                   NoInfo
                                                                   (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "standard_metadata" |})
                                                                    NoLocator)
                                                                    (TypTypeName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "standard_metadata_t" |})
                                                                    InOut)
                                                                    {| stags := NoInfo;
                                                                    str := "deq_qdepth" |})
                                                                   (TypBit
                                                                    19%N)
                                                                   Directionless))
                                                         (TypTypeName
                                                          {| stags := NoInfo;
                                                             str := "qdepth_t" |})
                                                         Directionless) ))
                                             TypBool Directionless)
                                        (MkStatement NoInfo
                                             (StatBlock
                                              (BlockCons
                                                   (MkStatement NoInfo
                                                        (StatAssignment
                                                             (MkExpression
                                                                  NoInfo
                                                                  (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "hdr" |})
                                                                    NoLocator)
                                                                    (TypTypeName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "headers" |})
                                                                    InOut)
                                                                    {| stags := NoInfo;
                                                                    str := "hula" |})
                                                                    (TypHeader
                                                                    [( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "dir" |},
                                                                    (
                                                                    TypBit
                                                                    1%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "qdepth" |},
                                                                    (
                                                                    TypBit
                                                                    15%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "digest" |},
                                                                    (
                                                                    TypBit
                                                                    32%N) )])
                                                                    Directionless)
                                                                    {| stags := NoInfo;
                                                                    str := "qdepth" |})
                                                                  (TypBit
                                                                   15%N)
                                                                  Directionless)
                                                             (MkExpression
                                                                  NoInfo
                                                                  (ExpCast
                                                                    (TypTypeName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "qdepth_t" |})
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "standard_metadata" |})
                                                                    NoLocator)
                                                                    (TypTypeName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "standard_metadata_t" |})
                                                                    InOut)
                                                                    {| stags := NoInfo;
                                                                    str := "deq_qdepth" |})
                                                                    (TypBit
                                                                    19%N)
                                                                    Directionless))
                                                                  (TypTypeName
                                                                   {| 
                                                                   stags := NoInfo;
                                                                   str := "qdepth_t" |})
                                                                  Directionless))
                                                        StmUnit)
                                                   (BlockEmpty NoInfo)))
                                             StmUnit) None) StmUnit)
                              (BlockEmpty NoInfo))) StmUnit) None) StmUnit)
         (BlockEmpty NoInfo)).

Definition MyComputeChecksum := DeclControl NoInfo
    {| stags := NoInfo; str := "MyComputeChecksum" |} nil
    [(MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "headers" |}) None
          {| stags := NoInfo; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "metadata" |}) None
          {| stags := NoInfo; str := "meta" |})] nil nil
    (BlockCons
         (MkStatement NoInfo
              (StatMethodCall
                   (MkExpression NoInfo
                        (ExpName
                         (BareName
                          {| stags := NoInfo; str := "update_checksum" |})
                         NoLocator)
                        (TypFunction
                         (MkFunctionType
                              [{| stags := NoInfo; str := "T12" |};
                               {| stags := NoInfo; str := "O13" |}]
                              [(MkParameter false In TypBool None
                                    {| stags := NoInfo; str := "condition" |});
                               (MkParameter false In
                                    (TypTypeName
                                     {| stags := NoInfo; str := "T12" |})
                                    None
                                    {| stags := NoInfo; str := "data" |});
                               (MkParameter false InOut
                                    (TypTypeName
                                     {| stags := NoInfo; str := "O13" |})
                                    None
                                    {| stags := NoInfo; str := "checksum" |});
                               (MkParameter false Directionless
                                    (TypTypeName
                                     {| stags := NoInfo;
                                        str := "HashAlgorithm" |}) None
                                    {| stags := NoInfo; str := "algo" |})]
                              FunExtern TypVoid)) Directionless)
                   [(TypList
                     [(TypBit 4%N); (TypBit 4%N); (TypBit 8%N);
                      (TypBit 16%N); (TypBit 16%N); (TypBit 3%N);
                      (TypBit 13%N); (TypBit 8%N); (TypBit 8%N);
                      (TypBit 32%N); (TypBit 32%N)]); (TypBit 16%N)]
                   [(Some
                     (MkExpression NoInfo
                          (ExpFunctionCall
                               (MkExpression NoInfo
                                    (ExpExpressionMember
                                         (MkExpression NoInfo
                                              (ExpExpressionMember
                                                   (MkExpression NoInfo
                                                        (ExpName
                                                         (BareName
                                                          {| stags := NoInfo;
                                                             str := "hdr" |})
                                                         NoLocator)
                                                        (TypTypeName
                                                         {| stags := NoInfo;
                                                            str := "headers" |})
                                                        InOut)
                                                   {| stags := NoInfo;
                                                      str := "ipv4" |})
                                              (TypHeader
                                               [( {| stags := NoInfo;
                                                     str := "version" |},
                                                  (TypBit 4%N) );
                                                ( {| stags := NoInfo;
                                                     str := "ihl" |},
                                                  (TypBit 4%N) );
                                                ( {| stags := NoInfo;
                                                     str := "diffserv" |},
                                                  (TypBit 8%N) );
                                                ( {| stags := NoInfo;
                                                     str := "totalLen" |},
                                                  (TypBit 16%N) );
                                                ( {| stags := NoInfo;
                                                     str := "identification" |},
                                                  (TypBit 16%N) );
                                                ( {| stags := NoInfo;
                                                     str := "flags" |},
                                                  (TypBit 3%N) );
                                                ( {| stags := NoInfo;
                                                     str := "fragOffset" |},
                                                  (TypBit 13%N) );
                                                ( {| stags := NoInfo;
                                                     str := "ttl" |},
                                                  (TypBit 8%N) );
                                                ( {| stags := NoInfo;
                                                     str := "protocol" |},
                                                  (TypBit 8%N) );
                                                ( {| stags := NoInfo;
                                                     str := "hdrChecksum" |},
                                                  (TypBit 16%N) );
                                                ( {| stags := NoInfo;
                                                     str := "srcAddr" |},
                                                  (TypBit 32%N) );
                                                ( {| stags := NoInfo;
                                                     str := "dstAddr" |},
                                                  (TypBit 32%N) )])
                                              Directionless)
                                         {| stags := NoInfo;
                                            str := "isValid" |})
                                    (TypFunction
                                     (MkFunctionType nil nil FunBuiltin
                                          TypBool)) Directionless) nil nil)
                          TypBool Directionless));
                    (Some
                     (MkExpression NoInfo
                          (ExpList
                           [(MkExpression NoInfo
                                 (ExpExpressionMember
                                      (MkExpression NoInfo
                                           (ExpExpressionMember
                                                (MkExpression NoInfo
                                                     (ExpName
                                                      (BareName
                                                       {| stags := NoInfo;
                                                          str := "hdr" |})
                                                      NoLocator)
                                                     (TypTypeName
                                                      {| stags := NoInfo;
                                                         str := "headers" |})
                                                     InOut)
                                                {| stags := NoInfo;
                                                   str := "ipv4" |})
                                           (TypHeader
                                            [( {| stags := NoInfo;
                                                  str := "version" |},
                                               (TypBit 4%N) );
                                             ( {| stags := NoInfo;
                                                  str := "ihl" |},
                                               (TypBit 4%N) );
                                             ( {| stags := NoInfo;
                                                  str := "diffserv" |},
                                               (TypBit 8%N) );
                                             ( {| stags := NoInfo;
                                                  str := "totalLen" |},
                                               (TypBit 16%N) );
                                             ( {| stags := NoInfo;
                                                  str := "identification" |},
                                               (TypBit 16%N) );
                                             ( {| stags := NoInfo;
                                                  str := "flags" |},
                                               (TypBit 3%N) );
                                             ( {| stags := NoInfo;
                                                  str := "fragOffset" |},
                                               (TypBit 13%N) );
                                             ( {| stags := NoInfo;
                                                  str := "ttl" |},
                                               (TypBit 8%N) );
                                             ( {| stags := NoInfo;
                                                  str := "protocol" |},
                                               (TypBit 8%N) );
                                             ( {| stags := NoInfo;
                                                  str := "hdrChecksum" |},
                                               (TypBit 16%N) );
                                             ( {| stags := NoInfo;
                                                  str := "srcAddr" |},
                                               (TypBit 32%N) );
                                             ( {| stags := NoInfo;
                                                  str := "dstAddr" |},
                                               (TypBit 32%N) )])
                                           Directionless)
                                      {| stags := NoInfo; str := "version" |})
                                 (TypBit 4%N) Directionless);
                            (MkExpression NoInfo
                                 (ExpExpressionMember
                                      (MkExpression NoInfo
                                           (ExpExpressionMember
                                                (MkExpression NoInfo
                                                     (ExpName
                                                      (BareName
                                                       {| stags := NoInfo;
                                                          str := "hdr" |})
                                                      NoLocator)
                                                     (TypTypeName
                                                      {| stags := NoInfo;
                                                         str := "headers" |})
                                                     InOut)
                                                {| stags := NoInfo;
                                                   str := "ipv4" |})
                                           (TypHeader
                                            [( {| stags := NoInfo;
                                                  str := "version" |},
                                               (TypBit 4%N) );
                                             ( {| stags := NoInfo;
                                                  str := "ihl" |},
                                               (TypBit 4%N) );
                                             ( {| stags := NoInfo;
                                                  str := "diffserv" |},
                                               (TypBit 8%N) );
                                             ( {| stags := NoInfo;
                                                  str := "totalLen" |},
                                               (TypBit 16%N) );
                                             ( {| stags := NoInfo;
                                                  str := "identification" |},
                                               (TypBit 16%N) );
                                             ( {| stags := NoInfo;
                                                  str := "flags" |},
                                               (TypBit 3%N) );
                                             ( {| stags := NoInfo;
                                                  str := "fragOffset" |},
                                               (TypBit 13%N) );
                                             ( {| stags := NoInfo;
                                                  str := "ttl" |},
                                               (TypBit 8%N) );
                                             ( {| stags := NoInfo;
                                                  str := "protocol" |},
                                               (TypBit 8%N) );
                                             ( {| stags := NoInfo;
                                                  str := "hdrChecksum" |},
                                               (TypBit 16%N) );
                                             ( {| stags := NoInfo;
                                                  str := "srcAddr" |},
                                               (TypBit 32%N) );
                                             ( {| stags := NoInfo;
                                                  str := "dstAddr" |},
                                               (TypBit 32%N) )])
                                           Directionless)
                                      {| stags := NoInfo; str := "ihl" |})
                                 (TypBit 4%N) Directionless);
                            (MkExpression NoInfo
                                 (ExpExpressionMember
                                      (MkExpression NoInfo
                                           (ExpExpressionMember
                                                (MkExpression NoInfo
                                                     (ExpName
                                                      (BareName
                                                       {| stags := NoInfo;
                                                          str := "hdr" |})
                                                      NoLocator)
                                                     (TypTypeName
                                                      {| stags := NoInfo;
                                                         str := "headers" |})
                                                     InOut)
                                                {| stags := NoInfo;
                                                   str := "ipv4" |})
                                           (TypHeader
                                            [( {| stags := NoInfo;
                                                  str := "version" |},
                                               (TypBit 4%N) );
                                             ( {| stags := NoInfo;
                                                  str := "ihl" |},
                                               (TypBit 4%N) );
                                             ( {| stags := NoInfo;
                                                  str := "diffserv" |},
                                               (TypBit 8%N) );
                                             ( {| stags := NoInfo;
                                                  str := "totalLen" |},
                                               (TypBit 16%N) );
                                             ( {| stags := NoInfo;
                                                  str := "identification" |},
                                               (TypBit 16%N) );
                                             ( {| stags := NoInfo;
                                                  str := "flags" |},
                                               (TypBit 3%N) );
                                             ( {| stags := NoInfo;
                                                  str := "fragOffset" |},
                                               (TypBit 13%N) );
                                             ( {| stags := NoInfo;
                                                  str := "ttl" |},
                                               (TypBit 8%N) );
                                             ( {| stags := NoInfo;
                                                  str := "protocol" |},
                                               (TypBit 8%N) );
                                             ( {| stags := NoInfo;
                                                  str := "hdrChecksum" |},
                                               (TypBit 16%N) );
                                             ( {| stags := NoInfo;
                                                  str := "srcAddr" |},
                                               (TypBit 32%N) );
                                             ( {| stags := NoInfo;
                                                  str := "dstAddr" |},
                                               (TypBit 32%N) )])
                                           Directionless)
                                      {| stags := NoInfo;
                                         str := "diffserv" |}) (TypBit 8%N)
                                 Directionless);
                            (MkExpression NoInfo
                                 (ExpExpressionMember
                                      (MkExpression NoInfo
                                           (ExpExpressionMember
                                                (MkExpression NoInfo
                                                     (ExpName
                                                      (BareName
                                                       {| stags := NoInfo;
                                                          str := "hdr" |})
                                                      NoLocator)
                                                     (TypTypeName
                                                      {| stags := NoInfo;
                                                         str := "headers" |})
                                                     InOut)
                                                {| stags := NoInfo;
                                                   str := "ipv4" |})
                                           (TypHeader
                                            [( {| stags := NoInfo;
                                                  str := "version" |},
                                               (TypBit 4%N) );
                                             ( {| stags := NoInfo;
                                                  str := "ihl" |},
                                               (TypBit 4%N) );
                                             ( {| stags := NoInfo;
                                                  str := "diffserv" |},
                                               (TypBit 8%N) );
                                             ( {| stags := NoInfo;
                                                  str := "totalLen" |},
                                               (TypBit 16%N) );
                                             ( {| stags := NoInfo;
                                                  str := "identification" |},
                                               (TypBit 16%N) );
                                             ( {| stags := NoInfo;
                                                  str := "flags" |},
                                               (TypBit 3%N) );
                                             ( {| stags := NoInfo;
                                                  str := "fragOffset" |},
                                               (TypBit 13%N) );
                                             ( {| stags := NoInfo;
                                                  str := "ttl" |},
                                               (TypBit 8%N) );
                                             ( {| stags := NoInfo;
                                                  str := "protocol" |},
                                               (TypBit 8%N) );
                                             ( {| stags := NoInfo;
                                                  str := "hdrChecksum" |},
                                               (TypBit 16%N) );
                                             ( {| stags := NoInfo;
                                                  str := "srcAddr" |},
                                               (TypBit 32%N) );
                                             ( {| stags := NoInfo;
                                                  str := "dstAddr" |},
                                               (TypBit 32%N) )])
                                           Directionless)
                                      {| stags := NoInfo;
                                         str := "totalLen" |}) (TypBit 16%N)
                                 Directionless);
                            (MkExpression NoInfo
                                 (ExpExpressionMember
                                      (MkExpression NoInfo
                                           (ExpExpressionMember
                                                (MkExpression NoInfo
                                                     (ExpName
                                                      (BareName
                                                       {| stags := NoInfo;
                                                          str := "hdr" |})
                                                      NoLocator)
                                                     (TypTypeName
                                                      {| stags := NoInfo;
                                                         str := "headers" |})
                                                     InOut)
                                                {| stags := NoInfo;
                                                   str := "ipv4" |})
                                           (TypHeader
                                            [( {| stags := NoInfo;
                                                  str := "version" |},
                                               (TypBit 4%N) );
                                             ( {| stags := NoInfo;
                                                  str := "ihl" |},
                                               (TypBit 4%N) );
                                             ( {| stags := NoInfo;
                                                  str := "diffserv" |},
                                               (TypBit 8%N) );
                                             ( {| stags := NoInfo;
                                                  str := "totalLen" |},
                                               (TypBit 16%N) );
                                             ( {| stags := NoInfo;
                                                  str := "identification" |},
                                               (TypBit 16%N) );
                                             ( {| stags := NoInfo;
                                                  str := "flags" |},
                                               (TypBit 3%N) );
                                             ( {| stags := NoInfo;
                                                  str := "fragOffset" |},
                                               (TypBit 13%N) );
                                             ( {| stags := NoInfo;
                                                  str := "ttl" |},
                                               (TypBit 8%N) );
                                             ( {| stags := NoInfo;
                                                  str := "protocol" |},
                                               (TypBit 8%N) );
                                             ( {| stags := NoInfo;
                                                  str := "hdrChecksum" |},
                                               (TypBit 16%N) );
                                             ( {| stags := NoInfo;
                                                  str := "srcAddr" |},
                                               (TypBit 32%N) );
                                             ( {| stags := NoInfo;
                                                  str := "dstAddr" |},
                                               (TypBit 32%N) )])
                                           Directionless)
                                      {| stags := NoInfo;
                                         str := "identification" |})
                                 (TypBit 16%N) Directionless);
                            (MkExpression NoInfo
                                 (ExpExpressionMember
                                      (MkExpression NoInfo
                                           (ExpExpressionMember
                                                (MkExpression NoInfo
                                                     (ExpName
                                                      (BareName
                                                       {| stags := NoInfo;
                                                          str := "hdr" |})
                                                      NoLocator)
                                                     (TypTypeName
                                                      {| stags := NoInfo;
                                                         str := "headers" |})
                                                     InOut)
                                                {| stags := NoInfo;
                                                   str := "ipv4" |})
                                           (TypHeader
                                            [( {| stags := NoInfo;
                                                  str := "version" |},
                                               (TypBit 4%N) );
                                             ( {| stags := NoInfo;
                                                  str := "ihl" |},
                                               (TypBit 4%N) );
                                             ( {| stags := NoInfo;
                                                  str := "diffserv" |},
                                               (TypBit 8%N) );
                                             ( {| stags := NoInfo;
                                                  str := "totalLen" |},
                                               (TypBit 16%N) );
                                             ( {| stags := NoInfo;
                                                  str := "identification" |},
                                               (TypBit 16%N) );
                                             ( {| stags := NoInfo;
                                                  str := "flags" |},
                                               (TypBit 3%N) );
                                             ( {| stags := NoInfo;
                                                  str := "fragOffset" |},
                                               (TypBit 13%N) );
                                             ( {| stags := NoInfo;
                                                  str := "ttl" |},
                                               (TypBit 8%N) );
                                             ( {| stags := NoInfo;
                                                  str := "protocol" |},
                                               (TypBit 8%N) );
                                             ( {| stags := NoInfo;
                                                  str := "hdrChecksum" |},
                                               (TypBit 16%N) );
                                             ( {| stags := NoInfo;
                                                  str := "srcAddr" |},
                                               (TypBit 32%N) );
                                             ( {| stags := NoInfo;
                                                  str := "dstAddr" |},
                                               (TypBit 32%N) )])
                                           Directionless)
                                      {| stags := NoInfo; str := "flags" |})
                                 (TypBit 3%N) Directionless);
                            (MkExpression NoInfo
                                 (ExpExpressionMember
                                      (MkExpression NoInfo
                                           (ExpExpressionMember
                                                (MkExpression NoInfo
                                                     (ExpName
                                                      (BareName
                                                       {| stags := NoInfo;
                                                          str := "hdr" |})
                                                      NoLocator)
                                                     (TypTypeName
                                                      {| stags := NoInfo;
                                                         str := "headers" |})
                                                     InOut)
                                                {| stags := NoInfo;
                                                   str := "ipv4" |})
                                           (TypHeader
                                            [( {| stags := NoInfo;
                                                  str := "version" |},
                                               (TypBit 4%N) );
                                             ( {| stags := NoInfo;
                                                  str := "ihl" |},
                                               (TypBit 4%N) );
                                             ( {| stags := NoInfo;
                                                  str := "diffserv" |},
                                               (TypBit 8%N) );
                                             ( {| stags := NoInfo;
                                                  str := "totalLen" |},
                                               (TypBit 16%N) );
                                             ( {| stags := NoInfo;
                                                  str := "identification" |},
                                               (TypBit 16%N) );
                                             ( {| stags := NoInfo;
                                                  str := "flags" |},
                                               (TypBit 3%N) );
                                             ( {| stags := NoInfo;
                                                  str := "fragOffset" |},
                                               (TypBit 13%N) );
                                             ( {| stags := NoInfo;
                                                  str := "ttl" |},
                                               (TypBit 8%N) );
                                             ( {| stags := NoInfo;
                                                  str := "protocol" |},
                                               (TypBit 8%N) );
                                             ( {| stags := NoInfo;
                                                  str := "hdrChecksum" |},
                                               (TypBit 16%N) );
                                             ( {| stags := NoInfo;
                                                  str := "srcAddr" |},
                                               (TypBit 32%N) );
                                             ( {| stags := NoInfo;
                                                  str := "dstAddr" |},
                                               (TypBit 32%N) )])
                                           Directionless)
                                      {| stags := NoInfo;
                                         str := "fragOffset" |})
                                 (TypBit 13%N) Directionless);
                            (MkExpression NoInfo
                                 (ExpExpressionMember
                                      (MkExpression NoInfo
                                           (ExpExpressionMember
                                                (MkExpression NoInfo
                                                     (ExpName
                                                      (BareName
                                                       {| stags := NoInfo;
                                                          str := "hdr" |})
                                                      NoLocator)
                                                     (TypTypeName
                                                      {| stags := NoInfo;
                                                         str := "headers" |})
                                                     InOut)
                                                {| stags := NoInfo;
                                                   str := "ipv4" |})
                                           (TypHeader
                                            [( {| stags := NoInfo;
                                                  str := "version" |},
                                               (TypBit 4%N) );
                                             ( {| stags := NoInfo;
                                                  str := "ihl" |},
                                               (TypBit 4%N) );
                                             ( {| stags := NoInfo;
                                                  str := "diffserv" |},
                                               (TypBit 8%N) );
                                             ( {| stags := NoInfo;
                                                  str := "totalLen" |},
                                               (TypBit 16%N) );
                                             ( {| stags := NoInfo;
                                                  str := "identification" |},
                                               (TypBit 16%N) );
                                             ( {| stags := NoInfo;
                                                  str := "flags" |},
                                               (TypBit 3%N) );
                                             ( {| stags := NoInfo;
                                                  str := "fragOffset" |},
                                               (TypBit 13%N) );
                                             ( {| stags := NoInfo;
                                                  str := "ttl" |},
                                               (TypBit 8%N) );
                                             ( {| stags := NoInfo;
                                                  str := "protocol" |},
                                               (TypBit 8%N) );
                                             ( {| stags := NoInfo;
                                                  str := "hdrChecksum" |},
                                               (TypBit 16%N) );
                                             ( {| stags := NoInfo;
                                                  str := "srcAddr" |},
                                               (TypBit 32%N) );
                                             ( {| stags := NoInfo;
                                                  str := "dstAddr" |},
                                               (TypBit 32%N) )])
                                           Directionless)
                                      {| stags := NoInfo; str := "ttl" |})
                                 (TypBit 8%N) Directionless);
                            (MkExpression NoInfo
                                 (ExpExpressionMember
                                      (MkExpression NoInfo
                                           (ExpExpressionMember
                                                (MkExpression NoInfo
                                                     (ExpName
                                                      (BareName
                                                       {| stags := NoInfo;
                                                          str := "hdr" |})
                                                      NoLocator)
                                                     (TypTypeName
                                                      {| stags := NoInfo;
                                                         str := "headers" |})
                                                     InOut)
                                                {| stags := NoInfo;
                                                   str := "ipv4" |})
                                           (TypHeader
                                            [( {| stags := NoInfo;
                                                  str := "version" |},
                                               (TypBit 4%N) );
                                             ( {| stags := NoInfo;
                                                  str := "ihl" |},
                                               (TypBit 4%N) );
                                             ( {| stags := NoInfo;
                                                  str := "diffserv" |},
                                               (TypBit 8%N) );
                                             ( {| stags := NoInfo;
                                                  str := "totalLen" |},
                                               (TypBit 16%N) );
                                             ( {| stags := NoInfo;
                                                  str := "identification" |},
                                               (TypBit 16%N) );
                                             ( {| stags := NoInfo;
                                                  str := "flags" |},
                                               (TypBit 3%N) );
                                             ( {| stags := NoInfo;
                                                  str := "fragOffset" |},
                                               (TypBit 13%N) );
                                             ( {| stags := NoInfo;
                                                  str := "ttl" |},
                                               (TypBit 8%N) );
                                             ( {| stags := NoInfo;
                                                  str := "protocol" |},
                                               (TypBit 8%N) );
                                             ( {| stags := NoInfo;
                                                  str := "hdrChecksum" |},
                                               (TypBit 16%N) );
                                             ( {| stags := NoInfo;
                                                  str := "srcAddr" |},
                                               (TypBit 32%N) );
                                             ( {| stags := NoInfo;
                                                  str := "dstAddr" |},
                                               (TypBit 32%N) )])
                                           Directionless)
                                      {| stags := NoInfo;
                                         str := "protocol" |}) (TypBit 8%N)
                                 Directionless);
                            (MkExpression NoInfo
                                 (ExpExpressionMember
                                      (MkExpression NoInfo
                                           (ExpExpressionMember
                                                (MkExpression NoInfo
                                                     (ExpName
                                                      (BareName
                                                       {| stags := NoInfo;
                                                          str := "hdr" |})
                                                      NoLocator)
                                                     (TypTypeName
                                                      {| stags := NoInfo;
                                                         str := "headers" |})
                                                     InOut)
                                                {| stags := NoInfo;
                                                   str := "ipv4" |})
                                           (TypHeader
                                            [( {| stags := NoInfo;
                                                  str := "version" |},
                                               (TypBit 4%N) );
                                             ( {| stags := NoInfo;
                                                  str := "ihl" |},
                                               (TypBit 4%N) );
                                             ( {| stags := NoInfo;
                                                  str := "diffserv" |},
                                               (TypBit 8%N) );
                                             ( {| stags := NoInfo;
                                                  str := "totalLen" |},
                                               (TypBit 16%N) );
                                             ( {| stags := NoInfo;
                                                  str := "identification" |},
                                               (TypBit 16%N) );
                                             ( {| stags := NoInfo;
                                                  str := "flags" |},
                                               (TypBit 3%N) );
                                             ( {| stags := NoInfo;
                                                  str := "fragOffset" |},
                                               (TypBit 13%N) );
                                             ( {| stags := NoInfo;
                                                  str := "ttl" |},
                                               (TypBit 8%N) );
                                             ( {| stags := NoInfo;
                                                  str := "protocol" |},
                                               (TypBit 8%N) );
                                             ( {| stags := NoInfo;
                                                  str := "hdrChecksum" |},
                                               (TypBit 16%N) );
                                             ( {| stags := NoInfo;
                                                  str := "srcAddr" |},
                                               (TypBit 32%N) );
                                             ( {| stags := NoInfo;
                                                  str := "dstAddr" |},
                                               (TypBit 32%N) )])
                                           Directionless)
                                      {| stags := NoInfo; str := "srcAddr" |})
                                 (TypBit 32%N) Directionless);
                            (MkExpression NoInfo
                                 (ExpExpressionMember
                                      (MkExpression NoInfo
                                           (ExpExpressionMember
                                                (MkExpression NoInfo
                                                     (ExpName
                                                      (BareName
                                                       {| stags := NoInfo;
                                                          str := "hdr" |})
                                                      NoLocator)
                                                     (TypTypeName
                                                      {| stags := NoInfo;
                                                         str := "headers" |})
                                                     InOut)
                                                {| stags := NoInfo;
                                                   str := "ipv4" |})
                                           (TypHeader
                                            [( {| stags := NoInfo;
                                                  str := "version" |},
                                               (TypBit 4%N) );
                                             ( {| stags := NoInfo;
                                                  str := "ihl" |},
                                               (TypBit 4%N) );
                                             ( {| stags := NoInfo;
                                                  str := "diffserv" |},
                                               (TypBit 8%N) );
                                             ( {| stags := NoInfo;
                                                  str := "totalLen" |},
                                               (TypBit 16%N) );
                                             ( {| stags := NoInfo;
                                                  str := "identification" |},
                                               (TypBit 16%N) );
                                             ( {| stags := NoInfo;
                                                  str := "flags" |},
                                               (TypBit 3%N) );
                                             ( {| stags := NoInfo;
                                                  str := "fragOffset" |},
                                               (TypBit 13%N) );
                                             ( {| stags := NoInfo;
                                                  str := "ttl" |},
                                               (TypBit 8%N) );
                                             ( {| stags := NoInfo;
                                                  str := "protocol" |},
                                               (TypBit 8%N) );
                                             ( {| stags := NoInfo;
                                                  str := "hdrChecksum" |},
                                               (TypBit 16%N) );
                                             ( {| stags := NoInfo;
                                                  str := "srcAddr" |},
                                               (TypBit 32%N) );
                                             ( {| stags := NoInfo;
                                                  str := "dstAddr" |},
                                               (TypBit 32%N) )])
                                           Directionless)
                                      {| stags := NoInfo; str := "dstAddr" |})
                                 (TypBit 32%N) Directionless)])
                          (TypList
                           [(TypBit 4%N); (TypBit 4%N); (TypBit 8%N);
                            (TypBit 16%N); (TypBit 16%N); (TypBit 3%N);
                            (TypBit 13%N); (TypBit 8%N); (TypBit 8%N);
                            (TypBit 32%N); (TypBit 32%N)]) Directionless));
                    (Some
                     (MkExpression NoInfo
                          (ExpExpressionMember
                               (MkExpression NoInfo
                                    (ExpExpressionMember
                                         (MkExpression NoInfo
                                              (ExpName
                                               (BareName
                                                {| stags := NoInfo;
                                                   str := "hdr" |})
                                               NoLocator)
                                              (TypTypeName
                                               {| stags := NoInfo;
                                                  str := "headers" |}) InOut)
                                         {| stags := NoInfo; str := "ipv4" |})
                                    (TypHeader
                                     [( {| stags := NoInfo;
                                           str := "version" |},
                                        (TypBit 4%N) );
                                      ( {| stags := NoInfo; str := "ihl" |},
                                        (TypBit 4%N) );
                                      ( {| stags := NoInfo;
                                           str := "diffserv" |},
                                        (TypBit 8%N) );
                                      ( {| stags := NoInfo;
                                           str := "totalLen" |},
                                        (TypBit 16%N) );
                                      ( {| stags := NoInfo;
                                           str := "identification" |},
                                        (TypBit 16%N) );
                                      ( {| stags := NoInfo; str := "flags" |},
                                        (TypBit 3%N) );
                                      ( {| stags := NoInfo;
                                           str := "fragOffset" |},
                                        (TypBit 13%N) );
                                      ( {| stags := NoInfo; str := "ttl" |},
                                        (TypBit 8%N) );
                                      ( {| stags := NoInfo;
                                           str := "protocol" |},
                                        (TypBit 8%N) );
                                      ( {| stags := NoInfo;
                                           str := "hdrChecksum" |},
                                        (TypBit 16%N) );
                                      ( {| stags := NoInfo;
                                           str := "srcAddr" |},
                                        (TypBit 32%N) );
                                      ( {| stags := NoInfo;
                                           str := "dstAddr" |},
                                        (TypBit 32%N) )]) Directionless)
                               {| stags := NoInfo; str := "hdrChecksum" |})
                          (TypBit 16%N) Directionless));
                    (Some
                     (MkExpression NoInfo
                          (ExpTypeMember
                               {| stags := NoInfo; str := "HashAlgorithm" |}
                               {| stags := NoInfo; str := "csum16" |})
                          (TypEnum
                               {| stags := NoInfo; str := "HashAlgorithm" |}
                               None
                               [{| stags := NoInfo; str := "crc32" |};
                                {| stags := NoInfo; str := "crc32_custom" |};
                                {| stags := NoInfo; str := "crc16" |};
                                {| stags := NoInfo; str := "crc16_custom" |};
                                {| stags := NoInfo; str := "random" |};
                                {| stags := NoInfo; str := "identity" |};
                                {| stags := NoInfo; str := "csum16" |};
                                {| stags := NoInfo; str := "xor16" |}])
                          Directionless))]) StmUnit) (BlockEmpty NoInfo)).

Definition MyDeparser := DeclControl NoInfo
    {| stags := NoInfo; str := "MyDeparser" |} nil
    [(MkParameter false Directionless
          (TypTypeName {| stags := NoInfo; str := "packet_out" |}) None
          {| stags := NoInfo; str := "packet" |});
     (MkParameter false In
          (TypTypeName {| stags := NoInfo; str := "headers" |}) None
          {| stags := NoInfo; str := "hdr" |})] nil nil
    (BlockCons
         (MkStatement NoInfo
              (StatMethodCall
                   (MkExpression NoInfo
                        (ExpExpressionMember
                             (MkExpression NoInfo
                                  (ExpName
                                   (BareName
                                    {| stags := NoInfo; str := "packet" |})
                                   NoLocator)
                                  (TypTypeName
                                   {| stags := NoInfo; str := "packet_out" |})
                                  Directionless)
                             {| stags := NoInfo; str := "emit" |})
                        (TypFunction
                         (MkFunctionType [{| stags := NoInfo; str := "T2" |}]
                              [(MkParameter false In
                                    (TypTypeName
                                     {| stags := NoInfo; str := "T2" |}) 
                                    None {| stags := NoInfo; str := "hdr" |})]
                              FunExtern TypVoid)) Directionless)
                   [(TypHeader
                     [( {| stags := NoInfo; str := "dstAddr" |},
                        (TypBit 48%N) );
                      ( {| stags := NoInfo; str := "srcAddr" |},
                        (TypBit 48%N) );
                      ( {| stags := NoInfo; str := "etherType" |},
                        (TypBit 16%N) )])]
                   [(Some
                     (MkExpression NoInfo
                          (ExpExpressionMember
                               (MkExpression NoInfo
                                    (ExpName
                                     (BareName
                                      {| stags := NoInfo; str := "hdr" |})
                                     NoLocator)
                                    (TypTypeName
                                     {| stags := NoInfo; str := "headers" |})
                                    In)
                               {| stags := NoInfo; str := "ethernet" |})
                          (TypHeader
                           [( {| stags := NoInfo; str := "dstAddr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "srcAddr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "etherType" |},
                              (TypBit 16%N) )]) Directionless))]) StmUnit)
         (BlockCons
              (MkStatement NoInfo
                   (StatMethodCall
                        (MkExpression NoInfo
                             (ExpExpressionMember
                                  (MkExpression NoInfo
                                       (ExpName
                                        (BareName
                                         {| stags := NoInfo;
                                            str := "packet" |}) NoLocator)
                                       (TypTypeName
                                        {| stags := NoInfo;
                                           str := "packet_out" |})
                                       Directionless)
                                  {| stags := NoInfo; str := "emit" |})
                             (TypFunction
                              (MkFunctionType
                                   [{| stags := NoInfo; str := "T2" |}]
                                   [(MkParameter false In
                                         (TypTypeName
                                          {| stags := NoInfo; str := "T2" |})
                                         None
                                         {| stags := NoInfo; str := "hdr" |})]
                                   FunExtern TypVoid)) Directionless)
                        [(TypHeader
                          [( {| stags := NoInfo; str := "dir" |},
                             (TypBit 1%N) );
                           ( {| stags := NoInfo; str := "qdepth" |},
                             (TypBit 15%N) );
                           ( {| stags := NoInfo; str := "digest" |},
                             (TypBit 32%N) )])]
                        [(Some
                          (MkExpression NoInfo
                               (ExpExpressionMember
                                    (MkExpression NoInfo
                                         (ExpName
                                          (BareName
                                           {| stags := NoInfo;
                                              str := "hdr" |}) NoLocator)
                                         (TypTypeName
                                          {| stags := NoInfo;
                                             str := "headers" |}) In)
                                    {| stags := NoInfo; str := "hula" |})
                               (TypHeader
                                [( {| stags := NoInfo; str := "dir" |},
                                   (TypBit 1%N) );
                                 ( {| stags := NoInfo; str := "qdepth" |},
                                   (TypBit 15%N) );
                                 ( {| stags := NoInfo; str := "digest" |},
                                   (TypBit 32%N) )]) Directionless))])
                   StmUnit)
              (BlockCons
                   (MkStatement NoInfo
                        (StatMethodCall
                             (MkExpression NoInfo
                                  (ExpExpressionMember
                                       (MkExpression NoInfo
                                            (ExpName
                                             (BareName
                                              {| stags := NoInfo;
                                                 str := "packet" |})
                                             NoLocator)
                                            (TypTypeName
                                             {| stags := NoInfo;
                                                str := "packet_out" |})
                                            Directionless)
                                       {| stags := NoInfo; str := "emit" |})
                                  (TypFunction
                                   (MkFunctionType
                                        [{| stags := NoInfo; str := "T2" |}]
                                        [(MkParameter false In
                                              (TypTypeName
                                               {| stags := NoInfo;
                                                  str := "T2" |}) None
                                              {| stags := NoInfo;
                                                 str := "hdr" |})] FunExtern
                                        TypVoid)) Directionless)
                             [(TypArray
                                   (TypHeader
                                    [( {| stags := NoInfo; str := "bos" |},
                                       (TypBit 1%N) );
                                     ( {| stags := NoInfo; str := "port" |},
                                       (TypBit 15%N) )]) 9%N)]
                             [(Some
                               (MkExpression NoInfo
                                    (ExpExpressionMember
                                         (MkExpression NoInfo
                                              (ExpName
                                               (BareName
                                                {| stags := NoInfo;
                                                   str := "hdr" |})
                                               NoLocator)
                                              (TypTypeName
                                               {| stags := NoInfo;
                                                  str := "headers" |}) In)
                                         {| stags := NoInfo;
                                            str := "srcRoutes" |})
                                    (TypArray
                                         (TypHeader
                                          [( {| stags := NoInfo;
                                                str := "bos" |},
                                             (TypBit 1%N) );
                                           ( {| stags := NoInfo;
                                                str := "port" |},
                                             (TypBit 15%N) )]) 9%N)
                                    Directionless))]) StmUnit)
                   (BlockCons
                        (MkStatement NoInfo
                             (StatMethodCall
                                  (MkExpression NoInfo
                                       (ExpExpressionMember
                                            (MkExpression NoInfo
                                                 (ExpName
                                                  (BareName
                                                   {| stags := NoInfo;
                                                      str := "packet" |})
                                                  NoLocator)
                                                 (TypTypeName
                                                  {| stags := NoInfo;
                                                     str := "packet_out" |})
                                                 Directionless)
                                            {| stags := NoInfo;
                                               str := "emit" |})
                                       (TypFunction
                                        (MkFunctionType
                                             [{| stags := NoInfo;
                                                 str := "T2" |}]
                                             [(MkParameter false In
                                                   (TypTypeName
                                                    {| stags := NoInfo;
                                                       str := "T2" |}) 
                                                   None
                                                   {| stags := NoInfo;
                                                      str := "hdr" |})]
                                             FunExtern TypVoid))
                                       Directionless)
                                  [(TypHeader
                                    [( {| stags := NoInfo;
                                          str := "version" |}, (TypBit 4%N) );
                                     ( {| stags := NoInfo; str := "ihl" |},
                                       (TypBit 4%N) );
                                     ( {| stags := NoInfo;
                                          str := "diffserv" |},
                                       (TypBit 8%N) );
                                     ( {| stags := NoInfo;
                                          str := "totalLen" |},
                                       (TypBit 16%N) );
                                     ( {| stags := NoInfo;
                                          str := "identification" |},
                                       (TypBit 16%N) );
                                     ( {| stags := NoInfo; str := "flags" |},
                                       (TypBit 3%N) );
                                     ( {| stags := NoInfo;
                                          str := "fragOffset" |},
                                       (TypBit 13%N) );
                                     ( {| stags := NoInfo; str := "ttl" |},
                                       (TypBit 8%N) );
                                     ( {| stags := NoInfo;
                                          str := "protocol" |},
                                       (TypBit 8%N) );
                                     ( {| stags := NoInfo;
                                          str := "hdrChecksum" |},
                                       (TypBit 16%N) );
                                     ( {| stags := NoInfo;
                                          str := "srcAddr" |},
                                       (TypBit 32%N) );
                                     ( {| stags := NoInfo;
                                          str := "dstAddr" |},
                                       (TypBit 32%N) )])]
                                  [(Some
                                    (MkExpression NoInfo
                                         (ExpExpressionMember
                                              (MkExpression NoInfo
                                                   (ExpName
                                                    (BareName
                                                     {| stags := NoInfo;
                                                        str := "hdr" |})
                                                    NoLocator)
                                                   (TypTypeName
                                                    {| stags := NoInfo;
                                                       str := "headers" |})
                                                   In)
                                              {| stags := NoInfo;
                                                 str := "ipv4" |})
                                         (TypHeader
                                          [( {| stags := NoInfo;
                                                str := "version" |},
                                             (TypBit 4%N) );
                                           ( {| stags := NoInfo;
                                                str := "ihl" |},
                                             (TypBit 4%N) );
                                           ( {| stags := NoInfo;
                                                str := "diffserv" |},
                                             (TypBit 8%N) );
                                           ( {| stags := NoInfo;
                                                str := "totalLen" |},
                                             (TypBit 16%N) );
                                           ( {| stags := NoInfo;
                                                str := "identification" |},
                                             (TypBit 16%N) );
                                           ( {| stags := NoInfo;
                                                str := "flags" |},
                                             (TypBit 3%N) );
                                           ( {| stags := NoInfo;
                                                str := "fragOffset" |},
                                             (TypBit 13%N) );
                                           ( {| stags := NoInfo;
                                                str := "ttl" |},
                                             (TypBit 8%N) );
                                           ( {| stags := NoInfo;
                                                str := "protocol" |},
                                             (TypBit 8%N) );
                                           ( {| stags := NoInfo;
                                                str := "hdrChecksum" |},
                                             (TypBit 16%N) );
                                           ( {| stags := NoInfo;
                                                str := "srcAddr" |},
                                             (TypBit 32%N) );
                                           ( {| stags := NoInfo;
                                                str := "dstAddr" |},
                                             (TypBit 32%N) )]) Directionless))])
                             StmUnit)
                        (BlockCons
                             (MkStatement NoInfo
                                  (StatMethodCall
                                       (MkExpression NoInfo
                                            (ExpExpressionMember
                                                 (MkExpression NoInfo
                                                      (ExpName
                                                       (BareName
                                                        {| stags := NoInfo;
                                                           str := "packet" |})
                                                       NoLocator)
                                                      (TypTypeName
                                                       {| stags := NoInfo;
                                                          str := "packet_out" |})
                                                      Directionless)
                                                 {| stags := NoInfo;
                                                    str := "emit" |})
                                            (TypFunction
                                             (MkFunctionType
                                                  [{| stags := NoInfo;
                                                      str := "T2" |}]
                                                  [(MkParameter false In
                                                        (TypTypeName
                                                         {| stags := NoInfo;
                                                            str := "T2" |})
                                                        None
                                                        {| stags := NoInfo;
                                                           str := "hdr" |})]
                                                  FunExtern TypVoid))
                                            Directionless)
                                       [(TypHeader
                                         [( {| stags := NoInfo;
                                               str := "srcPort" |},
                                            (TypBit 16%N) );
                                          ( {| stags := NoInfo;
                                               str := "dstPort" |},
                                            (TypBit 16%N) );
                                          ( {| stags := NoInfo;
                                               str := "length_" |},
                                            (TypBit 16%N) );
                                          ( {| stags := NoInfo;
                                               str := "checksum" |},
                                            (TypBit 16%N) )])]
                                       [(Some
                                         (MkExpression NoInfo
                                              (ExpExpressionMember
                                                   (MkExpression NoInfo
                                                        (ExpName
                                                         (BareName
                                                          {| stags := NoInfo;
                                                             str := "hdr" |})
                                                         NoLocator)
                                                        (TypTypeName
                                                         {| stags := NoInfo;
                                                            str := "headers" |})
                                                        In)
                                                   {| stags := NoInfo;
                                                      str := "udp" |})
                                              (TypHeader
                                               [( {| stags := NoInfo;
                                                     str := "srcPort" |},
                                                  (TypBit 16%N) );
                                                ( {| stags := NoInfo;
                                                     str := "dstPort" |},
                                                  (TypBit 16%N) );
                                                ( {| stags := NoInfo;
                                                     str := "length_" |},
                                                  (TypBit 16%N) );
                                                ( {| stags := NoInfo;
                                                     str := "checksum" |},
                                                  (TypBit 16%N) )])
                                              Directionless))]) StmUnit)
                             (BlockEmpty NoInfo)))))).

Definition main := DeclInstantiation NoInfo
    (TypSpecializedType
         (TypTypeName {| stags := NoInfo; str := "V1Switch" |})
         [(TypStruct
           [( {| stags := NoInfo; str := "ethernet" |},
              (TypHeader
               [( {| stags := NoInfo; str := "dstAddr" |}, (TypBit 48%N) );
                ( {| stags := NoInfo; str := "srcAddr" |}, (TypBit 48%N) );
                ( {| stags := NoInfo; str := "etherType" |}, (TypBit 16%N) )]) );
            ( {| stags := NoInfo; str := "srcRoutes" |},
              (TypArray
                   (TypHeader
                    [( {| stags := NoInfo; str := "bos" |}, (TypBit 1%N) );
                     ( {| stags := NoInfo; str := "port" |}, (TypBit 15%N) )])
                   9%N) );
            ( {| stags := NoInfo; str := "ipv4" |},
              (TypHeader
               [( {| stags := NoInfo; str := "version" |}, (TypBit 4%N) );
                ( {| stags := NoInfo; str := "ihl" |}, (TypBit 4%N) );
                ( {| stags := NoInfo; str := "diffserv" |}, (TypBit 8%N) );
                ( {| stags := NoInfo; str := "totalLen" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "identification" |},
                  (TypBit 16%N) );
                ( {| stags := NoInfo; str := "flags" |}, (TypBit 3%N) );
                ( {| stags := NoInfo; str := "fragOffset" |}, (TypBit 13%N) );
                ( {| stags := NoInfo; str := "ttl" |}, (TypBit 8%N) );
                ( {| stags := NoInfo; str := "protocol" |}, (TypBit 8%N) );
                ( {| stags := NoInfo; str := "hdrChecksum" |},
                  (TypBit 16%N) );
                ( {| stags := NoInfo; str := "srcAddr" |}, (TypBit 32%N) );
                ( {| stags := NoInfo; str := "dstAddr" |}, (TypBit 32%N) )]) );
            ( {| stags := NoInfo; str := "udp" |},
              (TypHeader
               [( {| stags := NoInfo; str := "srcPort" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "dstPort" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "length_" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "checksum" |}, (TypBit 16%N) )]) );
            ( {| stags := NoInfo; str := "hula" |},
              (TypHeader
               [( {| stags := NoInfo; str := "dir" |}, (TypBit 1%N) );
                ( {| stags := NoInfo; str := "qdepth" |}, (TypBit 15%N) );
                ( {| stags := NoInfo; str := "digest" |}, (TypBit 32%N) )]) )]);
          (TypStruct
           [( {| stags := NoInfo; str := "index" |}, (TypBit 32%N) )])])
    [(MkExpression NoInfo
          (ExpNamelessInstantiation
               (TypSpecializedType
                    (TypTypeName {| stags := NoInfo; str := "MyParser" |})
                    nil) nil)
          (TypParser
           (MkControlType nil
                [(MkParameter false Directionless
                      (TypExtern {| stags := NoInfo; str := "packet_in" |})
                      None {| stags := NoInfo; str := "packet" |});
                 (MkParameter false Out
                      (TypStruct
                       [( {| stags := NoInfo; str := "ethernet" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "dstAddr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "srcAddr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "etherType" |},
                              (TypBit 16%N) )]) );
                        ( {| stags := NoInfo; str := "srcRoutes" |},
                          (TypArray
                               (TypHeader
                                [( {| stags := NoInfo; str := "bos" |},
                                   (TypBit 1%N) );
                                 ( {| stags := NoInfo; str := "port" |},
                                   (TypBit 15%N) )]) 9%N) );
                        ( {| stags := NoInfo; str := "ipv4" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "version" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "ihl" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "diffserv" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "totalLen" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "identification" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "flags" |},
                              (TypBit 3%N) );
                            ( {| stags := NoInfo; str := "fragOffset" |},
                              (TypBit 13%N) );
                            ( {| stags := NoInfo; str := "ttl" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "protocol" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "hdrChecksum" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "srcAddr" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "dstAddr" |},
                              (TypBit 32%N) )]) );
                        ( {| stags := NoInfo; str := "udp" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "srcPort" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "dstPort" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "length_" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "checksum" |},
                              (TypBit 16%N) )]) );
                        ( {| stags := NoInfo; str := "hula" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "dir" |},
                              (TypBit 1%N) );
                            ( {| stags := NoInfo; str := "qdepth" |},
                              (TypBit 15%N) );
                            ( {| stags := NoInfo; str := "digest" |},
                              (TypBit 32%N) )]) )]) None
                      {| stags := NoInfo; str := "hdr" |});
                 (MkParameter false InOut
                      (TypStruct
                       [( {| stags := NoInfo; str := "index" |},
                          (TypBit 32%N) )]) None
                      {| stags := NoInfo; str := "meta" |});
                 (MkParameter false InOut
                      (TypStruct
                       [( {| stags := NoInfo; str := "ingress_port" |},
                          (TypBit 9%N) );
                        ( {| stags := NoInfo; str := "egress_spec" |},
                          (TypBit 9%N) );
                        ( {| stags := NoInfo; str := "egress_port" |},
                          (TypBit 9%N) );
                        ( {| stags := NoInfo; str := "instance_type" |},
                          (TypBit 32%N) );
                        ( {| stags := NoInfo; str := "packet_length" |},
                          (TypBit 32%N) );
                        ( {| stags := NoInfo; str := "enq_timestamp" |},
                          (TypBit 32%N) );
                        ( {| stags := NoInfo; str := "enq_qdepth" |},
                          (TypBit 19%N) );
                        ( {| stags := NoInfo; str := "deq_timedelta" |},
                          (TypBit 32%N) );
                        ( {| stags := NoInfo; str := "deq_qdepth" |},
                          (TypBit 19%N) );
                        ( {| stags := NoInfo;
                             str := "ingress_global_timestamp" |},
                          (TypBit 48%N) );
                        ( {| stags := NoInfo;
                             str := "egress_global_timestamp" |},
                          (TypBit 48%N) );
                        ( {| stags := NoInfo; str := "mcast_grp" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "egress_rid" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "checksum_error" |},
                          (TypBit 1%N) );
                        ( {| stags := NoInfo; str := "parser_error" |},
                          TypError );
                        ( {| stags := NoInfo; str := "priority" |},
                          (TypBit 3%N) )]) None
                      {| stags := NoInfo; str := "standard_metadata" |})]))
          Directionless);
     (MkExpression NoInfo
          (ExpNamelessInstantiation
               (TypSpecializedType
                    (TypTypeName
                     {| stags := NoInfo; str := "MyVerifyChecksum" |}) nil)
               nil)
          (TypControl
           (MkControlType nil
                [(MkParameter false InOut
                      (TypStruct
                       [( {| stags := NoInfo; str := "ethernet" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "dstAddr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "srcAddr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "etherType" |},
                              (TypBit 16%N) )]) );
                        ( {| stags := NoInfo; str := "srcRoutes" |},
                          (TypArray
                               (TypHeader
                                [( {| stags := NoInfo; str := "bos" |},
                                   (TypBit 1%N) );
                                 ( {| stags := NoInfo; str := "port" |},
                                   (TypBit 15%N) )]) 9%N) );
                        ( {| stags := NoInfo; str := "ipv4" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "version" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "ihl" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "diffserv" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "totalLen" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "identification" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "flags" |},
                              (TypBit 3%N) );
                            ( {| stags := NoInfo; str := "fragOffset" |},
                              (TypBit 13%N) );
                            ( {| stags := NoInfo; str := "ttl" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "protocol" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "hdrChecksum" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "srcAddr" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "dstAddr" |},
                              (TypBit 32%N) )]) );
                        ( {| stags := NoInfo; str := "udp" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "srcPort" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "dstPort" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "length_" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "checksum" |},
                              (TypBit 16%N) )]) );
                        ( {| stags := NoInfo; str := "hula" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "dir" |},
                              (TypBit 1%N) );
                            ( {| stags := NoInfo; str := "qdepth" |},
                              (TypBit 15%N) );
                            ( {| stags := NoInfo; str := "digest" |},
                              (TypBit 32%N) )]) )]) None
                      {| stags := NoInfo; str := "hdr" |});
                 (MkParameter false InOut
                      (TypStruct
                       [( {| stags := NoInfo; str := "index" |},
                          (TypBit 32%N) )]) None
                      {| stags := NoInfo; str := "meta" |})])) Directionless);
     (MkExpression NoInfo
          (ExpNamelessInstantiation
               (TypSpecializedType
                    (TypTypeName {| stags := NoInfo; str := "MyIngress" |})
                    nil) nil)
          (TypControl
           (MkControlType nil
                [(MkParameter false InOut
                      (TypStruct
                       [( {| stags := NoInfo; str := "ethernet" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "dstAddr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "srcAddr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "etherType" |},
                              (TypBit 16%N) )]) );
                        ( {| stags := NoInfo; str := "srcRoutes" |},
                          (TypArray
                               (TypHeader
                                [( {| stags := NoInfo; str := "bos" |},
                                   (TypBit 1%N) );
                                 ( {| stags := NoInfo; str := "port" |},
                                   (TypBit 15%N) )]) 9%N) );
                        ( {| stags := NoInfo; str := "ipv4" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "version" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "ihl" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "diffserv" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "totalLen" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "identification" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "flags" |},
                              (TypBit 3%N) );
                            ( {| stags := NoInfo; str := "fragOffset" |},
                              (TypBit 13%N) );
                            ( {| stags := NoInfo; str := "ttl" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "protocol" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "hdrChecksum" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "srcAddr" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "dstAddr" |},
                              (TypBit 32%N) )]) );
                        ( {| stags := NoInfo; str := "udp" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "srcPort" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "dstPort" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "length_" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "checksum" |},
                              (TypBit 16%N) )]) );
                        ( {| stags := NoInfo; str := "hula" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "dir" |},
                              (TypBit 1%N) );
                            ( {| stags := NoInfo; str := "qdepth" |},
                              (TypBit 15%N) );
                            ( {| stags := NoInfo; str := "digest" |},
                              (TypBit 32%N) )]) )]) None
                      {| stags := NoInfo; str := "hdr" |});
                 (MkParameter false InOut
                      (TypStruct
                       [( {| stags := NoInfo; str := "index" |},
                          (TypBit 32%N) )]) None
                      {| stags := NoInfo; str := "meta" |});
                 (MkParameter false InOut
                      (TypStruct
                       [( {| stags := NoInfo; str := "ingress_port" |},
                          (TypBit 9%N) );
                        ( {| stags := NoInfo; str := "egress_spec" |},
                          (TypBit 9%N) );
                        ( {| stags := NoInfo; str := "egress_port" |},
                          (TypBit 9%N) );
                        ( {| stags := NoInfo; str := "instance_type" |},
                          (TypBit 32%N) );
                        ( {| stags := NoInfo; str := "packet_length" |},
                          (TypBit 32%N) );
                        ( {| stags := NoInfo; str := "enq_timestamp" |},
                          (TypBit 32%N) );
                        ( {| stags := NoInfo; str := "enq_qdepth" |},
                          (TypBit 19%N) );
                        ( {| stags := NoInfo; str := "deq_timedelta" |},
                          (TypBit 32%N) );
                        ( {| stags := NoInfo; str := "deq_qdepth" |},
                          (TypBit 19%N) );
                        ( {| stags := NoInfo;
                             str := "ingress_global_timestamp" |},
                          (TypBit 48%N) );
                        ( {| stags := NoInfo;
                             str := "egress_global_timestamp" |},
                          (TypBit 48%N) );
                        ( {| stags := NoInfo; str := "mcast_grp" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "egress_rid" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "checksum_error" |},
                          (TypBit 1%N) );
                        ( {| stags := NoInfo; str := "parser_error" |},
                          TypError );
                        ( {| stags := NoInfo; str := "priority" |},
                          (TypBit 3%N) )]) None
                      {| stags := NoInfo; str := "standard_metadata" |})]))
          Directionless);
     (MkExpression NoInfo
          (ExpNamelessInstantiation
               (TypSpecializedType
                    (TypTypeName {| stags := NoInfo; str := "MyEgress" |})
                    nil) nil)
          (TypControl
           (MkControlType nil
                [(MkParameter false InOut
                      (TypStruct
                       [( {| stags := NoInfo; str := "ethernet" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "dstAddr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "srcAddr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "etherType" |},
                              (TypBit 16%N) )]) );
                        ( {| stags := NoInfo; str := "srcRoutes" |},
                          (TypArray
                               (TypHeader
                                [( {| stags := NoInfo; str := "bos" |},
                                   (TypBit 1%N) );
                                 ( {| stags := NoInfo; str := "port" |},
                                   (TypBit 15%N) )]) 9%N) );
                        ( {| stags := NoInfo; str := "ipv4" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "version" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "ihl" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "diffserv" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "totalLen" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "identification" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "flags" |},
                              (TypBit 3%N) );
                            ( {| stags := NoInfo; str := "fragOffset" |},
                              (TypBit 13%N) );
                            ( {| stags := NoInfo; str := "ttl" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "protocol" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "hdrChecksum" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "srcAddr" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "dstAddr" |},
                              (TypBit 32%N) )]) );
                        ( {| stags := NoInfo; str := "udp" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "srcPort" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "dstPort" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "length_" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "checksum" |},
                              (TypBit 16%N) )]) );
                        ( {| stags := NoInfo; str := "hula" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "dir" |},
                              (TypBit 1%N) );
                            ( {| stags := NoInfo; str := "qdepth" |},
                              (TypBit 15%N) );
                            ( {| stags := NoInfo; str := "digest" |},
                              (TypBit 32%N) )]) )]) None
                      {| stags := NoInfo; str := "hdr" |});
                 (MkParameter false InOut
                      (TypStruct
                       [( {| stags := NoInfo; str := "index" |},
                          (TypBit 32%N) )]) None
                      {| stags := NoInfo; str := "meta" |});
                 (MkParameter false InOut
                      (TypStruct
                       [( {| stags := NoInfo; str := "ingress_port" |},
                          (TypBit 9%N) );
                        ( {| stags := NoInfo; str := "egress_spec" |},
                          (TypBit 9%N) );
                        ( {| stags := NoInfo; str := "egress_port" |},
                          (TypBit 9%N) );
                        ( {| stags := NoInfo; str := "instance_type" |},
                          (TypBit 32%N) );
                        ( {| stags := NoInfo; str := "packet_length" |},
                          (TypBit 32%N) );
                        ( {| stags := NoInfo; str := "enq_timestamp" |},
                          (TypBit 32%N) );
                        ( {| stags := NoInfo; str := "enq_qdepth" |},
                          (TypBit 19%N) );
                        ( {| stags := NoInfo; str := "deq_timedelta" |},
                          (TypBit 32%N) );
                        ( {| stags := NoInfo; str := "deq_qdepth" |},
                          (TypBit 19%N) );
                        ( {| stags := NoInfo;
                             str := "ingress_global_timestamp" |},
                          (TypBit 48%N) );
                        ( {| stags := NoInfo;
                             str := "egress_global_timestamp" |},
                          (TypBit 48%N) );
                        ( {| stags := NoInfo; str := "mcast_grp" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "egress_rid" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "checksum_error" |},
                          (TypBit 1%N) );
                        ( {| stags := NoInfo; str := "parser_error" |},
                          TypError );
                        ( {| stags := NoInfo; str := "priority" |},
                          (TypBit 3%N) )]) None
                      {| stags := NoInfo; str := "standard_metadata" |})]))
          Directionless);
     (MkExpression NoInfo
          (ExpNamelessInstantiation
               (TypSpecializedType
                    (TypTypeName
                     {| stags := NoInfo; str := "MyComputeChecksum" |}) nil)
               nil)
          (TypControl
           (MkControlType nil
                [(MkParameter false InOut
                      (TypStruct
                       [( {| stags := NoInfo; str := "ethernet" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "dstAddr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "srcAddr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "etherType" |},
                              (TypBit 16%N) )]) );
                        ( {| stags := NoInfo; str := "srcRoutes" |},
                          (TypArray
                               (TypHeader
                                [( {| stags := NoInfo; str := "bos" |},
                                   (TypBit 1%N) );
                                 ( {| stags := NoInfo; str := "port" |},
                                   (TypBit 15%N) )]) 9%N) );
                        ( {| stags := NoInfo; str := "ipv4" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "version" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "ihl" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "diffserv" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "totalLen" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "identification" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "flags" |},
                              (TypBit 3%N) );
                            ( {| stags := NoInfo; str := "fragOffset" |},
                              (TypBit 13%N) );
                            ( {| stags := NoInfo; str := "ttl" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "protocol" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "hdrChecksum" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "srcAddr" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "dstAddr" |},
                              (TypBit 32%N) )]) );
                        ( {| stags := NoInfo; str := "udp" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "srcPort" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "dstPort" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "length_" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "checksum" |},
                              (TypBit 16%N) )]) );
                        ( {| stags := NoInfo; str := "hula" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "dir" |},
                              (TypBit 1%N) );
                            ( {| stags := NoInfo; str := "qdepth" |},
                              (TypBit 15%N) );
                            ( {| stags := NoInfo; str := "digest" |},
                              (TypBit 32%N) )]) )]) None
                      {| stags := NoInfo; str := "hdr" |});
                 (MkParameter false InOut
                      (TypStruct
                       [( {| stags := NoInfo; str := "index" |},
                          (TypBit 32%N) )]) None
                      {| stags := NoInfo; str := "meta" |})])) Directionless);
     (MkExpression NoInfo
          (ExpNamelessInstantiation
               (TypSpecializedType
                    (TypTypeName {| stags := NoInfo; str := "MyDeparser" |})
                    nil) nil)
          (TypControl
           (MkControlType nil
                [(MkParameter false Directionless
                      (TypExtern {| stags := NoInfo; str := "packet_out" |})
                      None {| stags := NoInfo; str := "packet" |});
                 (MkParameter false In
                      (TypStruct
                       [( {| stags := NoInfo; str := "ethernet" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "dstAddr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "srcAddr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "etherType" |},
                              (TypBit 16%N) )]) );
                        ( {| stags := NoInfo; str := "srcRoutes" |},
                          (TypArray
                               (TypHeader
                                [( {| stags := NoInfo; str := "bos" |},
                                   (TypBit 1%N) );
                                 ( {| stags := NoInfo; str := "port" |},
                                   (TypBit 15%N) )]) 9%N) );
                        ( {| stags := NoInfo; str := "ipv4" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "version" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "ihl" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "diffserv" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "totalLen" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "identification" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "flags" |},
                              (TypBit 3%N) );
                            ( {| stags := NoInfo; str := "fragOffset" |},
                              (TypBit 13%N) );
                            ( {| stags := NoInfo; str := "ttl" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "protocol" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "hdrChecksum" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "srcAddr" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "dstAddr" |},
                              (TypBit 32%N) )]) );
                        ( {| stags := NoInfo; str := "udp" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "srcPort" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "dstPort" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "length_" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "checksum" |},
                              (TypBit 16%N) )]) );
                        ( {| stags := NoInfo; str := "hula" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "dir" |},
                              (TypBit 1%N) );
                            ( {| stags := NoInfo; str := "qdepth" |},
                              (TypBit 15%N) );
                            ( {| stags := NoInfo; str := "digest" |},
                              (TypBit 32%N) )]) )]) None
                      {| stags := NoInfo; str := "hdr" |})])) Directionless)]
    {| stags := NoInfo; str := "main" |} nil.

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
     ComputeChecksum; Deparser; V1Switch; egressSpec_t; macAddr_t; ip4Addr_t;
     qdepth_t; digest_t; ethernet_t; srcRoute_t; hula_t; ipv4_t; udp_t;
     metadata; headers; MyParser; MyVerifyChecksum; MyIngress; MyEgress;
     MyComputeChecksum; MyDeparser; main].


