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
    [(ProtoMethod NoInfo (TypBit 32) {| stags := NoInfo; str := "length" |}
          nil nil);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "advance" |} nil
          [(MkParameter false In (TypBit 32) None
                {| stags := NoInfo; str := "sizeInBits" |})]);
     (ProtoMethod NoInfo
          (TypTypeName (BareName {| stags := NoInfo; str := "T1" |}))
          {| stags := NoInfo; str := "lookahead" |}
          [{| stags := NoInfo; str := "T1" |}] nil);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "extract" |}
          [{| stags := NoInfo; str := "T0" |}]
          [(MkParameter false Out
                (TypTypeName (BareName {| stags := NoInfo; str := "T0" |}))
                None {| stags := NoInfo; str := "variableSizeHeader" |});
           (MkParameter false In (TypBit 32) None
                {| stags := NoInfo; str := "variableFieldSizeInBits" |})]);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "extract" |}
          [{| stags := NoInfo; str := "T" |}]
          [(MkParameter false Out
                (TypTypeName (BareName {| stags := NoInfo; str := "T" |}))
                None {| stags := NoInfo; str := "hdr" |})])].

Definition packet_out := DeclExternObject NoInfo
    {| stags := NoInfo; str := "packet_out" |} nil
    [(ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "emit" |}
          [{| stags := NoInfo; str := "T2" |}]
          [(MkParameter false In
                (TypTypeName (BareName {| stags := NoInfo; str := "T2" |}))
                None {| stags := NoInfo; str := "hdr" |})])].

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
    [(MkDeclarationField NoInfo (TypBit 9)
          {| stags := NoInfo; str := "ingress_port" |});
     (MkDeclarationField NoInfo (TypBit 9)
          {| stags := NoInfo; str := "egress_spec" |});
     (MkDeclarationField NoInfo (TypBit 9)
          {| stags := NoInfo; str := "egress_port" |});
     (MkDeclarationField NoInfo (TypBit 32)
          {| stags := NoInfo; str := "instance_type" |});
     (MkDeclarationField NoInfo (TypBit 32)
          {| stags := NoInfo; str := "packet_length" |});
     (MkDeclarationField NoInfo (TypBit 32)
          {| stags := NoInfo; str := "enq_timestamp" |});
     (MkDeclarationField NoInfo (TypBit 19)
          {| stags := NoInfo; str := "enq_qdepth" |});
     (MkDeclarationField NoInfo (TypBit 32)
          {| stags := NoInfo; str := "deq_timedelta" |});
     (MkDeclarationField NoInfo (TypBit 19)
          {| stags := NoInfo; str := "deq_qdepth" |});
     (MkDeclarationField NoInfo (TypBit 48)
          {| stags := NoInfo; str := "ingress_global_timestamp" |});
     (MkDeclarationField NoInfo (TypBit 48)
          {| stags := NoInfo; str := "egress_global_timestamp" |});
     (MkDeclarationField NoInfo (TypBit 16)
          {| stags := NoInfo; str := "mcast_grp" |});
     (MkDeclarationField NoInfo (TypBit 16)
          {| stags := NoInfo; str := "egress_rid" |});
     (MkDeclarationField NoInfo (TypBit 1)
          {| stags := NoInfo; str := "checksum_error" |});
     (MkDeclarationField NoInfo TypError
          {| stags := NoInfo; str := "parser_error" |});
     (MkDeclarationField NoInfo (TypBit 3)
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
          [(MkParameter false Directionless (TypBit 32) None
                {| stags := NoInfo; str := "size" |});
           (MkParameter false Directionless
                (TypTypeName
                 (BareName {| stags := NoInfo; str := "CounterType" |}))
                None {| stags := NoInfo; str := "type" |})]);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "count" |} nil
          [(MkParameter false In (TypBit 32) None
                {| stags := NoInfo; str := "index" |})])].

Definition direct_counter := DeclExternObject NoInfo
    {| stags := NoInfo; str := "direct_counter" |} nil
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "direct_counter" |}
          [(MkParameter false Directionless
                (TypTypeName
                 (BareName {| stags := NoInfo; str := "CounterType" |}))
                None {| stags := NoInfo; str := "type" |})]);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "count" |} nil
          nil)].

Definition meter := DeclExternObject NoInfo
    {| stags := NoInfo; str := "meter" |} nil
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "meter" |}
          [(MkParameter false Directionless (TypBit 32) None
                {| stags := NoInfo; str := "size" |});
           (MkParameter false Directionless
                (TypTypeName
                 (BareName {| stags := NoInfo; str := "MeterType" |}))
                None {| stags := NoInfo; str := "type" |})]);
     (ProtoMethod NoInfo TypVoid
          {| stags := NoInfo; str := "execute_meter" |}
          [{| stags := NoInfo; str := "T3" |}]
          [(MkParameter false In (TypBit 32) None
                {| stags := NoInfo; str := "index" |});
           (MkParameter false Out
                (TypTypeName (BareName {| stags := NoInfo; str := "T3" |}))
                None {| stags := NoInfo; str := "result" |})])].

Definition direct_meter := DeclExternObject NoInfo
    {| stags := NoInfo; str := "direct_meter" |}
    [{| stags := NoInfo; str := "T4" |}]
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "direct_meter" |}
          [(MkParameter false Directionless
                (TypTypeName
                 (BareName {| stags := NoInfo; str := "MeterType" |}))
                None {| stags := NoInfo; str := "type" |})]);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "read" |} nil
          [(MkParameter false Out
                (TypTypeName (BareName {| stags := NoInfo; str := "T4" |}))
                None {| stags := NoInfo; str := "result" |})])].

Definition register := DeclExternObject NoInfo
    {| stags := NoInfo; str := "register" |}
    [{| stags := NoInfo; str := "T5" |}]
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "register" |}
          [(MkParameter false Directionless (TypBit 32) None
                {| stags := NoInfo; str := "size" |})]);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "write" |} nil
          [(MkParameter false In (TypBit 32) None
                {| stags := NoInfo; str := "index" |});
           (MkParameter false In
                (TypTypeName (BareName {| stags := NoInfo; str := "T5" |}))
                None {| stags := NoInfo; str := "value" |})]);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "read" |} nil
          [(MkParameter false Out
                (TypTypeName (BareName {| stags := NoInfo; str := "T5" |}))
                None {| stags := NoInfo; str := "result" |});
           (MkParameter false In (TypBit 32) None
                {| stags := NoInfo; str := "index" |})])].

Definition action_profile := DeclExternObject NoInfo
    {| stags := NoInfo; str := "action_profile" |} nil
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "action_profile" |}
          [(MkParameter false Directionless (TypBit 32) None
                {| stags := NoInfo; str := "size" |})])].

Definition random'result'lo'hi := DeclExternFunction NoInfo TypVoid
    {| stags := NoInfo; str := "random" |}
    [{| stags := NoInfo; str := "T6" |}]
    [(MkParameter false Out
          (TypTypeName (BareName {| stags := NoInfo; str := "T6" |}))
          None {| stags := NoInfo; str := "result" |});
     (MkParameter false In
          (TypTypeName (BareName {| stags := NoInfo; str := "T6" |}))
          None {| stags := NoInfo; str := "lo" |});
     (MkParameter false In
          (TypTypeName (BareName {| stags := NoInfo; str := "T6" |}))
          None {| stags := NoInfo; str := "hi" |})].

Definition digest'receiver'data := DeclExternFunction NoInfo TypVoid
    {| stags := NoInfo; str := "digest" |}
    [{| stags := NoInfo; str := "T7" |}]
    [(MkParameter false In (TypBit 32) None
          {| stags := NoInfo; str := "receiver" |});
     (MkParameter false In
          (TypTypeName (BareName {| stags := NoInfo; str := "T7" |}))
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
          (TypTypeName
           (BareName {| stags := NoInfo; str := "standard_metadata_t" |}))
          None {| stags := NoInfo; str := "standard_metadata" |})].

Definition hash'result'algo'base'data'max := DeclExternFunction NoInfo
    TypVoid {| stags := NoInfo; str := "hash" |}
    [{| stags := NoInfo; str := "O" |}; {| stags := NoInfo; str := "T8" |};
     {| stags := NoInfo; str := "D" |}; {| stags := NoInfo; str := "M" |}]
    [(MkParameter false Out
          (TypTypeName (BareName {| stags := NoInfo; str := "O" |}))
          None {| stags := NoInfo; str := "result" |});
     (MkParameter false In
          (TypTypeName
           (BareName {| stags := NoInfo; str := "HashAlgorithm" |}))
          None {| stags := NoInfo; str := "algo" |});
     (MkParameter false In
          (TypTypeName (BareName {| stags := NoInfo; str := "T8" |}))
          None {| stags := NoInfo; str := "base" |});
     (MkParameter false In
          (TypTypeName (BareName {| stags := NoInfo; str := "D" |}))
          None {| stags := NoInfo; str := "data" |});
     (MkParameter false In
          (TypTypeName (BareName {| stags := NoInfo; str := "M" |}))
          None {| stags := NoInfo; str := "max" |})].

Definition action_selector := DeclExternObject NoInfo
    {| stags := NoInfo; str := "action_selector" |} nil
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "action_selector" |}
          [(MkParameter false Directionless
                (TypTypeName
                 (BareName {| stags := NoInfo; str := "HashAlgorithm" |}))
                None {| stags := NoInfo; str := "algorithm" |});
           (MkParameter false Directionless (TypBit 32) None
                {| stags := NoInfo; str := "size" |});
           (MkParameter false Directionless (TypBit 32) None
                {| stags := NoInfo; str := "outputWidth" |})])].

Definition CloneType := DeclEnum NoInfo
    {| stags := NoInfo; str := "CloneType" |}
    [{| stags := NoInfo; str := "I2E" |};
     {| stags := NoInfo; str := "E2E" |}].

Definition Checksum16 := DeclExternObject NoInfo
    {| stags := NoInfo; str := "Checksum16" |} nil
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "Checksum16" |} nil);
     (ProtoMethod NoInfo (TypBit 16) {| stags := NoInfo; str := "get" |}
          [{| stags := NoInfo; str := "D9" |}]
          [(MkParameter false In
                (TypTypeName (BareName {| stags := NoInfo; str := "D9" |}))
                None {| stags := NoInfo; str := "data" |})])].

Definition verify_checksum'condition'data'checksum'algo := DeclExternFunction
    NoInfo TypVoid {| stags := NoInfo; str := "verify_checksum" |}
    [{| stags := NoInfo; str := "T10" |};
     {| stags := NoInfo; str := "O11" |}]
    [(MkParameter false In TypBool None
          {| stags := NoInfo; str := "condition" |});
     (MkParameter false In
          (TypTypeName (BareName {| stags := NoInfo; str := "T10" |}))
          None {| stags := NoInfo; str := "data" |});
     (MkParameter false In
          (TypTypeName (BareName {| stags := NoInfo; str := "O11" |}))
          None {| stags := NoInfo; str := "checksum" |});
     (MkParameter false Directionless
          (TypTypeName
           (BareName {| stags := NoInfo; str := "HashAlgorithm" |}))
          None {| stags := NoInfo; str := "algo" |})].

Definition update_checksum'condition'data'checksum'algo := DeclExternFunction
    NoInfo TypVoid {| stags := NoInfo; str := "update_checksum" |}
    [{| stags := NoInfo; str := "T12" |};
     {| stags := NoInfo; str := "O13" |}]
    [(MkParameter false In TypBool None
          {| stags := NoInfo; str := "condition" |});
     (MkParameter false In
          (TypTypeName (BareName {| stags := NoInfo; str := "T12" |}))
          None {| stags := NoInfo; str := "data" |});
     (MkParameter false InOut
          (TypTypeName (BareName {| stags := NoInfo; str := "O13" |}))
          None {| stags := NoInfo; str := "checksum" |});
     (MkParameter false Directionless
          (TypTypeName
           (BareName {| stags := NoInfo; str := "HashAlgorithm" |}))
          None {| stags := NoInfo; str := "algo" |})].

Definition verify_checksum_with_payload'condition'data'checksum'algo := DeclExternFunction
    NoInfo TypVoid
    {| stags := NoInfo; str := "verify_checksum_with_payload" |}
    [{| stags := NoInfo; str := "T14" |};
     {| stags := NoInfo; str := "O15" |}]
    [(MkParameter false In TypBool None
          {| stags := NoInfo; str := "condition" |});
     (MkParameter false In
          (TypTypeName (BareName {| stags := NoInfo; str := "T14" |}))
          None {| stags := NoInfo; str := "data" |});
     (MkParameter false In
          (TypTypeName (BareName {| stags := NoInfo; str := "O15" |}))
          None {| stags := NoInfo; str := "checksum" |});
     (MkParameter false Directionless
          (TypTypeName
           (BareName {| stags := NoInfo; str := "HashAlgorithm" |}))
          None {| stags := NoInfo; str := "algo" |})].

Definition update_checksum_with_payload'condition'data'checksum'algo := DeclExternFunction
    NoInfo TypVoid
    {| stags := NoInfo; str := "update_checksum_with_payload" |}
    [{| stags := NoInfo; str := "T16" |};
     {| stags := NoInfo; str := "O17" |}]
    [(MkParameter false In TypBool None
          {| stags := NoInfo; str := "condition" |});
     (MkParameter false In
          (TypTypeName (BareName {| stags := NoInfo; str := "T16" |}))
          None {| stags := NoInfo; str := "data" |});
     (MkParameter false InOut
          (TypTypeName (BareName {| stags := NoInfo; str := "O17" |}))
          None {| stags := NoInfo; str := "checksum" |});
     (MkParameter false Directionless
          (TypTypeName
           (BareName {| stags := NoInfo; str := "HashAlgorithm" |}))
          None {| stags := NoInfo; str := "algo" |})].

Definition resubmit'data := DeclExternFunction NoInfo TypVoid
    {| stags := NoInfo; str := "resubmit" |}
    [{| stags := NoInfo; str := "T18" |}]
    [(MkParameter false In
          (TypTypeName (BareName {| stags := NoInfo; str := "T18" |}))
          None {| stags := NoInfo; str := "data" |})].

Definition recirculate'data := DeclExternFunction NoInfo TypVoid
    {| stags := NoInfo; str := "recirculate" |}
    [{| stags := NoInfo; str := "T19" |}]
    [(MkParameter false In
          (TypTypeName (BareName {| stags := NoInfo; str := "T19" |}))
          None {| stags := NoInfo; str := "data" |})].

Definition clone'type'session := DeclExternFunction NoInfo TypVoid
    {| stags := NoInfo; str := "clone" |} nil
    [(MkParameter false In
          (TypTypeName (BareName {| stags := NoInfo; str := "CloneType" |}))
          None {| stags := NoInfo; str := "type" |});
     (MkParameter false In (TypBit 32) None
          {| stags := NoInfo; str := "session" |})].

Definition clone3'type'session'data := DeclExternFunction NoInfo TypVoid
    {| stags := NoInfo; str := "clone3" |}
    [{| stags := NoInfo; str := "T20" |}]
    [(MkParameter false In
          (TypTypeName (BareName {| stags := NoInfo; str := "CloneType" |}))
          None {| stags := NoInfo; str := "type" |});
     (MkParameter false In (TypBit 32) None
          {| stags := NoInfo; str := "session" |});
     (MkParameter false In
          (TypTypeName (BareName {| stags := NoInfo; str := "T20" |}))
          None {| stags := NoInfo; str := "data" |})].

Definition truncate'length := DeclExternFunction NoInfo TypVoid
    {| stags := NoInfo; str := "truncate" |} nil
    [(MkParameter false In (TypBit 32) None
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
     (MkParameter false In
          (TypTypeName (BareName {| stags := NoInfo; str := "T21" |}))
          None {| stags := NoInfo; str := "data" |})].

Definition Parser := DeclParserType NoInfo
    {| stags := NoInfo; str := "Parser" |}
    [{| stags := NoInfo; str := "H" |}; {| stags := NoInfo; str := "M22" |}]
    [(MkParameter false Directionless
          (TypTypeName (BareName {| stags := NoInfo; str := "packet_in" |}))
          None {| stags := NoInfo; str := "b" |});
     (MkParameter false Out
          (TypTypeName (BareName {| stags := NoInfo; str := "H" |}))
          None {| stags := NoInfo; str := "parsedHdr" |});
     (MkParameter false InOut
          (TypTypeName (BareName {| stags := NoInfo; str := "M22" |}))
          None {| stags := NoInfo; str := "meta" |});
     (MkParameter false InOut
          (TypTypeName
           (BareName {| stags := NoInfo; str := "standard_metadata_t" |}))
          None {| stags := NoInfo; str := "standard_metadata" |})].

Definition VerifyChecksum := DeclControlType NoInfo
    {| stags := NoInfo; str := "VerifyChecksum" |}
    [{| stags := NoInfo; str := "H23" |};
     {| stags := NoInfo; str := "M24" |}]
    [(MkParameter false InOut
          (TypTypeName (BareName {| stags := NoInfo; str := "H23" |}))
          None {| stags := NoInfo; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName (BareName {| stags := NoInfo; str := "M24" |}))
          None {| stags := NoInfo; str := "meta" |})].

Definition Ingress := DeclControlType NoInfo
    {| stags := NoInfo; str := "Ingress" |}
    [{| stags := NoInfo; str := "H25" |};
     {| stags := NoInfo; str := "M26" |}]
    [(MkParameter false InOut
          (TypTypeName (BareName {| stags := NoInfo; str := "H25" |}))
          None {| stags := NoInfo; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName (BareName {| stags := NoInfo; str := "M26" |}))
          None {| stags := NoInfo; str := "meta" |});
     (MkParameter false InOut
          (TypTypeName
           (BareName {| stags := NoInfo; str := "standard_metadata_t" |}))
          None {| stags := NoInfo; str := "standard_metadata" |})].

Definition Egress := DeclControlType NoInfo
    {| stags := NoInfo; str := "Egress" |}
    [{| stags := NoInfo; str := "H27" |};
     {| stags := NoInfo; str := "M28" |}]
    [(MkParameter false InOut
          (TypTypeName (BareName {| stags := NoInfo; str := "H27" |}))
          None {| stags := NoInfo; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName (BareName {| stags := NoInfo; str := "M28" |}))
          None {| stags := NoInfo; str := "meta" |});
     (MkParameter false InOut
          (TypTypeName
           (BareName {| stags := NoInfo; str := "standard_metadata_t" |}))
          None {| stags := NoInfo; str := "standard_metadata" |})].

Definition ComputeChecksum := DeclControlType NoInfo
    {| stags := NoInfo; str := "ComputeChecksum" |}
    [{| stags := NoInfo; str := "H29" |};
     {| stags := NoInfo; str := "M30" |}]
    [(MkParameter false InOut
          (TypTypeName (BareName {| stags := NoInfo; str := "H29" |}))
          None {| stags := NoInfo; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName (BareName {| stags := NoInfo; str := "M30" |}))
          None {| stags := NoInfo; str := "meta" |})].

Definition Deparser := DeclControlType NoInfo
    {| stags := NoInfo; str := "Deparser" |}
    [{| stags := NoInfo; str := "H31" |}]
    [(MkParameter false Directionless
          (TypTypeName (BareName {| stags := NoInfo; str := "packet_out" |}))
          None {| stags := NoInfo; str := "b" |});
     (MkParameter false In
          (TypTypeName (BareName {| stags := NoInfo; str := "H31" |}))
          None {| stags := NoInfo; str := "hdr" |})].

Definition V1Switch := DeclPackageType NoInfo
    {| stags := NoInfo; str := "V1Switch" |}
    [{| stags := NoInfo; str := "H32" |};
     {| stags := NoInfo; str := "M33" |}]
    [(MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName
                (BareName {| stags := NoInfo; str := "Parser" |}))
               [(TypTypeName (BareName {| stags := NoInfo; str := "H32" |}));
                (TypTypeName (BareName {| stags := NoInfo; str := "M33" |}))])
          None {| stags := NoInfo; str := "p" |});
     (MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName
                (BareName {| stags := NoInfo; str := "VerifyChecksum" |}))
               [(TypTypeName (BareName {| stags := NoInfo; str := "H32" |}));
                (TypTypeName (BareName {| stags := NoInfo; str := "M33" |}))])
          None {| stags := NoInfo; str := "vr" |});
     (MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName
                (BareName {| stags := NoInfo; str := "Ingress" |}))
               [(TypTypeName (BareName {| stags := NoInfo; str := "H32" |}));
                (TypTypeName (BareName {| stags := NoInfo; str := "M33" |}))])
          None {| stags := NoInfo; str := "ig" |});
     (MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName
                (BareName {| stags := NoInfo; str := "Egress" |}))
               [(TypTypeName (BareName {| stags := NoInfo; str := "H32" |}));
                (TypTypeName (BareName {| stags := NoInfo; str := "M33" |}))])
          None {| stags := NoInfo; str := "eg" |});
     (MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName
                (BareName {| stags := NoInfo; str := "ComputeChecksum" |}))
               [(TypTypeName (BareName {| stags := NoInfo; str := "H32" |}));
                (TypTypeName (BareName {| stags := NoInfo; str := "M33" |}))])
          None {| stags := NoInfo; str := "ck" |});
     (MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName
                (BareName {| stags := NoInfo; str := "Deparser" |}))
               [(TypTypeName (BareName {| stags := NoInfo; str := "H32" |}))])
          None {| stags := NoInfo; str := "dep" |})].

Definition silly_combined_hdr := DeclHeader NoInfo
    {| stags := NoInfo; str := "silly_combined_hdr" |}
    [(MkDeclarationField NoInfo (TypBit 8)
          {| stags := NoInfo; str := "src" |});
     (MkDeclarationField NoInfo (TypBit 8)
          {| stags := NoInfo; str := "dst" |});
     (MkDeclarationField NoInfo (TypBit 4)
          {| stags := NoInfo; str := "proto" |});
     (MkDeclarationField NoInfo (TypBit 8)
          {| stags := NoInfo; str := "t_or_u_sport" |});
     (MkDeclarationField NoInfo (TypBit 8)
          {| stags := NoInfo; str := "t_or_u_dport" |});
     (MkDeclarationField NoInfo (TypBit 4)
          {| stags := NoInfo; str := "t_or_u_flags" |})].

Definition tcp_seq_suffix := DeclHeader NoInfo
    {| stags := NoInfo; str := "tcp_seq_suffix" |}
    [(MkDeclarationField NoInfo (TypBit 8)
          {| stags := NoInfo; str := "seq" |})].

Definition metadata := DeclStruct NoInfo
    {| stags := NoInfo; str := "metadata" |} nil.

Definition headers := DeclStruct NoInfo
    {| stags := NoInfo; str := "headers" |}
    [(MkDeclarationField NoInfo
          (TypHeader
           [(MkFieldType {| stags := NoInfo; str := "src" |} (TypBit 8));
            (MkFieldType {| stags := NoInfo; str := "dst" |} (TypBit 8));
            (MkFieldType {| stags := NoInfo; str := "proto" |} (TypBit 4));
            (MkFieldType {| stags := NoInfo; str := "t_or_u_sport" |}
                 (TypBit 8));
            (MkFieldType {| stags := NoInfo; str := "t_or_u_dport" |}
                 (TypBit 8));
            (MkFieldType {| stags := NoInfo; str := "t_or_u_flags" |}
                 (TypBit 4))]) {| stags := NoInfo; str := "comb" |});
     (MkDeclarationField NoInfo
          (TypHeader
           [(MkFieldType {| stags := NoInfo; str := "seq" |} (TypBit 8))])
          {| stags := NoInfo; str := "opt_suff" |})].

Definition MyParser := DeclParser NoInfo
    {| stags := NoInfo; str := "MyParser" |} nil
    [(MkParameter false Directionless
          (TypTypeName (BareName {| stags := NoInfo; str := "packet_in" |}))
          None {| stags := NoInfo; str := "packet" |});
     (MkParameter false Out
          (TypTypeName (BareName {| stags := NoInfo; str := "headers" |}))
          None {| stags := NoInfo; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName (BareName {| stags := NoInfo; str := "metadata" |}))
          None {| stags := NoInfo; str := "meta" |});
     (MkParameter false InOut
          (TypTypeName
           (BareName {| stags := NoInfo; str := "standard_metadata_t" |}))
          None {| stags := NoInfo; str := "standard_metadata" |})] nil nil
    [(MkParserState NoInfo {| stags := NoInfo; str := "start" |}
          [(MkStatement NoInfo
                (StatMethodCall
                     (MkExpression NoInfo
                          (ExpExpressionMember
                               (MkExpression NoInfo
                                    (ExpName
                                     (BareName
                                      {| stags := NoInfo; str := "packet" |}))
                                    (TypTypeName
                                     (BareName
                                      {| stags := NoInfo;
                                         str := "packet_in" |}))
                                    Directionless)
                               {| stags := NoInfo; str := "extract" |})
                          (TypFunction
                           (MkFunctionType
                                [{| stags := NoInfo; str := "T" |}]
                                [(MkParameter false Out
                                      (TypTypeName
                                       (BareName
                                        {| stags := NoInfo; str := "T" |}))
                                      None
                                      {| stags := NoInfo; str := "hdr" |})]
                                FunExtern TypVoid)) Directionless)
                     [(TypHeader
                       [(MkFieldType {| stags := NoInfo; str := "src" |}
                             (TypBit 8));
                        (MkFieldType {| stags := NoInfo; str := "dst" |}
                             (TypBit 8));
                        (MkFieldType {| stags := NoInfo; str := "proto" |}
                             (TypBit 4));
                        (MkFieldType
                             {| stags := NoInfo; str := "t_or_u_sport" |}
                             (TypBit 8));
                        (MkFieldType
                             {| stags := NoInfo; str := "t_or_u_dport" |}
                             (TypBit 8));
                        (MkFieldType
                             {| stags := NoInfo; str := "t_or_u_flags" |}
                             (TypBit 4))])]
                     [(Some
                       (MkExpression NoInfo
                            (ExpExpressionMember
                                 (MkExpression NoInfo
                                      (ExpName
                                       (BareName
                                        {| stags := NoInfo; str := "hdr" |}))
                                      (TypTypeName
                                       (BareName
                                        {| stags := NoInfo;
                                           str := "headers" |})) Out)
                                 {| stags := NoInfo; str := "comb" |})
                            (TypHeader
                             [(MkFieldType
                                   {| stags := NoInfo; str := "src" |}
                                   (TypBit 8));
                              (MkFieldType
                                   {| stags := NoInfo; str := "dst" |}
                                   (TypBit 8));
                              (MkFieldType
                                   {| stags := NoInfo; str := "proto" |}
                                   (TypBit 4));
                              (MkFieldType
                                   {| stags := NoInfo;
                                      str := "t_or_u_sport" |} (TypBit 8));
                              (MkFieldType
                                   {| stags := NoInfo;
                                      str := "t_or_u_dport" |} (TypBit 8));
                              (MkFieldType
                                   {| stags := NoInfo;
                                      str := "t_or_u_flags" |} (TypBit 4))])
                            Directionless))]) StmUnit)]
          (ParserSelect NoInfo
               [(MkExpression NoInfo
                     (ExpExpressionMember
                          (MkExpression NoInfo
                               (ExpExpressionMember
                                    (MkExpression NoInfo
                                         (ExpName
                                          (BareName
                                           {| stags := NoInfo;
                                              str := "hdr" |}))
                                         (TypTypeName
                                          (BareName
                                           {| stags := NoInfo;
                                              str := "headers" |})) Out)
                                    {| stags := NoInfo; str := "comb" |})
                               (TypHeader
                                [(MkFieldType
                                      {| stags := NoInfo; str := "src" |}
                                      (TypBit 8));
                                 (MkFieldType
                                      {| stags := NoInfo; str := "dst" |}
                                      (TypBit 8));
                                 (MkFieldType
                                      {| stags := NoInfo; str := "proto" |}
                                      (TypBit 4));
                                 (MkFieldType
                                      {| stags := NoInfo;
                                         str := "t_or_u_sport" |} (TypBit 8));
                                 (MkFieldType
                                      {| stags := NoInfo;
                                         str := "t_or_u_dport" |} (TypBit 8));
                                 (MkFieldType
                                      {| stags := NoInfo;
                                         str := "t_or_u_flags" |} (TypBit 4))])
                               Directionless)
                          {| stags := NoInfo; str := "proto" |}) (TypBit 4)
                     Directionless)]
               [(MkParserCase NoInfo
                     [(MkMatch NoInfo
                           (MatchExpression
                            (MkExpression NoInfo
                                 (ExpCast (TypSet (TypBit 4))
                                      (MkExpression NoInfo
                                           (ExpCast (TypBit 4)
                                                (MkExpression NoInfo
                                                     (ExpInt
                                                      {| itags := NoInfo;
                                                         value := 1;
                                                         width_signed :=
                                                         None |}) TypInteger
                                                     Directionless))
                                           (TypBit 4) Directionless))
                                 (TypSet (TypBit 4)) Directionless))
                           (TypSet (TypSet (TypBit 4))))]
                     {| stags := NoInfo; str := "accept" |});
                (MkParserCase NoInfo
                     [(MkMatch NoInfo
                           (MatchExpression
                            (MkExpression NoInfo
                                 (ExpCast (TypSet (TypBit 4))
                                      (MkExpression NoInfo
                                           (ExpCast (TypBit 4)
                                                (MkExpression NoInfo
                                                     (ExpInt
                                                      {| itags := NoInfo;
                                                         value := 0;
                                                         width_signed :=
                                                         None |}) TypInteger
                                                     Directionless))
                                           (TypBit 4) Directionless))
                                 (TypSet (TypBit 4)) Directionless))
                           (TypSet (TypSet (TypBit 4))))]
                     {| stags := NoInfo; str := "parse_tcp" |});
                (MkParserCase NoInfo
                     [(MkMatch NoInfo MatchDontCare (TypSet (TypBit 4)))]
                     {| stags := NoInfo; str := "reject" |})]));
     (MkParserState NoInfo {| stags := NoInfo; str := "parse_tcp" |}
          [(MkStatement NoInfo
                (StatMethodCall
                     (MkExpression NoInfo
                          (ExpExpressionMember
                               (MkExpression NoInfo
                                    (ExpName
                                     (BareName
                                      {| stags := NoInfo; str := "packet" |}))
                                    (TypTypeName
                                     (BareName
                                      {| stags := NoInfo;
                                         str := "packet_in" |}))
                                    Directionless)
                               {| stags := NoInfo; str := "extract" |})
                          (TypFunction
                           (MkFunctionType
                                [{| stags := NoInfo; str := "T" |}]
                                [(MkParameter false Out
                                      (TypTypeName
                                       (BareName
                                        {| stags := NoInfo; str := "T" |}))
                                      None
                                      {| stags := NoInfo; str := "hdr" |})]
                                FunExtern TypVoid)) Directionless)
                     [(TypHeader
                       [(MkFieldType {| stags := NoInfo; str := "seq" |}
                             (TypBit 8))])]
                     [(Some
                       (MkExpression NoInfo
                            (ExpExpressionMember
                                 (MkExpression NoInfo
                                      (ExpName
                                       (BareName
                                        {| stags := NoInfo; str := "hdr" |}))
                                      (TypTypeName
                                       (BareName
                                        {| stags := NoInfo;
                                           str := "headers" |})) Out)
                                 {| stags := NoInfo; str := "opt_suff" |})
                            (TypHeader
                             [(MkFieldType
                                   {| stags := NoInfo; str := "seq" |}
                                   (TypBit 8))]) Directionless))]) StmUnit)]
          (ParserDirect NoInfo {| stags := NoInfo; str := "accept" |}))].

Definition MyChecksum := DeclControl NoInfo
    {| stags := NoInfo; str := "MyChecksum" |} nil
    [(MkParameter false InOut
          (TypTypeName (BareName {| stags := NoInfo; str := "headers" |}))
          None {| stags := NoInfo; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName (BareName {| stags := NoInfo; str := "metadata" |}))
          None {| stags := NoInfo; str := "meta" |})] nil nil
    (BlockEmpty NoInfo).

Definition MyIngress := DeclControl NoInfo
    {| stags := NoInfo; str := "MyIngress" |} nil
    [(MkParameter false InOut
          (TypTypeName (BareName {| stags := NoInfo; str := "headers" |}))
          None {| stags := NoInfo; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName (BareName {| stags := NoInfo; str := "metadata" |}))
          None {| stags := NoInfo; str := "meta" |});
     (MkParameter false InOut
          (TypTypeName
           (BareName {| stags := NoInfo; str := "standard_metadata_t" |}))
          None {| stags := NoInfo; str := "standard_metadata" |})] nil nil
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
                                                           str := "hdr" |}))
                                                      (TypTypeName
                                                       (BareName
                                                        {| stags := NoInfo;
                                                           str := "headers" |}))
                                                      InOut)
                                                 {| stags := NoInfo;
                                                    str := "opt_suff" |})
                                            (TypHeader
                                             [(MkFieldType
                                                   {| stags := NoInfo;
                                                      str := "seq" |}
                                                   (TypBit 8))])
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
                                   (StatAssignment
                                        (MkExpression NoInfo
                                             (ExpExpressionMember
                                                  (MkExpression NoInfo
                                                       (ExpName
                                                        (BareName
                                                         {| stags := NoInfo;
                                                            str := "standard_metadata" |}))
                                                       (TypTypeName
                                                        (BareName
                                                         {| stags := NoInfo;
                                                            str := "standard_metadata_t" |}))
                                                       InOut)
                                                  {| stags := NoInfo;
                                                     str := "egress_spec" |})
                                             (TypBit 9) Directionless)
                                        (MkExpression NoInfo
                                             (ExpCast (TypBit 9)
                                                  (MkExpression NoInfo
                                                       (ExpInt
                                                        {| itags := NoInfo;
                                                           value := 0;
                                                           width_signed :=
                                                           None |})
                                                       TypInteger
                                                       Directionless))
                                             (TypBit 9) Directionless))
                                   StmUnit) (BlockEmpty NoInfo))) StmUnit)
                   (Some
                    (MkStatement NoInfo
                         (StatBlock
                          (BlockCons
                               (MkStatement NoInfo
                                    (StatAssignment
                                         (MkExpression NoInfo
                                              (ExpExpressionMember
                                                   (MkExpression NoInfo
                                                        (ExpName
                                                         (BareName
                                                          {| stags := NoInfo;
                                                             str := "standard_metadata" |}))
                                                        (TypTypeName
                                                         (BareName
                                                          {| stags := NoInfo;
                                                             str := "standard_metadata_t" |}))
                                                        InOut)
                                                   {| stags := NoInfo;
                                                      str := "egress_spec" |})
                                              (TypBit 9) Directionless)
                                         (MkExpression NoInfo
                                              (ExpCast (TypBit 9)
                                                   (MkExpression NoInfo
                                                        (ExpInt
                                                         {| itags := NoInfo;
                                                            value := 1;
                                                            width_signed :=
                                                            None |})
                                                        TypInteger
                                                        Directionless))
                                              (TypBit 9) Directionless))
                                    StmUnit) (BlockEmpty NoInfo))) StmUnit)))
              StmUnit) (BlockEmpty NoInfo)).

Definition MyEgress := DeclControl NoInfo
    {| stags := NoInfo; str := "MyEgress" |} nil
    [(MkParameter false InOut
          (TypTypeName (BareName {| stags := NoInfo; str := "headers" |}))
          None {| stags := NoInfo; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName (BareName {| stags := NoInfo; str := "metadata" |}))
          None {| stags := NoInfo; str := "meta" |});
     (MkParameter false InOut
          (TypTypeName
           (BareName {| stags := NoInfo; str := "standard_metadata_t" |}))
          None {| stags := NoInfo; str := "standard_metadata" |})] nil nil
    (BlockEmpty NoInfo).

Definition MyDeparser := DeclControl NoInfo
    {| stags := NoInfo; str := "MyDeparser" |} nil
    [(MkParameter false Directionless
          (TypTypeName (BareName {| stags := NoInfo; str := "packet_out" |}))
          None {| stags := NoInfo; str := "packet" |});
     (MkParameter false In
          (TypTypeName (BareName {| stags := NoInfo; str := "headers" |}))
          None {| stags := NoInfo; str := "hdr" |})] nil nil
    (BlockCons
         (MkStatement NoInfo
              (StatMethodCall
                   (MkExpression NoInfo
                        (ExpExpressionMember
                             (MkExpression NoInfo
                                  (ExpName
                                   (BareName
                                    {| stags := NoInfo; str := "packet" |}))
                                  (TypTypeName
                                   (BareName
                                    {| stags := NoInfo;
                                       str := "packet_out" |}))
                                  Directionless)
                             {| stags := NoInfo; str := "emit" |})
                        (TypFunction
                         (MkFunctionType [{| stags := NoInfo; str := "T2" |}]
                              [(MkParameter false In
                                    (TypTypeName
                                     (BareName
                                      {| stags := NoInfo; str := "T2" |}))
                                    None {| stags := NoInfo; str := "hdr" |})]
                              FunExtern TypVoid)) Directionless)
                   [(TypHeader
                     [(MkFieldType {| stags := NoInfo; str := "src" |}
                           (TypBit 8));
                      (MkFieldType {| stags := NoInfo; str := "dst" |}
                           (TypBit 8));
                      (MkFieldType {| stags := NoInfo; str := "proto" |}
                           (TypBit 4));
                      (MkFieldType
                           {| stags := NoInfo; str := "t_or_u_sport" |}
                           (TypBit 8));
                      (MkFieldType
                           {| stags := NoInfo; str := "t_or_u_dport" |}
                           (TypBit 8));
                      (MkFieldType
                           {| stags := NoInfo; str := "t_or_u_flags" |}
                           (TypBit 4))])]
                   [(Some
                     (MkExpression NoInfo
                          (ExpExpressionMember
                               (MkExpression NoInfo
                                    (ExpName
                                     (BareName
                                      {| stags := NoInfo; str := "hdr" |}))
                                    (TypTypeName
                                     (BareName
                                      {| stags := NoInfo; str := "headers" |}))
                                    In) {| stags := NoInfo; str := "comb" |})
                          (TypHeader
                           [(MkFieldType {| stags := NoInfo; str := "src" |}
                                 (TypBit 8));
                            (MkFieldType {| stags := NoInfo; str := "dst" |}
                                 (TypBit 8));
                            (MkFieldType
                                 {| stags := NoInfo; str := "proto" |}
                                 (TypBit 4));
                            (MkFieldType
                                 {| stags := NoInfo; str := "t_or_u_sport" |}
                                 (TypBit 8));
                            (MkFieldType
                                 {| stags := NoInfo; str := "t_or_u_dport" |}
                                 (TypBit 8));
                            (MkFieldType
                                 {| stags := NoInfo; str := "t_or_u_flags" |}
                                 (TypBit 4))]) Directionless))]) StmUnit)
         (BlockCons
              (MkStatement NoInfo
                   (StatMethodCall
                        (MkExpression NoInfo
                             (ExpExpressionMember
                                  (MkExpression NoInfo
                                       (ExpName
                                        (BareName
                                         {| stags := NoInfo;
                                            str := "packet" |}))
                                       (TypTypeName
                                        (BareName
                                         {| stags := NoInfo;
                                            str := "packet_out" |}))
                                       Directionless)
                                  {| stags := NoInfo; str := "emit" |})
                             (TypFunction
                              (MkFunctionType
                                   [{| stags := NoInfo; str := "T2" |}]
                                   [(MkParameter false In
                                         (TypTypeName
                                          (BareName
                                           {| stags := NoInfo; str := "T2" |}))
                                         None
                                         {| stags := NoInfo; str := "hdr" |})]
                                   FunExtern TypVoid)) Directionless)
                        [(TypHeader
                          [(MkFieldType {| stags := NoInfo; str := "seq" |}
                                (TypBit 8))])]
                        [(Some
                          (MkExpression NoInfo
                               (ExpExpressionMember
                                    (MkExpression NoInfo
                                         (ExpName
                                          (BareName
                                           {| stags := NoInfo;
                                              str := "hdr" |}))
                                         (TypTypeName
                                          (BareName
                                           {| stags := NoInfo;
                                              str := "headers" |})) In)
                                    {| stags := NoInfo; str := "opt_suff" |})
                               (TypHeader
                                [(MkFieldType
                                      {| stags := NoInfo; str := "seq" |}
                                      (TypBit 8))]) Directionless))])
                   StmUnit) (BlockEmpty NoInfo))).

Definition main := DeclInstantiation NoInfo
    (TypSpecializedType
         (TypTypeName (BareName {| stags := NoInfo; str := "V1Switch" |}))
         nil)
    [(MkExpression NoInfo
          (ExpNamelessInstantiation
               (TypSpecializedType
                    (TypTypeName
                     (BareName {| stags := NoInfo; str := "MyParser" |}))
                    nil) nil)
          (TypParser
           (MkControlType nil
                [(MkParameter false Directionless
                      (TypExtern {| stags := NoInfo; str := "packet_in" |})
                      None {| stags := NoInfo; str := "packet" |});
                 (MkParameter false Out
                      (TypStruct
                       [(MkFieldType {| stags := NoInfo; str := "comb" |}
                             (TypHeader
                              [(MkFieldType
                                    {| stags := NoInfo; str := "src" |}
                                    (TypBit 8));
                               (MkFieldType
                                    {| stags := NoInfo; str := "dst" |}
                                    (TypBit 8));
                               (MkFieldType
                                    {| stags := NoInfo; str := "proto" |}
                                    (TypBit 4));
                               (MkFieldType
                                    {| stags := NoInfo;
                                       str := "t_or_u_sport" |} (TypBit 8));
                               (MkFieldType
                                    {| stags := NoInfo;
                                       str := "t_or_u_dport" |} (TypBit 8));
                               (MkFieldType
                                    {| stags := NoInfo;
                                       str := "t_or_u_flags" |} (TypBit 4))]));
                        (MkFieldType {| stags := NoInfo; str := "opt_suff" |}
                             (TypHeader
                              [(MkFieldType
                                    {| stags := NoInfo; str := "seq" |}
                                    (TypBit 8))]))]) None
                      {| stags := NoInfo; str := "hdr" |});
                 (MkParameter false InOut (TypStruct nil) None
                      {| stags := NoInfo; str := "meta" |});
                 (MkParameter false InOut
                      (TypStruct
                       [(MkFieldType
                             {| stags := NoInfo; str := "ingress_port" |}
                             (TypBit 9));
                        (MkFieldType
                             {| stags := NoInfo; str := "egress_spec" |}
                             (TypBit 9));
                        (MkFieldType
                             {| stags := NoInfo; str := "egress_port" |}
                             (TypBit 9));
                        (MkFieldType
                             {| stags := NoInfo; str := "instance_type" |}
                             (TypBit 32));
                        (MkFieldType
                             {| stags := NoInfo; str := "packet_length" |}
                             (TypBit 32));
                        (MkFieldType
                             {| stags := NoInfo; str := "enq_timestamp" |}
                             (TypBit 32));
                        (MkFieldType
                             {| stags := NoInfo; str := "enq_qdepth" |}
                             (TypBit 19));
                        (MkFieldType
                             {| stags := NoInfo; str := "deq_timedelta" |}
                             (TypBit 32));
                        (MkFieldType
                             {| stags := NoInfo; str := "deq_qdepth" |}
                             (TypBit 19));
                        (MkFieldType
                             {| stags := NoInfo;
                                str := "ingress_global_timestamp" |}
                             (TypBit 48));
                        (MkFieldType
                             {| stags := NoInfo;
                                str := "egress_global_timestamp" |}
                             (TypBit 48));
                        (MkFieldType
                             {| stags := NoInfo; str := "mcast_grp" |}
                             (TypBit 16));
                        (MkFieldType
                             {| stags := NoInfo; str := "egress_rid" |}
                             (TypBit 16));
                        (MkFieldType
                             {| stags := NoInfo; str := "checksum_error" |}
                             (TypBit 1));
                        (MkFieldType
                             {| stags := NoInfo; str := "parser_error" |}
                             TypError);
                        (MkFieldType {| stags := NoInfo; str := "priority" |}
                             (TypBit 3))]) None
                      {| stags := NoInfo; str := "standard_metadata" |})]))
          Directionless);
     (MkExpression NoInfo
          (ExpNamelessInstantiation
               (TypSpecializedType
                    (TypTypeName
                     (BareName {| stags := NoInfo; str := "MyChecksum" |}))
                    nil) nil)
          (TypControl
           (MkControlType nil
                [(MkParameter false InOut
                      (TypStruct
                       [(MkFieldType {| stags := NoInfo; str := "comb" |}
                             (TypHeader
                              [(MkFieldType
                                    {| stags := NoInfo; str := "src" |}
                                    (TypBit 8));
                               (MkFieldType
                                    {| stags := NoInfo; str := "dst" |}
                                    (TypBit 8));
                               (MkFieldType
                                    {| stags := NoInfo; str := "proto" |}
                                    (TypBit 4));
                               (MkFieldType
                                    {| stags := NoInfo;
                                       str := "t_or_u_sport" |} (TypBit 8));
                               (MkFieldType
                                    {| stags := NoInfo;
                                       str := "t_or_u_dport" |} (TypBit 8));
                               (MkFieldType
                                    {| stags := NoInfo;
                                       str := "t_or_u_flags" |} (TypBit 4))]));
                        (MkFieldType {| stags := NoInfo; str := "opt_suff" |}
                             (TypHeader
                              [(MkFieldType
                                    {| stags := NoInfo; str := "seq" |}
                                    (TypBit 8))]))]) None
                      {| stags := NoInfo; str := "hdr" |});
                 (MkParameter false InOut (TypStruct nil) None
                      {| stags := NoInfo; str := "meta" |})])) Directionless);
     (MkExpression NoInfo
          (ExpNamelessInstantiation
               (TypSpecializedType
                    (TypTypeName
                     (BareName {| stags := NoInfo; str := "MyIngress" |}))
                    nil) nil)
          (TypControl
           (MkControlType nil
                [(MkParameter false InOut
                      (TypStruct
                       [(MkFieldType {| stags := NoInfo; str := "comb" |}
                             (TypHeader
                              [(MkFieldType
                                    {| stags := NoInfo; str := "src" |}
                                    (TypBit 8));
                               (MkFieldType
                                    {| stags := NoInfo; str := "dst" |}
                                    (TypBit 8));
                               (MkFieldType
                                    {| stags := NoInfo; str := "proto" |}
                                    (TypBit 4));
                               (MkFieldType
                                    {| stags := NoInfo;
                                       str := "t_or_u_sport" |} (TypBit 8));
                               (MkFieldType
                                    {| stags := NoInfo;
                                       str := "t_or_u_dport" |} (TypBit 8));
                               (MkFieldType
                                    {| stags := NoInfo;
                                       str := "t_or_u_flags" |} (TypBit 4))]));
                        (MkFieldType {| stags := NoInfo; str := "opt_suff" |}
                             (TypHeader
                              [(MkFieldType
                                    {| stags := NoInfo; str := "seq" |}
                                    (TypBit 8))]))]) None
                      {| stags := NoInfo; str := "hdr" |});
                 (MkParameter false InOut (TypStruct nil) None
                      {| stags := NoInfo; str := "meta" |});
                 (MkParameter false InOut
                      (TypStruct
                       [(MkFieldType
                             {| stags := NoInfo; str := "ingress_port" |}
                             (TypBit 9));
                        (MkFieldType
                             {| stags := NoInfo; str := "egress_spec" |}
                             (TypBit 9));
                        (MkFieldType
                             {| stags := NoInfo; str := "egress_port" |}
                             (TypBit 9));
                        (MkFieldType
                             {| stags := NoInfo; str := "instance_type" |}
                             (TypBit 32));
                        (MkFieldType
                             {| stags := NoInfo; str := "packet_length" |}
                             (TypBit 32));
                        (MkFieldType
                             {| stags := NoInfo; str := "enq_timestamp" |}
                             (TypBit 32));
                        (MkFieldType
                             {| stags := NoInfo; str := "enq_qdepth" |}
                             (TypBit 19));
                        (MkFieldType
                             {| stags := NoInfo; str := "deq_timedelta" |}
                             (TypBit 32));
                        (MkFieldType
                             {| stags := NoInfo; str := "deq_qdepth" |}
                             (TypBit 19));
                        (MkFieldType
                             {| stags := NoInfo;
                                str := "ingress_global_timestamp" |}
                             (TypBit 48));
                        (MkFieldType
                             {| stags := NoInfo;
                                str := "egress_global_timestamp" |}
                             (TypBit 48));
                        (MkFieldType
                             {| stags := NoInfo; str := "mcast_grp" |}
                             (TypBit 16));
                        (MkFieldType
                             {| stags := NoInfo; str := "egress_rid" |}
                             (TypBit 16));
                        (MkFieldType
                             {| stags := NoInfo; str := "checksum_error" |}
                             (TypBit 1));
                        (MkFieldType
                             {| stags := NoInfo; str := "parser_error" |}
                             TypError);
                        (MkFieldType {| stags := NoInfo; str := "priority" |}
                             (TypBit 3))]) None
                      {| stags := NoInfo; str := "standard_metadata" |})]))
          Directionless);
     (MkExpression NoInfo
          (ExpNamelessInstantiation
               (TypSpecializedType
                    (TypTypeName
                     (BareName {| stags := NoInfo; str := "MyEgress" |}))
                    nil) nil)
          (TypControl
           (MkControlType nil
                [(MkParameter false InOut
                      (TypStruct
                       [(MkFieldType {| stags := NoInfo; str := "comb" |}
                             (TypHeader
                              [(MkFieldType
                                    {| stags := NoInfo; str := "src" |}
                                    (TypBit 8));
                               (MkFieldType
                                    {| stags := NoInfo; str := "dst" |}
                                    (TypBit 8));
                               (MkFieldType
                                    {| stags := NoInfo; str := "proto" |}
                                    (TypBit 4));
                               (MkFieldType
                                    {| stags := NoInfo;
                                       str := "t_or_u_sport" |} (TypBit 8));
                               (MkFieldType
                                    {| stags := NoInfo;
                                       str := "t_or_u_dport" |} (TypBit 8));
                               (MkFieldType
                                    {| stags := NoInfo;
                                       str := "t_or_u_flags" |} (TypBit 4))]));
                        (MkFieldType {| stags := NoInfo; str := "opt_suff" |}
                             (TypHeader
                              [(MkFieldType
                                    {| stags := NoInfo; str := "seq" |}
                                    (TypBit 8))]))]) None
                      {| stags := NoInfo; str := "hdr" |});
                 (MkParameter false InOut (TypStruct nil) None
                      {| stags := NoInfo; str := "meta" |});
                 (MkParameter false InOut
                      (TypStruct
                       [(MkFieldType
                             {| stags := NoInfo; str := "ingress_port" |}
                             (TypBit 9));
                        (MkFieldType
                             {| stags := NoInfo; str := "egress_spec" |}
                             (TypBit 9));
                        (MkFieldType
                             {| stags := NoInfo; str := "egress_port" |}
                             (TypBit 9));
                        (MkFieldType
                             {| stags := NoInfo; str := "instance_type" |}
                             (TypBit 32));
                        (MkFieldType
                             {| stags := NoInfo; str := "packet_length" |}
                             (TypBit 32));
                        (MkFieldType
                             {| stags := NoInfo; str := "enq_timestamp" |}
                             (TypBit 32));
                        (MkFieldType
                             {| stags := NoInfo; str := "enq_qdepth" |}
                             (TypBit 19));
                        (MkFieldType
                             {| stags := NoInfo; str := "deq_timedelta" |}
                             (TypBit 32));
                        (MkFieldType
                             {| stags := NoInfo; str := "deq_qdepth" |}
                             (TypBit 19));
                        (MkFieldType
                             {| stags := NoInfo;
                                str := "ingress_global_timestamp" |}
                             (TypBit 48));
                        (MkFieldType
                             {| stags := NoInfo;
                                str := "egress_global_timestamp" |}
                             (TypBit 48));
                        (MkFieldType
                             {| stags := NoInfo; str := "mcast_grp" |}
                             (TypBit 16));
                        (MkFieldType
                             {| stags := NoInfo; str := "egress_rid" |}
                             (TypBit 16));
                        (MkFieldType
                             {| stags := NoInfo; str := "checksum_error" |}
                             (TypBit 1));
                        (MkFieldType
                             {| stags := NoInfo; str := "parser_error" |}
                             TypError);
                        (MkFieldType {| stags := NoInfo; str := "priority" |}
                             (TypBit 3))]) None
                      {| stags := NoInfo; str := "standard_metadata" |})]))
          Directionless);
     (MkExpression NoInfo
          (ExpNamelessInstantiation
               (TypSpecializedType
                    (TypTypeName
                     (BareName {| stags := NoInfo; str := "MyChecksum" |}))
                    nil) nil)
          (TypControl
           (MkControlType nil
                [(MkParameter false InOut
                      (TypStruct
                       [(MkFieldType {| stags := NoInfo; str := "comb" |}
                             (TypHeader
                              [(MkFieldType
                                    {| stags := NoInfo; str := "src" |}
                                    (TypBit 8));
                               (MkFieldType
                                    {| stags := NoInfo; str := "dst" |}
                                    (TypBit 8));
                               (MkFieldType
                                    {| stags := NoInfo; str := "proto" |}
                                    (TypBit 4));
                               (MkFieldType
                                    {| stags := NoInfo;
                                       str := "t_or_u_sport" |} (TypBit 8));
                               (MkFieldType
                                    {| stags := NoInfo;
                                       str := "t_or_u_dport" |} (TypBit 8));
                               (MkFieldType
                                    {| stags := NoInfo;
                                       str := "t_or_u_flags" |} (TypBit 4))]));
                        (MkFieldType {| stags := NoInfo; str := "opt_suff" |}
                             (TypHeader
                              [(MkFieldType
                                    {| stags := NoInfo; str := "seq" |}
                                    (TypBit 8))]))]) None
                      {| stags := NoInfo; str := "hdr" |});
                 (MkParameter false InOut (TypStruct nil) None
                      {| stags := NoInfo; str := "meta" |})])) Directionless);
     (MkExpression NoInfo
          (ExpNamelessInstantiation
               (TypSpecializedType
                    (TypTypeName
                     (BareName {| stags := NoInfo; str := "MyDeparser" |}))
                    nil) nil)
          (TypControl
           (MkControlType nil
                [(MkParameter false Directionless
                      (TypExtern {| stags := NoInfo; str := "packet_out" |})
                      None {| stags := NoInfo; str := "packet" |});
                 (MkParameter false In
                      (TypStruct
                       [(MkFieldType {| stags := NoInfo; str := "comb" |}
                             (TypHeader
                              [(MkFieldType
                                    {| stags := NoInfo; str := "src" |}
                                    (TypBit 8));
                               (MkFieldType
                                    {| stags := NoInfo; str := "dst" |}
                                    (TypBit 8));
                               (MkFieldType
                                    {| stags := NoInfo; str := "proto" |}
                                    (TypBit 4));
                               (MkFieldType
                                    {| stags := NoInfo;
                                       str := "t_or_u_sport" |} (TypBit 8));
                               (MkFieldType
                                    {| stags := NoInfo;
                                       str := "t_or_u_dport" |} (TypBit 8));
                               (MkFieldType
                                    {| stags := NoInfo;
                                       str := "t_or_u_flags" |} (TypBit 4))]));
                        (MkFieldType {| stags := NoInfo; str := "opt_suff" |}
                             (TypHeader
                              [(MkFieldType
                                    {| stags := NoInfo; str := "seq" |}
                                    (TypBit 8))]))]) None
                      {| stags := NoInfo; str := "hdr" |})])) Directionless)]
    {| stags := NoInfo; str := "main" |} None.

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
     ComputeChecksum; Deparser; V1Switch; silly_combined_hdr; tcp_seq_suffix;
     metadata; headers; MyParser; MyChecksum; MyIngress; MyEgress;
     MyDeparser; main].


