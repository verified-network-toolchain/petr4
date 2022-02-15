Require Import Poulet4.P4light.Syntax.P4defs.
Open Scope string_scope.

Import ListNotations.

(* TODO: commented out until refactor is complete.

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
     (ProtoMethod NoInfo
          (TypTypeName {| stags := NoInfo; str := "T1" |})
          {| stags := NoInfo; str := "lookahead" |}
          [{| stags := NoInfo; str := "T1" |}] nil);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "extract" |}
          [{| stags := NoInfo; str := "T0" |}]
          [(MkParameter false Out
                (TypTypeName {| stags := NoInfo; str := "T0" |})
                None {| stags := NoInfo; str := "variableSizeHeader" |});
           (MkParameter false In (TypBit 32%N) None
                {| stags := NoInfo; str := "variableFieldSizeInBits" |})]);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "extract" |}
          [{| stags := NoInfo; str := "T" |}]
          [(MkParameter false Out
                (TypTypeName {| stags := NoInfo; str := "T" |})
                None {| stags := NoInfo; str := "hdr" |})])].

Definition packet_out := DeclExternObject NoInfo
    {| stags := NoInfo; str := "packet_out" |} nil
    [(ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "emit" |}
          [{| stags := NoInfo; str := "T2" |}]
          [(MkParameter false In
                (TypTypeName {| stags := NoInfo; str := "T2" |})
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
                (TypTypeName
                 {| stags := NoInfo; str := "CounterType" |})
                None {| stags := NoInfo; str := "type" |})]);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "count" |} nil
          [(MkParameter false In (TypBit 32%N) None
                {| stags := NoInfo; str := "index" |})])].

Definition direct_counter := DeclExternObject NoInfo
    {| stags := NoInfo; str := "direct_counter" |} nil
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "direct_counter" |}
          [(MkParameter false Directionless
                (TypTypeName
                 {| stags := NoInfo; str := "CounterType" |})
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
                (TypTypeName {| stags := NoInfo; str := "T3" |})
                None {| stags := NoInfo; str := "result" |})])].

Definition direct_meter := DeclExternObject NoInfo
    {| stags := NoInfo; str := "direct_meter" |}
    [{| stags := NoInfo; str := "T4" |}]
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "direct_meter" |}
          [(MkParameter false Directionless
                (TypTypeName {| stags := NoInfo; str := "MeterType" |})
                None {| stags := NoInfo; str := "type" |})]);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "read" |} nil
          [(MkParameter false Out
                (TypTypeName {| stags := NoInfo; str := "T4" |})
                None {| stags := NoInfo; str := "result" |})])].

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
                (TypTypeName {| stags := NoInfo; str := "T5" |})
                None {| stags := NoInfo; str := "value" |})]);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "read" |} nil
          [(MkParameter false Out
                (TypTypeName {| stags := NoInfo; str := "T5" |})
                None {| stags := NoInfo; str := "result" |});
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
    [(MkParameter false Out
          (TypTypeName {| stags := NoInfo; str := "T6" |})
          None {| stags := NoInfo; str := "result" |});
     (MkParameter false In
          (TypTypeName {| stags := NoInfo; str := "T6" |})
          None {| stags := NoInfo; str := "lo" |});
     (MkParameter false In
          (TypTypeName {| stags := NoInfo; str := "T6" |})
          None {| stags := NoInfo; str := "hi" |})].

Definition digest'receiver'data := DeclExternFunction NoInfo TypVoid
    {| stags := NoInfo; str := "digest" |}
    [{| stags := NoInfo; str := "T7" |}]
    [(MkParameter false In (TypBit 32%N) None
          {| stags := NoInfo; str := "receiver" |});
     (MkParameter false In
          (TypTypeName {| stags := NoInfo; str := "T7" |})
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
           {| stags := NoInfo; str := "standard_metadata_t" |})
          None {| stags := NoInfo; str := "standard_metadata" |})].

Definition hash'result'algo'base'data'max := DeclExternFunction NoInfo
    TypVoid {| stags := NoInfo; str := "hash" |}
    [{| stags := NoInfo; str := "O" |}; {| stags := NoInfo; str := "T8" |};
     {| stags := NoInfo; str := "D" |}; {| stags := NoInfo; str := "M" |}]
    [(MkParameter false Out
          (TypTypeName ( {| stags := NoInfo; str := "O" |})) 
          None {| stags := NoInfo; str := "result" |});
     (MkParameter false In
          (TypTypeName {| stags := NoInfo; str := "HashAlgorithm" |})
          None {| stags := NoInfo; str := "algo" |});
     (MkParameter false In
          (TypTypeName ( {| stags := NoInfo; str := "T8" |})) 
          None {| stags := NoInfo; str := "base" |});
     (MkParameter false In
          (TypTypeName ( {| stags := NoInfo; str := "D" |})) 
          None {| stags := NoInfo; str := "data" |});
     (MkParameter false In
          (TypTypeName ( {| stags := NoInfo; str := "M" |})) 
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
                (TypTypeName ( {| stags := NoInfo; str := "D9" |}))
                None {| stags := NoInfo; str := "data" |})])].

Definition verify_checksum'condition'data'checksum'algo := DeclExternFunction
    NoInfo TypVoid {| stags := NoInfo; str := "verify_checksum" |}
    [{| stags := NoInfo; str := "T10" |};
     {| stags := NoInfo; str := "O11" |}]
    [(MkParameter false In TypBool None
          {| stags := NoInfo; str := "condition" |});
     (MkParameter false In
          (TypTypeName ( {| stags := NoInfo; str := "T10" |})) 
          None {| stags := NoInfo; str := "data" |});
     (MkParameter false In
          (TypTypeName ( {| stags := NoInfo; str := "O11" |})) 
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
     (MkParameter false In
          (TypTypeName ( {| stags := NoInfo; str := "T12" |})) 
          None {| stags := NoInfo; str := "data" |});
     (MkParameter false InOut
          (TypTypeName ( {| stags := NoInfo; str := "O13" |})) 
          None {| stags := NoInfo; str := "checksum" |});
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
     (MkParameter false In
          (TypTypeName ( {| stags := NoInfo; str := "T14" |})) 
          None {| stags := NoInfo; str := "data" |});
     (MkParameter false In
          (TypTypeName ( {| stags := NoInfo; str := "O15" |})) 
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
     (MkParameter false In
          (TypTypeName ( {| stags := NoInfo; str := "T16" |})) 
          None {| stags := NoInfo; str := "data" |});
     (MkParameter false InOut
          (TypTypeName ( {| stags := NoInfo; str := "O17" |})) 
          None {| stags := NoInfo; str := "checksum" |});
     (MkParameter false Directionless
          (TypTypeName {| stags := NoInfo; str := "HashAlgorithm" |})
          None {| stags := NoInfo; str := "algo" |})].

Definition resubmit'data := DeclExternFunction NoInfo TypVoid
    {| stags := NoInfo; str := "resubmit" |}
    [{| stags := NoInfo; str := "T18" |}]
    [(MkParameter false In
          (TypTypeName ( {| stags := NoInfo; str := "T18" |})) 
          None {| stags := NoInfo; str := "data" |})].

Definition recirculate'data := DeclExternFunction NoInfo TypVoid
    {| stags := NoInfo; str := "recirculate" |}
    [{| stags := NoInfo; str := "T19" |}]
    [(MkParameter false In
          (TypTypeName ( {| stags := NoInfo; str := "T19" |})) 
          None {| stags := NoInfo; str := "data" |})].

Definition clone'type'session := DeclExternFunction NoInfo TypVoid
    {| stags := NoInfo; str := "clone" |} nil
    [(MkParameter false In
          (TypTypeName ( {| stags := NoInfo; str := "CloneType" |}))
          None {| stags := NoInfo; str := "type" |});
     (MkParameter false In (TypBit 32%N) None
          {| stags := NoInfo; str := "session" |})].

Definition clone3'type'session'data := DeclExternFunction NoInfo TypVoid
    {| stags := NoInfo; str := "clone3" |}
    [{| stags := NoInfo; str := "T20" |}]
    [(MkParameter false In
          (TypTypeName ( {| stags := NoInfo; str := "CloneType" |}))
          None {| stags := NoInfo; str := "type" |});
     (MkParameter false In (TypBit 32%N) None
          {| stags := NoInfo; str := "session" |});
     (MkParameter false In
          (TypTypeName ( {| stags := NoInfo; str := "T20" |})) 
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
     (MkParameter false In
          (TypTypeName ( {| stags := NoInfo; str := "T21" |})) 
          None {| stags := NoInfo; str := "data" |})].

Definition Parser := DeclParserType NoInfo
    {| stags := NoInfo; str := "Parser" |}
    [{| stags := NoInfo; str := "H" |}; {| stags := NoInfo; str := "M22" |}]
    [(MkParameter false Directionless
          (TypTypeName ( {| stags := NoInfo; str := "packet_in" |}))
          None {| stags := NoInfo; str := "b" |});
     (MkParameter false Out
          (TypTypeName ( {| stags := NoInfo; str := "H" |})) 
          None {| stags := NoInfo; str := "parsedHdr" |});
     (MkParameter false InOut
          (TypTypeName ( {| stags := NoInfo; str := "M22" |})) 
          None {| stags := NoInfo; str := "meta" |});
     (MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "standard_metadata_t" |})
          None {| stags := NoInfo; str := "standard_metadata" |})].

Definition VerifyChecksum := DeclControlType NoInfo
    {| stags := NoInfo; str := "VerifyChecksum" |}
    [{| stags := NoInfo; str := "H23" |};
     {| stags := NoInfo; str := "M24" |}]
    [(MkParameter false InOut
          (TypTypeName ( {| stags := NoInfo; str := "H23" |})) 
          None {| stags := NoInfo; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName ( {| stags := NoInfo; str := "M24" |})) 
          None {| stags := NoInfo; str := "meta" |})].

Definition Ingress := DeclControlType NoInfo
    {| stags := NoInfo; str := "Ingress" |}
    [{| stags := NoInfo; str := "H25" |};
     {| stags := NoInfo; str := "M26" |}]
    [(MkParameter false InOut
          (TypTypeName ( {| stags := NoInfo; str := "H25" |})) 
          None {| stags := NoInfo; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName ( {| stags := NoInfo; str := "M26" |})) 
          None {| stags := NoInfo; str := "meta" |});
     (MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "standard_metadata_t" |})
          None {| stags := NoInfo; str := "standard_metadata" |})].

Definition Egress := DeclControlType NoInfo
    {| stags := NoInfo; str := "Egress" |}
    [{| stags := NoInfo; str := "H27" |};
     {| stags := NoInfo; str := "M28" |}]
    [(MkParameter false InOut
          (TypTypeName ( {| stags := NoInfo; str := "H27" |})) 
          None {| stags := NoInfo; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName ( {| stags := NoInfo; str := "M28" |})) 
          None {| stags := NoInfo; str := "meta" |});
     (MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "standard_metadata_t" |})
          None {| stags := NoInfo; str := "standard_metadata" |})].

Definition ComputeChecksum := DeclControlType NoInfo
    {| stags := NoInfo; str := "ComputeChecksum" |}
    [{| stags := NoInfo; str := "H29" |};
     {| stags := NoInfo; str := "M30" |}]
    [(MkParameter false InOut
          (TypTypeName ( {| stags := NoInfo; str := "H29" |})) 
          None {| stags := NoInfo; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName ( {| stags := NoInfo; str := "M30" |})) 
          None {| stags := NoInfo; str := "meta" |})].

Definition Deparser := DeclControlType NoInfo
    {| stags := NoInfo; str := "Deparser" |}
    [{| stags := NoInfo; str := "H31" |}]
    [(MkParameter false Directionless
          (TypTypeName ( {| stags := NoInfo; str := "packet_out" |}))
          None {| stags := NoInfo; str := "b" |});
     (MkParameter false In
          (TypTypeName ( {| stags := NoInfo; str := "H31" |})) 
          None {| stags := NoInfo; str := "hdr" |})].

Definition V1Switch := DeclPackageType NoInfo
    {| stags := NoInfo; str := "V1Switch" |}
    [{| stags := NoInfo; str := "H32" |};
     {| stags := NoInfo; str := "M33" |}]
    [(MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "Parser" |})
               [(TypTypeName ( {| stags := NoInfo; str := "H32" |}));
                (TypTypeName ( {| stags := NoInfo; str := "M33" |}))])
          None {| stags := NoInfo; str := "p" |});
     (MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "VerifyChecksum" |})
               [(TypTypeName ( {| stags := NoInfo; str := "H32" |}));
                (TypTypeName ( {| stags := NoInfo; str := "M33" |}))])
          None {| stags := NoInfo; str := "vr" |});
     (MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "Ingress" |})
               [(TypTypeName ( {| stags := NoInfo; str := "H32" |}));
                (TypTypeName ( {| stags := NoInfo; str := "M33" |}))])
          None {| stags := NoInfo; str := "ig" |});
     (MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "Egress" |})
               [(TypTypeName ( {| stags := NoInfo; str := "H32" |}));
                (TypTypeName ( {| stags := NoInfo; str := "M33" |}))])
          None {| stags := NoInfo; str := "eg" |});
     (MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "ComputeChecksum" |})
               [(TypTypeName ( {| stags := NoInfo; str := "H32" |}));
                (TypTypeName ( {| stags := NoInfo; str := "M33" |}))])
          None {| stags := NoInfo; str := "ck" |});
     (MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "Deparser" |})
               [(TypTypeName ( {| stags := NoInfo; str := "H32" |}))])
          None {| stags := NoInfo; str := "dep" |})].

Definition intrinsic_metadata_t := DeclStruct NoInfo
    {| stags := NoInfo; str := "intrinsic_metadata_t" |}
    [(MkDeclarationField NoInfo (TypBit 4%N)
          {| stags := NoInfo; str := "mcast_grp" |});
     (MkDeclarationField NoInfo (TypBit 4%N)
          {| stags := NoInfo; str := "egress_rid" |})].

Definition meta_t := DeclStruct NoInfo {| stags := NoInfo; str := "meta_t" |}
    [(MkDeclarationField NoInfo (TypBit 1%N)
          {| stags := NoInfo; str := "do_forward" |});
     (MkDeclarationField NoInfo (TypBit 32%N)
          {| stags := NoInfo; str := "ipv4_sa" |});
     (MkDeclarationField NoInfo (TypBit 32%N)
          {| stags := NoInfo; str := "ipv4_da" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "tcp_sp" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "tcp_dp" |});
     (MkDeclarationField NoInfo (TypBit 32%N)
          {| stags := NoInfo; str := "nhop_ipv4" |});
     (MkDeclarationField NoInfo (TypBit 32%N)
          {| stags := NoInfo; str := "if_ipv4_addr" |});
     (MkDeclarationField NoInfo (TypBit 48%N)
          {| stags := NoInfo; str := "if_mac_addr" |});
     (MkDeclarationField NoInfo (TypBit 1%N)
          {| stags := NoInfo; str := "is_ext_if" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "tcpLength" |});
     (MkDeclarationField NoInfo (TypBit 8%N)
          {| stags := NoInfo; str := "if_index" |});
     (MkDeclarationField NoInfo (TypBit 9%N)
          {| stags := NoInfo; str := "init_egress_spec" |})].

Definition cpu_header_t := DeclHeader NoInfo
    {| stags := NoInfo; str := "cpu_header_t" |}
    [(MkDeclarationField NoInfo (TypBit 64%N)
          {| stags := NoInfo; str := "preamble" |});
     (MkDeclarationField NoInfo (TypBit 8%N)
          {| stags := NoInfo; str := "device" |});
     (MkDeclarationField NoInfo (TypBit 8%N)
          {| stags := NoInfo; str := "reason" |});
     (MkDeclarationField NoInfo (TypBit 8%N)
          {| stags := NoInfo; str := "if_index" |})].

Definition ethernet_t := DeclHeader NoInfo
    {| stags := NoInfo; str := "ethernet_t" |}
    [(MkDeclarationField NoInfo (TypBit 48%N)
          {| stags := NoInfo; str := "dstAddr" |});
     (MkDeclarationField NoInfo (TypBit 48%N)
          {| stags := NoInfo; str := "srcAddr" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "etherType" |})].

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

Definition tcp_t := DeclHeader NoInfo {| stags := NoInfo; str := "tcp_t" |}
    [(MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "srcPort" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "dstPort" |});
     (MkDeclarationField NoInfo (TypBit 32%N)
          {| stags := NoInfo; str := "seqNo" |});
     (MkDeclarationField NoInfo (TypBit 32%N)
          {| stags := NoInfo; str := "ackNo" |});
     (MkDeclarationField NoInfo (TypBit 4%N)
          {| stags := NoInfo; str := "dataOffset" |});
     (MkDeclarationField NoInfo (TypBit 4%N)
          {| stags := NoInfo; str := "res" |});
     (MkDeclarationField NoInfo (TypBit 8%N)
          {| stags := NoInfo; str := "flags" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "window" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "checksum" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "urgentPtr" |})].

Definition metadata := DeclStruct NoInfo
    {| stags := NoInfo; str := "metadata" |}
    [(MkDeclarationField NoInfo
          (TypStruct
           [( {| stags := NoInfo; str := "do_forward" |}, (TypBit 1%N) );
            ( {| stags := NoInfo; str := "ipv4_sa" |}, (TypBit 32%N) );
            ( {| stags := NoInfo; str := "ipv4_da" |}, (TypBit 32%N) );
            ( {| stags := NoInfo; str := "tcp_sp" |}, (TypBit 16%N) );
            ( {| stags := NoInfo; str := "tcp_dp" |}, (TypBit 16%N) );
            ( {| stags := NoInfo; str := "nhop_ipv4" |}, (TypBit 32%N) );
            ( {| stags := NoInfo; str := "if_ipv4_addr" |}, (TypBit 32%N) );
            ( {| stags := NoInfo; str := "if_mac_addr" |}, (TypBit 48%N) );
            ( {| stags := NoInfo; str := "is_ext_if" |}, (TypBit 1%N) );
            ( {| stags := NoInfo; str := "tcpLength" |}, (TypBit 16%N) );
            ( {| stags := NoInfo; str := "if_index" |}, (TypBit 8%N) );
            ( {| stags := NoInfo; str := "init_egress_spec" |},
              (TypBit 9%N) )]) {| stags := NoInfo; str := "meta" |})].

Definition headers := DeclStruct NoInfo
    {| stags := NoInfo; str := "headers" |}
    [(MkDeclarationField NoInfo
          (TypHeader
           [( {| stags := NoInfo; str := "preamble" |}, (TypBit 64%N) );
            ( {| stags := NoInfo; str := "device" |}, (TypBit 8%N) );
            ( {| stags := NoInfo; str := "reason" |}, (TypBit 8%N) );
            ( {| stags := NoInfo; str := "if_index" |}, (TypBit 8%N) )])
          {| stags := NoInfo; str := "cpu_header" |});
     (MkDeclarationField NoInfo
          (TypHeader
           [( {| stags := NoInfo; str := "dstAddr" |}, (TypBit 48%N) );
            ( {| stags := NoInfo; str := "srcAddr" |}, (TypBit 48%N) );
            ( {| stags := NoInfo; str := "etherType" |}, (TypBit 16%N) )])
          {| stags := NoInfo; str := "ethernet" |});
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
            ( {| stags := NoInfo; str := "seqNo" |}, (TypBit 32%N) );
            ( {| stags := NoInfo; str := "ackNo" |}, (TypBit 32%N) );
            ( {| stags := NoInfo; str := "dataOffset" |}, (TypBit 4%N) );
            ( {| stags := NoInfo; str := "res" |}, (TypBit 4%N) );
            ( {| stags := NoInfo; str := "flags" |}, (TypBit 8%N) );
            ( {| stags := NoInfo; str := "window" |}, (TypBit 16%N) );
            ( {| stags := NoInfo; str := "checksum" |}, (TypBit 16%N) );
            ( {| stags := NoInfo; str := "urgentPtr" |}, (TypBit 16%N) )])
          {| stags := NoInfo; str := "tcp" |})].

Definition ParserImpl := DeclParser NoInfo
    {| stags := NoInfo; str := "ParserImpl" |} nil
    [(MkParameter false Directionless
          (TypTypeName ( {| stags := NoInfo; str := "packet_in" |}))
          None {| stags := NoInfo; str := "packet" |});
     (MkParameter false Out
          (TypTypeName ( {| stags := NoInfo; str := "headers" |}))
          None {| stags := NoInfo; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName ( {| stags := NoInfo; str := "metadata" |}))
          None {| stags := NoInfo; str := "meta" |});
     (MkParameter false InOut
          (TypTypeName ( {| stags := NoInfo; str := "standard_metadata_t" |}))
          None {| stags := NoInfo; str := "standard_metadata" |})] nil nil
    [(MkParserState NoInfo {| stags := NoInfo; str := "parse_cpu_header" |}
          [(MkStatement NoInfo
                (StatAssignment
                     (MkExpression NoInfo
                          (ExpExpressionMember
                               (MkExpression NoInfo
                                    (ExpExpressionMember
                                         (MkExpression NoInfo
                                              (ExpName
                                               (BareName
                                                {| stags := NoInfo;
                                                   str := "meta" |})
                                               NoLocator)
                                              (TypTypeName (
                                                {| stags := NoInfo;
                                                   str := "metadata" |}))
                                              InOut)
                                         {| stags := NoInfo; str := "meta" |})
                                    (TypStruct
                                     [( {| stags := NoInfo;
                                           str := "do_forward" |},
                                        (TypBit 1%N) );
                                      ( {| stags := NoInfo;
                                           str := "ipv4_sa" |},
                                        (TypBit 32%N) );
                                      ( {| stags := NoInfo;
                                           str := "ipv4_da" |},
                                        (TypBit 32%N) );
                                      ( {| stags := NoInfo;
                                           str := "tcp_sp" |},
                                        (TypBit 16%N) );
                                      ( {| stags := NoInfo;
                                           str := "tcp_dp" |},
                                        (TypBit 16%N) );
                                      ( {| stags := NoInfo;
                                           str := "nhop_ipv4" |},
                                        (TypBit 32%N) );
                                      ( {| stags := NoInfo;
                                           str := "if_ipv4_addr" |},
                                        (TypBit 32%N) );
                                      ( {| stags := NoInfo;
                                           str := "if_mac_addr" |},
                                        (TypBit 48%N) );
                                      ( {| stags := NoInfo;
                                           str := "is_ext_if" |},
                                        (TypBit 1%N) );
                                      ( {| stags := NoInfo;
                                           str := "tcpLength" |},
                                        (TypBit 16%N) );
                                      ( {| stags := NoInfo;
                                           str := "if_index" |},
                                        (TypBit 8%N) );
                                      ( {| stags := NoInfo;
                                           str := "init_egress_spec" |},
                                        (TypBit 9%N) )]) Directionless)
                               {| stags := NoInfo; str := "if_index" |})
                          (TypBit 8%N) Directionless)
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
                                              (TypTypeName (
                                                {| stags := NoInfo;
                                                   str := "headers" |})) Out)
                                         {| stags := NoInfo;
                                            str := "cpu_header" |})
                                    (TypHeader
                                     [( {| stags := NoInfo;
                                           str := "preamble" |},
                                        (TypBit 64%N) );
                                      ( {| stags := NoInfo;
                                           str := "device" |}, (TypBit 8%N) );
                                      ( {| stags := NoInfo;
                                           str := "reason" |}, (TypBit 8%N) );
                                      ( {| stags := NoInfo;
                                           str := "if_index" |},
                                        (TypBit 8%N) )]) Directionless)
                               {| stags := NoInfo; str := "if_index" |})
                          (TypBit 8%N) Directionless)) StmUnit);
           (MkStatement NoInfo
                (StatMethodCall
                     (MkExpression NoInfo
                          (ExpExpressionMember
                               (MkExpression NoInfo
                                    (ExpName
                                     (BareName
                                      {| stags := NoInfo; str := "packet" |})
                                     NoLocator)
                                    (TypTypeName (
                                      {| stags := NoInfo;
                                         str := "packet_in" |}))
                                    Directionless)
                               {| stags := NoInfo; str := "extract" |})
                          (TypFunction
                           (MkFunctionType
                                [{| stags := NoInfo; str := "T" |}]
                                [(MkParameter false Out
                                      (TypTypeName (
                                        {| stags := NoInfo; str := "T" |}))
                                      None
                                      {| stags := NoInfo; str := "hdr" |})]
                                FunExtern TypVoid)) Directionless)
                     [(TypHeader
                       [( {| stags := NoInfo; str := "preamble" |},
                          (TypBit 64%N) );
                        ( {| stags := NoInfo; str := "device" |},
                          (TypBit 8%N) );
                        ( {| stags := NoInfo; str := "reason" |},
                          (TypBit 8%N) );
                        ( {| stags := NoInfo; str := "if_index" |},
                          (TypBit 8%N) )])]
                     [(Some
                       (MkExpression NoInfo
                            (ExpExpressionMember
                                 (MkExpression NoInfo
                                      (ExpName
                                       (BareName
                                        {| stags := NoInfo; str := "hdr" |})
                                       NoLocator)
                                      (TypTypeName (
                                        {| stags := NoInfo;
                                           str := "headers" |})) Out)
                                 {| stags := NoInfo; str := "cpu_header" |})
                            (TypHeader
                             [( {| stags := NoInfo; str := "preamble" |},
                                (TypBit 64%N) );
                              ( {| stags := NoInfo; str := "device" |},
                                (TypBit 8%N) );
                              ( {| stags := NoInfo; str := "reason" |},
                                (TypBit 8%N) );
                              ( {| stags := NoInfo; str := "if_index" |},
                                (TypBit 8%N) )]) Directionless))]) StmUnit)]
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
                                    (TypTypeName (
                                      {| stags := NoInfo;
                                         str := "packet_in" |}))
                                    Directionless)
                               {| stags := NoInfo; str := "extract" |})
                          (TypFunction
                           (MkFunctionType
                                [{| stags := NoInfo; str := "T" |}]
                                [(MkParameter false Out
                                      (TypTypeName (
                                        {| stags := NoInfo; str := "T" |}))
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
                                      (TypTypeName (
                                        {| stags := NoInfo;
                                           str := "headers" |})) Out)
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
                                         (TypTypeName (
                                           {| stags := NoInfo;
                                              str := "headers" |})) Out)
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
     (MkParserState NoInfo {| stags := NoInfo; str := "parse_ipv4" |}
          [(MkStatement NoInfo
                (StatAssignment
                     (MkExpression NoInfo
                          (ExpExpressionMember
                               (MkExpression NoInfo
                                    (ExpExpressionMember
                                         (MkExpression NoInfo
                                              (ExpName
                                               (BareName
                                                {| stags := NoInfo;
                                                   str := "meta" |})
                                               NoLocator)
                                              (TypTypeName (
                                                {| stags := NoInfo;
                                                   str := "metadata" |}))
                                              InOut)
                                         {| stags := NoInfo; str := "meta" |})
                                    (TypStruct
                                     [( {| stags := NoInfo;
                                           str := "do_forward" |},
                                        (TypBit 1%N) );
                                      ( {| stags := NoInfo;
                                           str := "ipv4_sa" |},
                                        (TypBit 32%N) );
                                      ( {| stags := NoInfo;
                                           str := "ipv4_da" |},
                                        (TypBit 32%N) );
                                      ( {| stags := NoInfo;
                                           str := "tcp_sp" |},
                                        (TypBit 16%N) );
                                      ( {| stags := NoInfo;
                                           str := "tcp_dp" |},
                                        (TypBit 16%N) );
                                      ( {| stags := NoInfo;
                                           str := "nhop_ipv4" |},
                                        (TypBit 32%N) );
                                      ( {| stags := NoInfo;
                                           str := "if_ipv4_addr" |},
                                        (TypBit 32%N) );
                                      ( {| stags := NoInfo;
                                           str := "if_mac_addr" |},
                                        (TypBit 48%N) );
                                      ( {| stags := NoInfo;
                                           str := "is_ext_if" |},
                                        (TypBit 1%N) );
                                      ( {| stags := NoInfo;
                                           str := "tcpLength" |},
                                        (TypBit 16%N) );
                                      ( {| stags := NoInfo;
                                           str := "if_index" |},
                                        (TypBit 8%N) );
                                      ( {| stags := NoInfo;
                                           str := "init_egress_spec" |},
                                        (TypBit 9%N) )]) Directionless)
                               {| stags := NoInfo; str := "tcpLength" |})
                          (TypBit 16%N) Directionless)
                     (MkExpression NoInfo
                          (ExpBinaryOp Minus
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
                                                          (TypTypeName (
                                                            {| stags := NoInfo;
                                                               str := "headers" |}))
                                                          Out)
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
                                              str := "totalLen" |})
                                      (TypBit 16%N) Directionless)
                                 (MkExpression NoInfo
                                      (ExpInt
                                       {| itags := NoInfo; value := 20;
                                          width_signed := (Some
                                                           ( 16%N, false )) |})
                                      (TypBit 16%N) Directionless))
                          (TypBit 16%N) Directionless)) StmUnit);
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
                                                   str := "meta" |})
                                               NoLocator)
                                              (TypTypeName (
                                                {| stags := NoInfo;
                                                   str := "metadata" |}))
                                              InOut)
                                         {| stags := NoInfo; str := "meta" |})
                                    (TypStruct
                                     [( {| stags := NoInfo;
                                           str := "do_forward" |},
                                        (TypBit 1%N) );
                                      ( {| stags := NoInfo;
                                           str := "ipv4_sa" |},
                                        (TypBit 32%N) );
                                      ( {| stags := NoInfo;
                                           str := "ipv4_da" |},
                                        (TypBit 32%N) );
                                      ( {| stags := NoInfo;
                                           str := "tcp_sp" |},
                                        (TypBit 16%N) );
                                      ( {| stags := NoInfo;
                                           str := "tcp_dp" |},
                                        (TypBit 16%N) );
                                      ( {| stags := NoInfo;
                                           str := "nhop_ipv4" |},
                                        (TypBit 32%N) );
                                      ( {| stags := NoInfo;
                                           str := "if_ipv4_addr" |},
                                        (TypBit 32%N) );
                                      ( {| stags := NoInfo;
                                           str := "if_mac_addr" |},
                                        (TypBit 48%N) );
                                      ( {| stags := NoInfo;
                                           str := "is_ext_if" |},
                                        (TypBit 1%N) );
                                      ( {| stags := NoInfo;
                                           str := "tcpLength" |},
                                        (TypBit 16%N) );
                                      ( {| stags := NoInfo;
                                           str := "if_index" |},
                                        (TypBit 8%N) );
                                      ( {| stags := NoInfo;
                                           str := "init_egress_spec" |},
                                        (TypBit 9%N) )]) Directionless)
                               {| stags := NoInfo; str := "ipv4_da" |})
                          (TypBit 32%N) Directionless)
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
                                              (TypTypeName (
                                                {| stags := NoInfo;
                                                   str := "headers" |})) Out)
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
                               {| stags := NoInfo; str := "dstAddr" |})
                          (TypBit 32%N) Directionless)) StmUnit);
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
                                                   str := "meta" |})
                                               NoLocator)
                                              (TypTypeName (
                                                {| stags := NoInfo;
                                                   str := "metadata" |}))
                                              InOut)
                                         {| stags := NoInfo; str := "meta" |})
                                    (TypStruct
                                     [( {| stags := NoInfo;
                                           str := "do_forward" |},
                                        (TypBit 1%N) );
                                      ( {| stags := NoInfo;
                                           str := "ipv4_sa" |},
                                        (TypBit 32%N) );
                                      ( {| stags := NoInfo;
                                           str := "ipv4_da" |},
                                        (TypBit 32%N) );
                                      ( {| stags := NoInfo;
                                           str := "tcp_sp" |},
                                        (TypBit 16%N) );
                                      ( {| stags := NoInfo;
                                           str := "tcp_dp" |},
                                        (TypBit 16%N) );
                                      ( {| stags := NoInfo;
                                           str := "nhop_ipv4" |},
                                        (TypBit 32%N) );
                                      ( {| stags := NoInfo;
                                           str := "if_ipv4_addr" |},
                                        (TypBit 32%N) );
                                      ( {| stags := NoInfo;
                                           str := "if_mac_addr" |},
                                        (TypBit 48%N) );
                                      ( {| stags := NoInfo;
                                           str := "is_ext_if" |},
                                        (TypBit 1%N) );
                                      ( {| stags := NoInfo;
                                           str := "tcpLength" |},
                                        (TypBit 16%N) );
                                      ( {| stags := NoInfo;
                                           str := "if_index" |},
                                        (TypBit 8%N) );
                                      ( {| stags := NoInfo;
                                           str := "init_egress_spec" |},
                                        (TypBit 9%N) )]) Directionless)
                               {| stags := NoInfo; str := "ipv4_sa" |})
                          (TypBit 32%N) Directionless)
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
                                              (TypTypeName (
                                                {| stags := NoInfo;
                                                   str := "headers" |})) Out)
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
                               {| stags := NoInfo; str := "srcAddr" |})
                          (TypBit 32%N) Directionless)) StmUnit);
           (MkStatement NoInfo
                (StatMethodCall
                     (MkExpression NoInfo
                          (ExpExpressionMember
                               (MkExpression NoInfo
                                    (ExpName
                                     (BareName
                                      {| stags := NoInfo; str := "packet" |})
                                     NoLocator)
                                    (TypTypeName (
                                      {| stags := NoInfo;
                                         str := "packet_in" |}))
                                    Directionless)
                               {| stags := NoInfo; str := "extract" |})
                          (TypFunction
                           (MkFunctionType
                                [{| stags := NoInfo; str := "T" |}]
                                [(MkParameter false Out
                                      (TypTypeName (
                                        {| stags := NoInfo; str := "T" |}))
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
                                      (TypTypeName (
                                        {| stags := NoInfo;
                                           str := "headers" |})) Out)
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
                                         (TypTypeName (
                                           {| stags := NoInfo;
                                              str := "headers" |})) Out)
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
                                                           value := 6;
                                                           width_signed := (
                                                           Some
                                                           ( 8%N, false )) |})
                                                       (TypBit 8%N)
                                                       Directionless))
                           (TypBit 8%N))]
                     {| stags := NoInfo; str := "parse_tcp" |});
                (MkParserCase NoInfo
                     [(MkMatch NoInfo MatchDontCare (TypBit 8%N))]
                     {| stags := NoInfo; str := "accept" |})]));
     (MkParserState NoInfo {| stags := NoInfo; str := "parse_tcp" |}
          [(MkStatement NoInfo
                (StatAssignment
                     (MkExpression NoInfo
                          (ExpExpressionMember
                               (MkExpression NoInfo
                                    (ExpExpressionMember
                                         (MkExpression NoInfo
                                              (ExpName
                                               (BareName
                                                {| stags := NoInfo;
                                                   str := "meta" |})
                                               NoLocator)
                                              (TypTypeName (
                                                {| stags := NoInfo;
                                                   str := "metadata" |}))
                                              InOut)
                                         {| stags := NoInfo; str := "meta" |})
                                    (TypStruct
                                     [( {| stags := NoInfo;
                                           str := "do_forward" |},
                                        (TypBit 1%N) );
                                      ( {| stags := NoInfo;
                                           str := "ipv4_sa" |},
                                        (TypBit 32%N) );
                                      ( {| stags := NoInfo;
                                           str := "ipv4_da" |},
                                        (TypBit 32%N) );
                                      ( {| stags := NoInfo;
                                           str := "tcp_sp" |},
                                        (TypBit 16%N) );
                                      ( {| stags := NoInfo;
                                           str := "tcp_dp" |},
                                        (TypBit 16%N) );
                                      ( {| stags := NoInfo;
                                           str := "nhop_ipv4" |},
                                        (TypBit 32%N) );
                                      ( {| stags := NoInfo;
                                           str := "if_ipv4_addr" |},
                                        (TypBit 32%N) );
                                      ( {| stags := NoInfo;
                                           str := "if_mac_addr" |},
                                        (TypBit 48%N) );
                                      ( {| stags := NoInfo;
                                           str := "is_ext_if" |},
                                        (TypBit 1%N) );
                                      ( {| stags := NoInfo;
                                           str := "tcpLength" |},
                                        (TypBit 16%N) );
                                      ( {| stags := NoInfo;
                                           str := "if_index" |},
                                        (TypBit 8%N) );
                                      ( {| stags := NoInfo;
                                           str := "init_egress_spec" |},
                                        (TypBit 9%N) )]) Directionless)
                               {| stags := NoInfo; str := "tcp_dp" |})
                          (TypBit 16%N) Directionless)
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
                                              (TypTypeName (
                                                {| stags := NoInfo;
                                                   str := "headers" |})) Out)
                                         {| stags := NoInfo; str := "tcp" |})
                                    (TypHeader
                                     [( {| stags := NoInfo;
                                           str := "srcPort" |},
                                        (TypBit 16%N) );
                                      ( {| stags := NoInfo;
                                           str := "dstPort" |},
                                        (TypBit 16%N) );
                                      ( {| stags := NoInfo; str := "seqNo" |},
                                        (TypBit 32%N) );
                                      ( {| stags := NoInfo; str := "ackNo" |},
                                        (TypBit 32%N) );
                                      ( {| stags := NoInfo;
                                           str := "dataOffset" |},
                                        (TypBit 4%N) );
                                      ( {| stags := NoInfo; str := "res" |},
                                        (TypBit 4%N) );
                                      ( {| stags := NoInfo; str := "flags" |},
                                        (TypBit 8%N) );
                                      ( {| stags := NoInfo;
                                           str := "window" |},
                                        (TypBit 16%N) );
                                      ( {| stags := NoInfo;
                                           str := "checksum" |},
                                        (TypBit 16%N) );
                                      ( {| stags := NoInfo;
                                           str := "urgentPtr" |},
                                        (TypBit 16%N) )]) Directionless)
                               {| stags := NoInfo; str := "dstPort" |})
                          (TypBit 16%N) Directionless)) StmUnit);
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
                                                   str := "meta" |})
                                               NoLocator)
                                              (TypTypeName (
                                                {| stags := NoInfo;
                                                   str := "metadata" |}))
                                              InOut)
                                         {| stags := NoInfo; str := "meta" |})
                                    (TypStruct
                                     [( {| stags := NoInfo;
                                           str := "do_forward" |},
                                        (TypBit 1%N) );
                                      ( {| stags := NoInfo;
                                           str := "ipv4_sa" |},
                                        (TypBit 32%N) );
                                      ( {| stags := NoInfo;
                                           str := "ipv4_da" |},
                                        (TypBit 32%N) );
                                      ( {| stags := NoInfo;
                                           str := "tcp_sp" |},
                                        (TypBit 16%N) );
                                      ( {| stags := NoInfo;
                                           str := "tcp_dp" |},
                                        (TypBit 16%N) );
                                      ( {| stags := NoInfo;
                                           str := "nhop_ipv4" |},
                                        (TypBit 32%N) );
                                      ( {| stags := NoInfo;
                                           str := "if_ipv4_addr" |},
                                        (TypBit 32%N) );
                                      ( {| stags := NoInfo;
                                           str := "if_mac_addr" |},
                                        (TypBit 48%N) );
                                      ( {| stags := NoInfo;
                                           str := "is_ext_if" |},
                                        (TypBit 1%N) );
                                      ( {| stags := NoInfo;
                                           str := "tcpLength" |},
                                        (TypBit 16%N) );
                                      ( {| stags := NoInfo;
                                           str := "if_index" |},
                                        (TypBit 8%N) );
                                      ( {| stags := NoInfo;
                                           str := "init_egress_spec" |},
                                        (TypBit 9%N) )]) Directionless)
                               {| stags := NoInfo; str := "tcp_sp" |})
                          (TypBit 16%N) Directionless)
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
                                              (TypTypeName (
                                                {| stags := NoInfo;
                                                   str := "headers" |})) Out)
                                         {| stags := NoInfo; str := "tcp" |})
                                    (TypHeader
                                     [( {| stags := NoInfo;
                                           str := "srcPort" |},
                                        (TypBit 16%N) );
                                      ( {| stags := NoInfo;
                                           str := "dstPort" |},
                                        (TypBit 16%N) );
                                      ( {| stags := NoInfo; str := "seqNo" |},
                                        (TypBit 32%N) );
                                      ( {| stags := NoInfo; str := "ackNo" |},
                                        (TypBit 32%N) );
                                      ( {| stags := NoInfo;
                                           str := "dataOffset" |},
                                        (TypBit 4%N) );
                                      ( {| stags := NoInfo; str := "res" |},
                                        (TypBit 4%N) );
                                      ( {| stags := NoInfo; str := "flags" |},
                                        (TypBit 8%N) );
                                      ( {| stags := NoInfo;
                                           str := "window" |},
                                        (TypBit 16%N) );
                                      ( {| stags := NoInfo;
                                           str := "checksum" |},
                                        (TypBit 16%N) );
                                      ( {| stags := NoInfo;
                                           str := "urgentPtr" |},
                                        (TypBit 16%N) )]) Directionless)
                               {| stags := NoInfo; str := "srcPort" |})
                          (TypBit 16%N) Directionless)) StmUnit);
           (MkStatement NoInfo
                (StatMethodCall
                     (MkExpression NoInfo
                          (ExpExpressionMember
                               (MkExpression NoInfo
                                    (ExpName
                                     (BareName
                                      {| stags := NoInfo; str := "packet" |})
                                     NoLocator)
                                    (TypTypeName (
                                      {| stags := NoInfo;
                                         str := "packet_in" |}))
                                    Directionless)
                               {| stags := NoInfo; str := "extract" |})
                          (TypFunction
                           (MkFunctionType
                                [{| stags := NoInfo; str := "T" |}]
                                [(MkParameter false Out
                                      (TypTypeName (
                                        {| stags := NoInfo; str := "T" |}))
                                      None
                                      {| stags := NoInfo; str := "hdr" |})]
                                FunExtern TypVoid)) Directionless)
                     [(TypHeader
                       [( {| stags := NoInfo; str := "srcPort" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "dstPort" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "seqNo" |},
                          (TypBit 32%N) );
                        ( {| stags := NoInfo; str := "ackNo" |},
                          (TypBit 32%N) );
                        ( {| stags := NoInfo; str := "dataOffset" |},
                          (TypBit 4%N) );
                        ( {| stags := NoInfo; str := "res" |}, (TypBit 4%N) );
                        ( {| stags := NoInfo; str := "flags" |},
                          (TypBit 8%N) );
                        ( {| stags := NoInfo; str := "window" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "checksum" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "urgentPtr" |},
                          (TypBit 16%N) )])]
                     [(Some
                       (MkExpression NoInfo
                            (ExpExpressionMember
                                 (MkExpression NoInfo
                                      (ExpName
                                       (BareName
                                        {| stags := NoInfo; str := "hdr" |})
                                       NoLocator)
                                      (TypTypeName (
                                        {| stags := NoInfo;
                                           str := "headers" |})) Out)
                                 {| stags := NoInfo; str := "tcp" |})
                            (TypHeader
                             [( {| stags := NoInfo; str := "srcPort" |},
                                (TypBit 16%N) );
                              ( {| stags := NoInfo; str := "dstPort" |},
                                (TypBit 16%N) );
                              ( {| stags := NoInfo; str := "seqNo" |},
                                (TypBit 32%N) );
                              ( {| stags := NoInfo; str := "ackNo" |},
                                (TypBit 32%N) );
                              ( {| stags := NoInfo; str := "dataOffset" |},
                                (TypBit 4%N) );
                              ( {| stags := NoInfo; str := "res" |},
                                (TypBit 4%N) );
                              ( {| stags := NoInfo; str := "flags" |},
                                (TypBit 8%N) );
                              ( {| stags := NoInfo; str := "window" |},
                                (TypBit 16%N) );
                              ( {| stags := NoInfo; str := "checksum" |},
                                (TypBit 16%N) );
                              ( {| stags := NoInfo; str := "urgentPtr" |},
                                (TypBit 16%N) )]) Directionless))]) StmUnit)]
          (ParserDirect NoInfo {| stags := NoInfo; str := "accept" |}));
     (MkParserState NoInfo {| stags := NoInfo; str := "start" |}
          [(MkStatement NoInfo
                (StatAssignment
                     (MkExpression NoInfo
                          (ExpExpressionMember
                               (MkExpression NoInfo
                                    (ExpExpressionMember
                                         (MkExpression NoInfo
                                              (ExpName
                                               (BareName
                                                {| stags := NoInfo;
                                                   str := "meta" |})
                                               NoLocator)
                                              (TypTypeName (
                                                {| stags := NoInfo;
                                                   str := "metadata" |}))
                                              InOut)
                                         {| stags := NoInfo; str := "meta" |})
                                    (TypStruct
                                     [( {| stags := NoInfo;
                                           str := "do_forward" |},
                                        (TypBit 1%N) );
                                      ( {| stags := NoInfo;
                                           str := "ipv4_sa" |},
                                        (TypBit 32%N) );
                                      ( {| stags := NoInfo;
                                           str := "ipv4_da" |},
                                        (TypBit 32%N) );
                                      ( {| stags := NoInfo;
                                           str := "tcp_sp" |},
                                        (TypBit 16%N) );
                                      ( {| stags := NoInfo;
                                           str := "tcp_dp" |},
                                        (TypBit 16%N) );
                                      ( {| stags := NoInfo;
                                           str := "nhop_ipv4" |},
                                        (TypBit 32%N) );
                                      ( {| stags := NoInfo;
                                           str := "if_ipv4_addr" |},
                                        (TypBit 32%N) );
                                      ( {| stags := NoInfo;
                                           str := "if_mac_addr" |},
                                        (TypBit 48%N) );
                                      ( {| stags := NoInfo;
                                           str := "is_ext_if" |},
                                        (TypBit 1%N) );
                                      ( {| stags := NoInfo;
                                           str := "tcpLength" |},
                                        (TypBit 16%N) );
                                      ( {| stags := NoInfo;
                                           str := "if_index" |},
                                        (TypBit 8%N) );
                                      ( {| stags := NoInfo;
                                           str := "init_egress_spec" |},
                                        (TypBit 9%N) )]) Directionless)
                               {| stags := NoInfo; str := "if_index" |})
                          (TypBit 8%N) Directionless)
                     (MkExpression NoInfo
                          (ExpCast (TypBit 8%N)
                               (MkExpression NoInfo
                                    (ExpExpressionMember
                                         (MkExpression NoInfo
                                              (ExpName
                                               (BareName
                                                {| stags := NoInfo;
                                                   str := "standard_metadata" |})
                                               NoLocator)
                                              (TypTypeName (
                                                {| stags := NoInfo;
                                                   str := "standard_metadata_t" |}))
                                              InOut)
                                         {| stags := NoInfo;
                                            str := "ingress_port" |})
                                    (TypBit 9%N) Directionless)) (TypBit 8%N)
                          Directionless)) StmUnit)]
          (ParserSelect NoInfo
               [(MkExpression NoInfo
                     (ExpBitStringAccess
                          (MkExpression NoInfo
                               (ExpFunctionCall
                                    (MkExpression NoInfo
                                         (ExpExpressionMember
                                              (MkExpression NoInfo
                                                   (ExpName
                                                    (BareName
                                                     {| stags := NoInfo;
                                                        str := "packet" |})
                                                    NoLocator)
                                                   (TypTypeName (
                                                     {| stags := NoInfo;
                                                        str := "packet_in" |}))
                                                   Directionless)
                                              {| stags := NoInfo;
                                                 str := "lookahead" |})
                                         (TypFunction
                                          (MkFunctionType
                                               [{| stags := NoInfo;
                                                   str := "T1" |}] nil
                                               FunExtern
                                               (TypTypeName (
                                                 {| stags := NoInfo;
                                                    str := "T1" |}))))
                                         Directionless) [(TypBit 64%N)] nil)
                               (TypBit 64%N) Directionless) 0%N 63%N)
                     (TypBit 64%N) Directionless)]
               [(MkParserCase NoInfo
                     [(MkMatch NoInfo
                           (MatchCast
                            (TypSet (TypBit 64%N)) (MkExpression NoInfo
                                                        (ExpInt
                                                         {| itags := NoInfo;
                                                            value := 0;
                                                            width_signed := (
                                                            Some
                                                            ( 64%N, false )) |})
                                                        (TypBit 64%N)
                                                        Directionless))
                           (TypBit 64%N))]
                     {| stags := NoInfo; str := "parse_cpu_header" |});
                (MkParserCase NoInfo
                     [(MkMatch NoInfo MatchDontCare (TypBit 64%N))]
                     {| stags := NoInfo; str := "parse_ethernet" |})]))].

Definition egress := DeclControl NoInfo
    {| stags := NoInfo; str := "egress" |} nil
    [(MkParameter false InOut
          (TypTypeName ( {| stags := NoInfo; str := "headers" |}))
          None {| stags := NoInfo; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName ( {| stags := NoInfo; str := "metadata" |}))
          None {| stags := NoInfo; str := "meta" |});
     (MkParameter false InOut
          (TypTypeName ( {| stags := NoInfo; str := "standard_metadata_t" |}))
          None {| stags := NoInfo; str := "standard_metadata" |})] nil
    [(DeclAction NoInfo {| stags := NoInfo; str := "do_rewrites" |} nil
          [(MkParameter false Directionless (TypBit 48%N) None
                {| stags := NoInfo; str := "smac" |})]
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
                                                  (TypTypeName (
                                                    {| stags := NoInfo;
                                                       str := "headers" |}))
                                                  InOut)
                                             {| stags := NoInfo;
                                                str := "cpu_header" |})
                                        (TypHeader
                                         [( {| stags := NoInfo;
                                               str := "preamble" |},
                                            (TypBit 64%N) );
                                          ( {| stags := NoInfo;
                                               str := "device" |},
                                            (TypBit 8%N) );
                                          ( {| stags := NoInfo;
                                               str := "reason" |},
                                            (TypBit 8%N) );
                                          ( {| stags := NoInfo;
                                               str := "if_index" |},
                                            (TypBit 8%N) )]) Directionless)
                                   {| stags := NoInfo; str := "setInvalid" |})
                              (TypFunction
                               (MkFunctionType nil nil FunBuiltin TypVoid))
                              Directionless) nil nil) StmUnit)
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
                                                       (TypTypeName (
                                                         {| stags := NoInfo;
                                                            str := "headers" |}))
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
                                           str := "srcAddr" |}) (TypBit 48%N)
                                   Directionless)
                              (MkExpression NoInfo
                                   (ExpName
                                    (BareName
                                     {| stags := NoInfo; str := "smac" |})
                                    NoLocator) (TypBit 48%N) In)) StmUnit)
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
                                                            (TypTypeName (
                                                              {| stags := NoInfo;
                                                                 str := "headers" |}))
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
                                                str := "srcAddr" |})
                                        (TypBit 32%N) Directionless)
                                   (MkExpression NoInfo
                                        (ExpExpressionMember
                                             (MkExpression NoInfo
                                                  (ExpExpressionMember
                                                       (MkExpression NoInfo
                                                            (ExpName
                                                             (BareName
                                                              {| stags := NoInfo;
                                                                 str := "meta" |})
                                                             NoLocator)
                                                            (TypTypeName (
                                                              {| stags := NoInfo;
                                                                 str := "metadata" |}))
                                                            InOut)
                                                       {| stags := NoInfo;
                                                          str := "meta" |})
                                                  (TypStruct
                                                   [( {| stags := NoInfo;
                                                         str := "do_forward" |},
                                                      (TypBit 1%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "ipv4_sa" |},
                                                      (TypBit 32%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "ipv4_da" |},
                                                      (TypBit 32%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "tcp_sp" |},
                                                      (TypBit 16%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "tcp_dp" |},
                                                      (TypBit 16%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "nhop_ipv4" |},
                                                      (TypBit 32%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "if_ipv4_addr" |},
                                                      (TypBit 32%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "if_mac_addr" |},
                                                      (TypBit 48%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "is_ext_if" |},
                                                      (TypBit 1%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "tcpLength" |},
                                                      (TypBit 16%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "if_index" |},
                                                      (TypBit 8%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "init_egress_spec" |},
                                                      (TypBit 9%N) )])
                                                  Directionless)
                                             {| stags := NoInfo;
                                                str := "ipv4_sa" |})
                                        (TypBit 32%N) Directionless))
                              StmUnit)
                         (BlockCons
                              (MkStatement NoInfo
                                   (StatAssignment
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
                                                                 (TypTypeName (
                                                                   {| 
                                                                   stags := NoInfo;
                                                                   str := "headers" |}))
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
                                                     str := "dstAddr" |})
                                             (TypBit 32%N) Directionless)
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
                                                                   str := "meta" |})
                                                                  NoLocator)
                                                                 (TypTypeName (
                                                                   {| 
                                                                   stags := NoInfo;
                                                                   str := "metadata" |}))
                                                                 InOut)
                                                            {| stags := NoInfo;
                                                               str := "meta" |})
                                                       (TypStruct
                                                        [( {| stags := NoInfo;
                                                              str := "do_forward" |},
                                                           (TypBit 1%N) );
                                                         ( {| stags := NoInfo;
                                                              str := "ipv4_sa" |},
                                                           (TypBit 32%N) );
                                                         ( {| stags := NoInfo;
                                                              str := "ipv4_da" |},
                                                           (TypBit 32%N) );
                                                         ( {| stags := NoInfo;
                                                              str := "tcp_sp" |},
                                                           (TypBit 16%N) );
                                                         ( {| stags := NoInfo;
                                                              str := "tcp_dp" |},
                                                           (TypBit 16%N) );
                                                         ( {| stags := NoInfo;
                                                              str := "nhop_ipv4" |},
                                                           (TypBit 32%N) );
                                                         ( {| stags := NoInfo;
                                                              str := "if_ipv4_addr" |},
                                                           (TypBit 32%N) );
                                                         ( {| stags := NoInfo;
                                                              str := "if_mac_addr" |},
                                                           (TypBit 48%N) );
                                                         ( {| stags := NoInfo;
                                                              str := "is_ext_if" |},
                                                           (TypBit 1%N) );
                                                         ( {| stags := NoInfo;
                                                              str := "tcpLength" |},
                                                           (TypBit 16%N) );
                                                         ( {| stags := NoInfo;
                                                              str := "if_index" |},
                                                           (TypBit 8%N) );
                                                         ( {| stags := NoInfo;
                                                              str := "init_egress_spec" |},
                                                           (TypBit 9%N) )])
                                                       Directionless)
                                                  {| stags := NoInfo;
                                                     str := "ipv4_da" |})
                                             (TypBit 32%N) Directionless))
                                   StmUnit)
                              (BlockCons
                                   (MkStatement NoInfo
                                        (StatAssignment
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
                                                                    (TypTypeName (
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "headers" |}))
                                                                    InOut)
                                                                 {| stags := NoInfo;
                                                                    str := "tcp" |})
                                                            (TypHeader
                                                             [( {| stags := NoInfo;
                                                                   str := "srcPort" |},
                                                                (TypBit 16%N) );
                                                              ( {| stags := NoInfo;
                                                                   str := "dstPort" |},
                                                                (TypBit 16%N) );
                                                              ( {| stags := NoInfo;
                                                                   str := "seqNo" |},
                                                                (TypBit 32%N) );
                                                              ( {| stags := NoInfo;
                                                                   str := "ackNo" |},
                                                                (TypBit 32%N) );
                                                              ( {| stags := NoInfo;
                                                                   str := "dataOffset" |},
                                                                (TypBit 4%N) );
                                                              ( {| stags := NoInfo;
                                                                   str := "res" |},
                                                                (TypBit 4%N) );
                                                              ( {| stags := NoInfo;
                                                                   str := "flags" |},
                                                                (TypBit 8%N) );
                                                              ( {| stags := NoInfo;
                                                                   str := "window" |},
                                                                (TypBit 16%N) );
                                                              ( {| stags := NoInfo;
                                                                   str := "checksum" |},
                                                                (TypBit 16%N) );
                                                              ( {| stags := NoInfo;
                                                                   str := "urgentPtr" |},
                                                                (TypBit 16%N) )])
                                                            Directionless)
                                                       {| stags := NoInfo;
                                                          str := "srcPort" |})
                                                  (TypBit 16%N)
                                                  Directionless)
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
                                                                    str := "meta" |})
                                                                    NoLocator)
                                                                    (TypTypeName (
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "metadata" |}))
                                                                    InOut)
                                                                 {| stags := NoInfo;
                                                                    str := "meta" |})
                                                            (TypStruct
                                                             [( {| stags := NoInfo;
                                                                   str := "do_forward" |},
                                                                (TypBit 1%N) );
                                                              ( {| stags := NoInfo;
                                                                   str := "ipv4_sa" |},
                                                                (TypBit 32%N) );
                                                              ( {| stags := NoInfo;
                                                                   str := "ipv4_da" |},
                                                                (TypBit 32%N) );
                                                              ( {| stags := NoInfo;
                                                                   str := "tcp_sp" |},
                                                                (TypBit 16%N) );
                                                              ( {| stags := NoInfo;
                                                                   str := "tcp_dp" |},
                                                                (TypBit 16%N) );
                                                              ( {| stags := NoInfo;
                                                                   str := "nhop_ipv4" |},
                                                                (TypBit 32%N) );
                                                              ( {| stags := NoInfo;
                                                                   str := "if_ipv4_addr" |},
                                                                (TypBit 32%N) );
                                                              ( {| stags := NoInfo;
                                                                   str := "if_mac_addr" |},
                                                                (TypBit 48%N) );
                                                              ( {| stags := NoInfo;
                                                                   str := "is_ext_if" |},
                                                                (TypBit 1%N) );
                                                              ( {| stags := NoInfo;
                                                                   str := "tcpLength" |},
                                                                (TypBit 16%N) );
                                                              ( {| stags := NoInfo;
                                                                   str := "if_index" |},
                                                                (TypBit 8%N) );
                                                              ( {| stags := NoInfo;
                                                                   str := "init_egress_spec" |},
                                                                (TypBit 9%N) )])
                                                            Directionless)
                                                       {| stags := NoInfo;
                                                          str := "tcp_sp" |})
                                                  (TypBit 16%N)
                                                  Directionless)) StmUnit)
                                   (BlockCons
                                        (MkStatement NoInfo
                                             (StatAssignment
                                                  (MkExpression NoInfo
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
                                                                    (TypTypeName (
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "headers" |}))
                                                                    InOut)
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "tcp" |})
                                                                 (TypHeader
                                                                  [( 
                                                                   {| 
                                                                   stags := NoInfo;
                                                                   str := "srcPort" |},
                                                                   (TypBit
                                                                    16%N) );
                                                                   ( 
                                                                   {| 
                                                                   stags := NoInfo;
                                                                   str := "dstPort" |},
                                                                   (TypBit
                                                                    16%N) );
                                                                   ( 
                                                                   {| 
                                                                   stags := NoInfo;
                                                                   str := "seqNo" |},
                                                                   (TypBit
                                                                    32%N) );
                                                                   ( 
                                                                   {| 
                                                                   stags := NoInfo;
                                                                   str := "ackNo" |},
                                                                   (TypBit
                                                                    32%N) );
                                                                   ( 
                                                                   {| 
                                                                   stags := NoInfo;
                                                                   str := "dataOffset" |},
                                                                   (TypBit
                                                                    4%N) );
                                                                   ( 
                                                                   {| 
                                                                   stags := NoInfo;
                                                                   str := "res" |},
                                                                   (TypBit
                                                                    4%N) );
                                                                   ( 
                                                                   {| 
                                                                   stags := NoInfo;
                                                                   str := "flags" |},
                                                                   (TypBit
                                                                    8%N) );
                                                                   ( 
                                                                   {| 
                                                                   stags := NoInfo;
                                                                   str := "window" |},
                                                                   (TypBit
                                                                    16%N) );
                                                                   ( 
                                                                   {| 
                                                                   stags := NoInfo;
                                                                   str := "checksum" |},
                                                                   (TypBit
                                                                    16%N) );
                                                                   ( 
                                                                   {| 
                                                                   stags := NoInfo;
                                                                   str := "urgentPtr" |},
                                                                   (TypBit
                                                                    16%N) )])
                                                                 Directionless)
                                                            {| stags := NoInfo;
                                                               str := "dstPort" |})
                                                       (TypBit 16%N)
                                                       Directionless)
                                                  (MkExpression NoInfo
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
                                                                    str := "meta" |})
                                                                    NoLocator)
                                                                    (TypTypeName (
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "metadata" |}))
                                                                    InOut)
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "meta" |})
                                                                 (TypStruct
                                                                  [( 
                                                                   {| 
                                                                   stags := NoInfo;
                                                                   str := "do_forward" |},
                                                                   (TypBit
                                                                    1%N) );
                                                                   ( 
                                                                   {| 
                                                                   stags := NoInfo;
                                                                   str := "ipv4_sa" |},
                                                                   (TypBit
                                                                    32%N) );
                                                                   ( 
                                                                   {| 
                                                                   stags := NoInfo;
                                                                   str := "ipv4_da" |},
                                                                   (TypBit
                                                                    32%N) );
                                                                   ( 
                                                                   {| 
                                                                   stags := NoInfo;
                                                                   str := "tcp_sp" |},
                                                                   (TypBit
                                                                    16%N) );
                                                                   ( 
                                                                   {| 
                                                                   stags := NoInfo;
                                                                   str := "tcp_dp" |},
                                                                   (TypBit
                                                                    16%N) );
                                                                   ( 
                                                                   {| 
                                                                   stags := NoInfo;
                                                                   str := "nhop_ipv4" |},
                                                                   (TypBit
                                                                    32%N) );
                                                                   ( 
                                                                   {| 
                                                                   stags := NoInfo;
                                                                   str := "if_ipv4_addr" |},
                                                                   (TypBit
                                                                    32%N) );
                                                                   ( 
                                                                   {| 
                                                                   stags := NoInfo;
                                                                   str := "if_mac_addr" |},
                                                                   (TypBit
                                                                    48%N) );
                                                                   ( 
                                                                   {| 
                                                                   stags := NoInfo;
                                                                   str := "is_ext_if" |},
                                                                   (TypBit
                                                                    1%N) );
                                                                   ( 
                                                                   {| 
                                                                   stags := NoInfo;
                                                                   str := "tcpLength" |},
                                                                   (TypBit
                                                                    16%N) );
                                                                   ( 
                                                                   {| 
                                                                   stags := NoInfo;
                                                                   str := "if_index" |},
                                                                   (TypBit
                                                                    8%N) );
                                                                   ( 
                                                                   {| 
                                                                   stags := NoInfo;
                                                                   str := "init_egress_spec" |},
                                                                   (TypBit
                                                                    9%N) )])
                                                                 Directionless)
                                                            {| stags := NoInfo;
                                                               str := "tcp_dp" |})
                                                       (TypBit 16%N)
                                                       Directionless))
                                             StmUnit) (BlockEmpty NoInfo))))))));
     (DeclAction NoInfo {| stags := NoInfo; str := "_drop" |} nil nil
          (BlockCons
               (MkStatement NoInfo
                    (StatMethodCall
                         (MkExpression NoInfo
                              (ExpName
                               (BareName
                                {| stags := NoInfo; str := "mark_to_drop" |})
                               NoLocator)
                              (TypFunction
                               (MkFunctionType nil
                                    [(MkParameter false InOut
                                          (TypTypeName (
                                            {| stags := NoInfo;
                                               str := "standard_metadata_t" |}))
                                          None
                                          {| stags := NoInfo;
                                             str := "standard_metadata" |})]
                                    FunExtern TypVoid)) Directionless) nil
                         [(Some
                           (MkExpression NoInfo
                                (ExpName
                                 (BareName
                                  {| stags := NoInfo;
                                     str := "standard_metadata" |})
                                 NoLocator)
                                (TypTypeName (
                                  {| stags := NoInfo;
                                     str := "standard_metadata_t" |})) InOut))])
                    StmUnit) (BlockEmpty NoInfo)));
     (DeclAction NoInfo {| stags := NoInfo; str := "do_cpu_encap" |} nil nil
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
                                                  (TypTypeName (
                                                    {| stags := NoInfo;
                                                       str := "headers" |}))
                                                  InOut)
                                             {| stags := NoInfo;
                                                str := "cpu_header" |})
                                        (TypHeader
                                         [( {| stags := NoInfo;
                                               str := "preamble" |},
                                            (TypBit 64%N) );
                                          ( {| stags := NoInfo;
                                               str := "device" |},
                                            (TypBit 8%N) );
                                          ( {| stags := NoInfo;
                                               str := "reason" |},
                                            (TypBit 8%N) );
                                          ( {| stags := NoInfo;
                                               str := "if_index" |},
                                            (TypBit 8%N) )]) Directionless)
                                   {| stags := NoInfo; str := "setValid" |})
                              (TypFunction
                               (MkFunctionType nil nil FunBuiltin TypVoid))
                              Directionless) nil nil) StmUnit)
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
                                                       (TypTypeName (
                                                         {| stags := NoInfo;
                                                            str := "headers" |}))
                                                       InOut)
                                                  {| stags := NoInfo;
                                                     str := "cpu_header" |})
                                             (TypHeader
                                              [( {| stags := NoInfo;
                                                    str := "preamble" |},
                                                 (TypBit 64%N) );
                                               ( {| stags := NoInfo;
                                                    str := "device" |},
                                                 (TypBit 8%N) );
                                               ( {| stags := NoInfo;
                                                    str := "reason" |},
                                                 (TypBit 8%N) );
                                               ( {| stags := NoInfo;
                                                    str := "if_index" |},
                                                 (TypBit 8%N) )])
                                             Directionless)
                                        {| stags := NoInfo;
                                           str := "preamble" |})
                                   (TypBit 64%N) Directionless)
                              (MkExpression NoInfo
                                   (ExpInt
                                    {| itags := NoInfo; value := 0;
                                       width_signed := (Some ( 64%N, false )) |})
                                   (TypBit 64%N) Directionless)) StmUnit)
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
                                                            (TypTypeName (
                                                              {| stags := NoInfo;
                                                                 str := "headers" |}))
                                                            InOut)
                                                       {| stags := NoInfo;
                                                          str := "cpu_header" |})
                                                  (TypHeader
                                                   [( {| stags := NoInfo;
                                                         str := "preamble" |},
                                                      (TypBit 64%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "device" |},
                                                      (TypBit 8%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "reason" |},
                                                      (TypBit 8%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "if_index" |},
                                                      (TypBit 8%N) )])
                                                  Directionless)
                                             {| stags := NoInfo;
                                                str := "device" |})
                                        (TypBit 8%N) Directionless)
                                   (MkExpression NoInfo
                                        (ExpInt
                                         {| itags := NoInfo; value := 0;
                                            width_signed := (Some
                                                             ( 8%N, false )) |})
                                        (TypBit 8%N) Directionless)) StmUnit)
                         (BlockCons
                              (MkStatement NoInfo
                                   (StatAssignment
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
                                                                 (TypTypeName (
                                                                   {| 
                                                                   stags := NoInfo;
                                                                   str := "headers" |}))
                                                                 InOut)
                                                            {| stags := NoInfo;
                                                               str := "cpu_header" |})
                                                       (TypHeader
                                                        [( {| stags := NoInfo;
                                                              str := "preamble" |},
                                                           (TypBit 64%N) );
                                                         ( {| stags := NoInfo;
                                                              str := "device" |},
                                                           (TypBit 8%N) );
                                                         ( {| stags := NoInfo;
                                                              str := "reason" |},
                                                           (TypBit 8%N) );
                                                         ( {| stags := NoInfo;
                                                              str := "if_index" |},
                                                           (TypBit 8%N) )])
                                                       Directionless)
                                                  {| stags := NoInfo;
                                                     str := "reason" |})
                                             (TypBit 8%N) Directionless)
                                        (MkExpression NoInfo
                                             (ExpInt
                                              {| itags := NoInfo;
                                                 value := 171;
                                                 width_signed := (Some
                                                                  ( 8%N,
                                                                    false )) |})
                                             (TypBit 8%N) Directionless))
                                   StmUnit)
                              (BlockCons
                                   (MkStatement NoInfo
                                        (StatAssignment
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
                                                                    (TypTypeName (
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "headers" |}))
                                                                    InOut)
                                                                 {| stags := NoInfo;
                                                                    str := "cpu_header" |})
                                                            (TypHeader
                                                             [( {| stags := NoInfo;
                                                                   str := "preamble" |},
                                                                (TypBit 64%N) );
                                                              ( {| stags := NoInfo;
                                                                   str := "device" |},
                                                                (TypBit 8%N) );
                                                              ( {| stags := NoInfo;
                                                                   str := "reason" |},
                                                                (TypBit 8%N) );
                                                              ( {| stags := NoInfo;
                                                                   str := "if_index" |},
                                                                (TypBit 8%N) )])
                                                            Directionless)
                                                       {| stags := NoInfo;
                                                          str := "if_index" |})
                                                  (TypBit 8%N) Directionless)
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
                                                                    str := "meta" |})
                                                                    NoLocator)
                                                                    (TypTypeName (
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "metadata" |}))
                                                                    InOut)
                                                                 {| stags := NoInfo;
                                                                    str := "meta" |})
                                                            (TypStruct
                                                             [( {| stags := NoInfo;
                                                                   str := "do_forward" |},
                                                                (TypBit 1%N) );
                                                              ( {| stags := NoInfo;
                                                                   str := "ipv4_sa" |},
                                                                (TypBit 32%N) );
                                                              ( {| stags := NoInfo;
                                                                   str := "ipv4_da" |},
                                                                (TypBit 32%N) );
                                                              ( {| stags := NoInfo;
                                                                   str := "tcp_sp" |},
                                                                (TypBit 16%N) );
                                                              ( {| stags := NoInfo;
                                                                   str := "tcp_dp" |},
                                                                (TypBit 16%N) );
                                                              ( {| stags := NoInfo;
                                                                   str := "nhop_ipv4" |},
                                                                (TypBit 32%N) );
                                                              ( {| stags := NoInfo;
                                                                   str := "if_ipv4_addr" |},
                                                                (TypBit 32%N) );
                                                              ( {| stags := NoInfo;
                                                                   str := "if_mac_addr" |},
                                                                (TypBit 48%N) );
                                                              ( {| stags := NoInfo;
                                                                   str := "is_ext_if" |},
                                                                (TypBit 1%N) );
                                                              ( {| stags := NoInfo;
                                                                   str := "tcpLength" |},
                                                                (TypBit 16%N) );
                                                              ( {| stags := NoInfo;
                                                                   str := "if_index" |},
                                                                (TypBit 8%N) );
                                                              ( {| stags := NoInfo;
                                                                   str := "init_egress_spec" |},
                                                                (TypBit 9%N) )])
                                                            Directionless)
                                                       {| stags := NoInfo;
                                                          str := "if_index" |})
                                                  (TypBit 8%N) Directionless))
                                        StmUnit) (BlockEmpty NoInfo)))))));
     (DeclTable NoInfo {| stags := NoInfo; str := "send_frame" |}
          [(MkTableKey NoInfo
                (MkExpression NoInfo
                     (ExpExpressionMember
                          (MkExpression NoInfo
                               (ExpName
                                (BareName
                                 {| stags := NoInfo;
                                    str := "standard_metadata" |}) NoLocator)
                               (TypTypeName (
                                 {| stags := NoInfo;
                                    str := "standard_metadata_t" |})) InOut)
                          {| stags := NoInfo; str := "egress_port" |})
                     (TypBit 9%N) Directionless)
                {| stags := NoInfo; str := "exact" |})]
          [(MkTableActionRef NoInfo
                (MkTablePreActionRef
                     (BareName {| stags := NoInfo; str := "do_rewrites" |})
                     nil)
                (TypAction nil
                     [(MkParameter false Directionless (TypBit 48%N) 
                           None {| stags := NoInfo; str := "smac" |})]));
           (MkTableActionRef NoInfo
                (MkTablePreActionRef
                     (BareName {| stags := NoInfo; str := "_drop" |}) nil)
                (TypAction nil nil))] None None (Some 256%N) nil);
     (DeclTable NoInfo {| stags := NoInfo; str := "send_to_cpu" |} nil
          [(MkTableActionRef NoInfo
                (MkTablePreActionRef
                     (BareName {| stags := NoInfo; str := "do_cpu_encap" |})
                     nil) (TypAction nil nil))] None None None nil)]
    (BlockCons
         (MkStatement NoInfo
              (StatConditional
                   (MkExpression NoInfo
                        (ExpBinaryOp Eq
                                     (MkExpression NoInfo
                                    (ExpExpressionMember
                                         (MkExpression NoInfo
                                              (ExpName
                                               (BareName
                                                {| stags := NoInfo;
                                                   str := "standard_metadata" |})
                                               NoLocator)
                                              (TypTypeName (
                                                {| stags := NoInfo;
                                                   str := "standard_metadata_t" |}))
                                              InOut)
                                         {| stags := NoInfo;
                                            str := "instance_type" |})
                                    (TypBit 32%N) Directionless)
                               (MkExpression NoInfo
                                    (ExpInt
                                     {| itags := NoInfo; value := 0;
                                        width_signed := (Some
                                                         ( 32%N, false )) |})
                                    (TypBit 32%N) Directionless)) TypBool
                        Directionless)
                   (MkStatement NoInfo
                        (StatBlock
                         (BlockCons
                              (MkStatement NoInfo
                                   (StatMethodCall
                                        (MkExpression NoInfo
                                             (ExpExpressionMember
                                                  (MkExpression NoInfo
                                                       (ExpName
                                                        (BareName
                                                         {| stags := NoInfo;
                                                            str := "send_frame" |})
                                                        NoLocator)
                                                       (TypTable
                                                        {| stags := NoInfo;
                                                           str := "apply_result_send_frame" |})
                                                       Directionless)
                                                  {| stags := NoInfo;
                                                     str := "apply" |})
                                             (TypFunction
                                              (MkFunctionType nil nil
                                                   FunTable
                                                   (TypTypeName (
                                                     {| stags := NoInfo;
                                                        str := "apply_result_send_frame" |}))))
                                             Directionless) nil nil) StmUnit)
                              (BlockEmpty NoInfo))) StmUnit)
                   (Some
                    (MkStatement NoInfo
                         (StatBlock
                          (BlockCons
                               (MkStatement NoInfo
                                    (StatMethodCall
                                         (MkExpression NoInfo
                                              (ExpExpressionMember
                                                   (MkExpression NoInfo
                                                        (ExpName
                                                         (BareName
                                                          {| stags := NoInfo;
                                                             str := "send_to_cpu" |})
                                                         NoLocator)
                                                        (TypTable
                                                         {| stags := NoInfo;
                                                            str := "apply_result_send_to_cpu" |})
                                                        Directionless)
                                                   {| stags := NoInfo;
                                                      str := "apply" |})
                                              (TypFunction
                                               (MkFunctionType nil nil
                                                    FunTable
                                                    (TypTypeName (
                                                      {| stags := NoInfo;
                                                         str := "apply_result_send_to_cpu" |}))))
                                              Directionless) nil nil)
                                    StmUnit) (BlockEmpty NoInfo))) StmUnit)))
              StmUnit)
         (BlockCons
              (MkStatement NoInfo
                   (StatMethodCall
                        (MkExpression NoInfo
                             (ExpName
                              (BareName
                               {| stags := NoInfo; str := "assert" |})
                              NoLocator)
                             (TypFunction
                              (MkFunctionType nil
                                   [(MkParameter false In TypBool None
                                         {| stags := NoInfo;
                                            str := "check" |})] FunExtern
                                   TypVoid)) Directionless) nil
                        [Some
                          (MkExpression NoInfo
                                        (ExpBinaryOp NotEq
                                                     (MkExpression NoInfo
                                           (ExpExpressionMember
                                                (MkExpression NoInfo
                                                     (ExpName
                                                      (BareName
                                                       {| stags := NoInfo;
                                                          str := "standard_metadata" |})
                                                      NoLocator)
                                                     (TypTypeName (
                                                       {| stags := NoInfo;
                                                          str := "standard_metadata_t" |}))
                                                     InOut)
                                                {| stags := NoInfo;
                                                   str := "egress_spec" |})
                                           (TypBit 9%N) Directionless)
                                      (MkExpression NoInfo
                                           (ExpExpressionMember
                                                (MkExpression NoInfo
                                                     (ExpExpressionMember
                                                          (MkExpression
                                                               NoInfo
                                                               (ExpName
                                                                (BareName
                                                                 {| stags := NoInfo;
                                                                    str := "meta" |})
                                                                NoLocator)
                                                               (TypTypeName (
                                                                 {| stags := NoInfo;
                                                                    str := "metadata" |}))
                                                               InOut)
                                                          {| stags := NoInfo;
                                                             str := "meta" |})
                                                     (TypStruct
                                                      [( {| stags := NoInfo;
                                                            str := "do_forward" |},
                                                         (TypBit 1%N) );
                                                       ( {| stags := NoInfo;
                                                            str := "ipv4_sa" |},
                                                         (TypBit 32%N) );
                                                       ( {| stags := NoInfo;
                                                            str := "ipv4_da" |},
                                                         (TypBit 32%N) );
                                                       ( {| stags := NoInfo;
                                                            str := "tcp_sp" |},
                                                         (TypBit 16%N) );
                                                       ( {| stags := NoInfo;
                                                            str := "tcp_dp" |},
                                                         (TypBit 16%N) );
                                                       ( {| stags := NoInfo;
                                                            str := "nhop_ipv4" |},
                                                         (TypBit 32%N) );
                                                       ( {| stags := NoInfo;
                                                            str := "if_ipv4_addr" |},
                                                         (TypBit 32%N) );
                                                       ( {| stags := NoInfo;
                                                            str := "if_mac_addr" |},
                                                         (TypBit 48%N) );
                                                       ( {| stags := NoInfo;
                                                            str := "is_ext_if" |},
                                                         (TypBit 1%N) );
                                                       ( {| stags := NoInfo;
                                                            str := "tcpLength" |},
                                                         (TypBit 16%N) );
                                                       ( {| stags := NoInfo;
                                                            str := "if_index" |},
                                                         (TypBit 8%N) );
                                                       ( {| stags := NoInfo;
                                                            str := "init_egress_spec" |},
                                                         (TypBit 9%N) )])
                                                     Directionless)
                                                {| stags := NoInfo;
                                                   str := "init_egress_spec" |})
                                           (TypBit 9%N) Directionless))
                                      TypBool Directionless)]) StmUnit)
              (BlockEmpty NoInfo))).

Definition ingress := DeclControl NoInfo
    {| stags := NoInfo; str := "ingress" |} nil
    [(MkParameter false InOut
          (TypTypeName ( {| stags := NoInfo; str := "headers" |}))
          None {| stags := NoInfo; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName ( {| stags := NoInfo; str := "metadata" |}))
          None {| stags := NoInfo; str := "meta" |});
     (MkParameter false InOut
          (TypTypeName ( {| stags := NoInfo; str := "standard_metadata_t" |}))
          None {| stags := NoInfo; str := "standard_metadata" |})] nil
    [(DeclAction NoInfo {| stags := NoInfo; str := "set_dmac" |} nil
          [(MkParameter false Directionless (TypBit 48%N) None
                {| stags := NoInfo; str := "dmac" |})]
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
                                                  (TypTypeName (
                                                    {| stags := NoInfo;
                                                       str := "headers" |}))
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
                              (TypBit 48%N) Directionless)
                         (MkExpression NoInfo
                              (ExpName
                               (BareName
                                {| stags := NoInfo; str := "dmac" |})
                               NoLocator) (TypBit 48%N) In)) StmUnit)
               (BlockEmpty NoInfo)));
     (DeclAction NoInfo {| stags := NoInfo; str := "_drop" |} nil nil
          (BlockCons
               (MkStatement NoInfo
                    (StatMethodCall
                         (MkExpression NoInfo
                              (ExpName
                               (BareName
                                {| stags := NoInfo; str := "mark_to_drop" |})
                               NoLocator)
                              (TypFunction
                               (MkFunctionType nil
                                    [(MkParameter false InOut
                                          (TypTypeName (
                                            {| stags := NoInfo;
                                               str := "standard_metadata_t" |}))
                                          None
                                          {| stags := NoInfo;
                                             str := "standard_metadata" |})]
                                    FunExtern TypVoid)) Directionless) nil
                         [(Some
                           (MkExpression NoInfo
                                (ExpName
                                 (BareName
                                  {| stags := NoInfo;
                                     str := "standard_metadata" |})
                                 NoLocator)
                                (TypTypeName (
                                  {| stags := NoInfo;
                                     str := "standard_metadata_t" |})) InOut))])
                    StmUnit) (BlockEmpty NoInfo)));
     (DeclAction NoInfo {| stags := NoInfo; str := "set_if_info" |} nil
          [(MkParameter false Directionless (TypBit 32%N) None
                {| stags := NoInfo; str := "ipv4_addr" |});
           (MkParameter false Directionless (TypBit 48%N) None
                {| stags := NoInfo; str := "mac_addr" |});
           (MkParameter false Directionless (TypBit 1%N) None
                {| stags := NoInfo; str := "is_ext" |})]
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
                                                       str := "meta" |})
                                                   NoLocator)
                                                  (TypTypeName (
                                                    {| stags := NoInfo;
                                                       str := "metadata" |}))
                                                  InOut)
                                             {| stags := NoInfo;
                                                str := "meta" |})
                                        (TypStruct
                                         [( {| stags := NoInfo;
                                               str := "do_forward" |},
                                            (TypBit 1%N) );
                                          ( {| stags := NoInfo;
                                               str := "ipv4_sa" |},
                                            (TypBit 32%N) );
                                          ( {| stags := NoInfo;
                                               str := "ipv4_da" |},
                                            (TypBit 32%N) );
                                          ( {| stags := NoInfo;
                                               str := "tcp_sp" |},
                                            (TypBit 16%N) );
                                          ( {| stags := NoInfo;
                                               str := "tcp_dp" |},
                                            (TypBit 16%N) );
                                          ( {| stags := NoInfo;
                                               str := "nhop_ipv4" |},
                                            (TypBit 32%N) );
                                          ( {| stags := NoInfo;
                                               str := "if_ipv4_addr" |},
                                            (TypBit 32%N) );
                                          ( {| stags := NoInfo;
                                               str := "if_mac_addr" |},
                                            (TypBit 48%N) );
                                          ( {| stags := NoInfo;
                                               str := "is_ext_if" |},
                                            (TypBit 1%N) );
                                          ( {| stags := NoInfo;
                                               str := "tcpLength" |},
                                            (TypBit 16%N) );
                                          ( {| stags := NoInfo;
                                               str := "if_index" |},
                                            (TypBit 8%N) );
                                          ( {| stags := NoInfo;
                                               str := "init_egress_spec" |},
                                            (TypBit 9%N) )]) Directionless)
                                   {| stags := NoInfo;
                                      str := "if_ipv4_addr" |}) (TypBit 32%N)
                              Directionless)
                         (MkExpression NoInfo
                              (ExpName
                               (BareName
                                {| stags := NoInfo; str := "ipv4_addr" |})
                               NoLocator) (TypBit 32%N) In)) StmUnit)
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
                                                            str := "meta" |})
                                                        NoLocator)
                                                       (TypTypeName (
                                                         {| stags := NoInfo;
                                                            str := "metadata" |}))
                                                       InOut)
                                                  {| stags := NoInfo;
                                                     str := "meta" |})
                                             (TypStruct
                                              [( {| stags := NoInfo;
                                                    str := "do_forward" |},
                                                 (TypBit 1%N) );
                                               ( {| stags := NoInfo;
                                                    str := "ipv4_sa" |},
                                                 (TypBit 32%N) );
                                               ( {| stags := NoInfo;
                                                    str := "ipv4_da" |},
                                                 (TypBit 32%N) );
                                               ( {| stags := NoInfo;
                                                    str := "tcp_sp" |},
                                                 (TypBit 16%N) );
                                               ( {| stags := NoInfo;
                                                    str := "tcp_dp" |},
                                                 (TypBit 16%N) );
                                               ( {| stags := NoInfo;
                                                    str := "nhop_ipv4" |},
                                                 (TypBit 32%N) );
                                               ( {| stags := NoInfo;
                                                    str := "if_ipv4_addr" |},
                                                 (TypBit 32%N) );
                                               ( {| stags := NoInfo;
                                                    str := "if_mac_addr" |},
                                                 (TypBit 48%N) );
                                               ( {| stags := NoInfo;
                                                    str := "is_ext_if" |},
                                                 (TypBit 1%N) );
                                               ( {| stags := NoInfo;
                                                    str := "tcpLength" |},
                                                 (TypBit 16%N) );
                                               ( {| stags := NoInfo;
                                                    str := "if_index" |},
                                                 (TypBit 8%N) );
                                               ( {| stags := NoInfo;
                                                    str := "init_egress_spec" |},
                                                 (TypBit 9%N) )])
                                             Directionless)
                                        {| stags := NoInfo;
                                           str := "if_mac_addr" |})
                                   (TypBit 48%N) Directionless)
                              (MkExpression NoInfo
                                   (ExpName
                                    (BareName
                                     {| stags := NoInfo; str := "mac_addr" |})
                                    NoLocator) (TypBit 48%N) In)) StmUnit)
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
                                                                 str := "meta" |})
                                                             NoLocator)
                                                            (TypTypeName (
                                                              {| stags := NoInfo;
                                                                 str := "metadata" |}))
                                                            InOut)
                                                       {| stags := NoInfo;
                                                          str := "meta" |})
                                                  (TypStruct
                                                   [( {| stags := NoInfo;
                                                         str := "do_forward" |},
                                                      (TypBit 1%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "ipv4_sa" |},
                                                      (TypBit 32%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "ipv4_da" |},
                                                      (TypBit 32%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "tcp_sp" |},
                                                      (TypBit 16%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "tcp_dp" |},
                                                      (TypBit 16%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "nhop_ipv4" |},
                                                      (TypBit 32%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "if_ipv4_addr" |},
                                                      (TypBit 32%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "if_mac_addr" |},
                                                      (TypBit 48%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "is_ext_if" |},
                                                      (TypBit 1%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "tcpLength" |},
                                                      (TypBit 16%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "if_index" |},
                                                      (TypBit 8%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "init_egress_spec" |},
                                                      (TypBit 9%N) )])
                                                  Directionless)
                                             {| stags := NoInfo;
                                                str := "is_ext_if" |})
                                        (TypBit 1%N) Directionless)
                                   (MkExpression NoInfo
                                        (ExpName
                                         (BareName
                                          {| stags := NoInfo;
                                             str := "is_ext" |}) NoLocator)
                                        (TypBit 1%N) In)) StmUnit)
                         (BlockEmpty NoInfo)))));
     (DeclAction NoInfo {| stags := NoInfo; str := "set_nhop" |} nil
          [(MkParameter false Directionless (TypBit 32%N) None
                {| stags := NoInfo; str := "nhop_ipv4" |});
           (MkParameter false Directionless (TypBit 9%N) None
                {| stags := NoInfo; str := "port" |})]
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
                                                       str := "meta" |})
                                                   NoLocator)
                                                  (TypTypeName (
                                                    {| stags := NoInfo;
                                                       str := "metadata" |}))
                                                  InOut)
                                             {| stags := NoInfo;
                                                str := "meta" |})
                                        (TypStruct
                                         [( {| stags := NoInfo;
                                               str := "do_forward" |},
                                            (TypBit 1%N) );
                                          ( {| stags := NoInfo;
                                               str := "ipv4_sa" |},
                                            (TypBit 32%N) );
                                          ( {| stags := NoInfo;
                                               str := "ipv4_da" |},
                                            (TypBit 32%N) );
                                          ( {| stags := NoInfo;
                                               str := "tcp_sp" |},
                                            (TypBit 16%N) );
                                          ( {| stags := NoInfo;
                                               str := "tcp_dp" |},
                                            (TypBit 16%N) );
                                          ( {| stags := NoInfo;
                                               str := "nhop_ipv4" |},
                                            (TypBit 32%N) );
                                          ( {| stags := NoInfo;
                                               str := "if_ipv4_addr" |},
                                            (TypBit 32%N) );
                                          ( {| stags := NoInfo;
                                               str := "if_mac_addr" |},
                                            (TypBit 48%N) );
                                          ( {| stags := NoInfo;
                                               str := "is_ext_if" |},
                                            (TypBit 1%N) );
                                          ( {| stags := NoInfo;
                                               str := "tcpLength" |},
                                            (TypBit 16%N) );
                                          ( {| stags := NoInfo;
                                               str := "if_index" |},
                                            (TypBit 8%N) );
                                          ( {| stags := NoInfo;
                                               str := "init_egress_spec" |},
                                            (TypBit 9%N) )]) Directionless)
                                   {| stags := NoInfo; str := "nhop_ipv4" |})
                              (TypBit 32%N) Directionless)
                         (MkExpression NoInfo
                              (ExpName
                               (BareName
                                {| stags := NoInfo; str := "nhop_ipv4" |})
                               NoLocator) (TypBit 32%N) In)) StmUnit)
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
                                             (TypTypeName (
                                               {| stags := NoInfo;
                                                  str := "standard_metadata_t" |}))
                                             InOut)
                                        {| stags := NoInfo;
                                           str := "egress_spec" |})
                                   (TypBit 9%N) Directionless)
                              (MkExpression NoInfo
                                   (ExpName
                                    (BareName
                                     {| stags := NoInfo; str := "port" |})
                                    NoLocator) (TypBit 9%N) In)) StmUnit)
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
                                                            (TypTypeName (
                                                              {| stags := NoInfo;
                                                                 str := "headers" |}))
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
                                                str := "ttl" |}) (TypBit 8%N)
                                        Directionless)
                                   (MkExpression NoInfo
                                        (ExpBinaryOp Minus
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
                                                                    (TypTypeName (
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "headers" |}))
                                                                    InOut)
                                                                   {| 
                                                                   stags := NoInfo;
                                                                   str := "ipv4" |})
                                                              (TypHeader
                                                               [( {| 
                                                                  stags := NoInfo;
                                                                  str := "version" |},
                                                                  (TypBit
                                                                   4%N) );
                                                                ( {| 
                                                                  stags := NoInfo;
                                                                  str := "ihl" |},
                                                                  (TypBit
                                                                   4%N) );
                                                                ( {| 
                                                                  stags := NoInfo;
                                                                  str := "diffserv" |},
                                                                  (TypBit
                                                                   8%N) );
                                                                ( {| 
                                                                  stags := NoInfo;
                                                                  str := "totalLen" |},
                                                                  (TypBit
                                                                   16%N) );
                                                                ( {| 
                                                                  stags := NoInfo;
                                                                  str := "identification" |},
                                                                  (TypBit
                                                                   16%N) );
                                                                ( {| 
                                                                  stags := NoInfo;
                                                                  str := "flags" |},
                                                                  (TypBit
                                                                   3%N) );
                                                                ( {| 
                                                                  stags := NoInfo;
                                                                  str := "fragOffset" |},
                                                                  (TypBit
                                                                   13%N) );
                                                                ( {| 
                                                                  stags := NoInfo;
                                                                  str := "ttl" |},
                                                                  (TypBit
                                                                   8%N) );
                                                                ( {| 
                                                                  stags := NoInfo;
                                                                  str := "protocol" |},
                                                                  (TypBit
                                                                   8%N) );
                                                                ( {| 
                                                                  stags := NoInfo;
                                                                  str := "hdrChecksum" |},
                                                                  (TypBit
                                                                   16%N) );
                                                                ( {| 
                                                                  stags := NoInfo;
                                                                  str := "srcAddr" |},
                                                                  (TypBit
                                                                   32%N) );
                                                                ( {| 
                                                                  stags := NoInfo;
                                                                  str := "dstAddr" |},
                                                                  (TypBit
                                                                   32%N) )])
                                                              Directionless)
                                                         {| stags := NoInfo;
                                                            str := "ttl" |})
                                                    (TypBit 8%N)
                                                    Directionless)
                                               (MkExpression NoInfo
                                                    (ExpInt
                                                     {| itags := NoInfo;
                                                        value := 1;
                                                        width_signed := (
                                                        Some ( 8%N, false )) |})
                                                    (TypBit 8%N)
                                                    Directionless) )
                                        (TypBit 8%N) Directionless)) StmUnit)
                         (BlockEmpty NoInfo)))));
     (DeclAction NoInfo {| stags := NoInfo; str := "nat_miss_int_to_ext" |}
          nil nil
          (BlockCons
               (MkStatement NoInfo
                    (StatMethodCall
                         (MkExpression NoInfo
                              (ExpName
                               (BareName
                                {| stags := NoInfo; str := "clone3" |})
                               NoLocator)
                              (TypFunction
                               (MkFunctionType
                                    [{| stags := NoInfo; str := "T20" |}]
                                    [(MkParameter false In
                                          (TypTypeName (
                                            {| stags := NoInfo;
                                               str := "CloneType" |})) 
                                          None
                                          {| stags := NoInfo;
                                             str := "type" |});
                                     (MkParameter false In (TypBit 32%N) 
                                          None
                                          {| stags := NoInfo;
                                             str := "session" |});
                                     (MkParameter false In
                                          (TypTypeName (
                                            {| stags := NoInfo;
                                               str := "T20" |})) None
                                          {| stags := NoInfo;
                                             str := "data" |})] FunExtern
                                    TypVoid)) Directionless)
                         [(TypList
                           [(TypStruct
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
                              ( {| stags := NoInfo;
                                   str := "checksum_error" |}, (TypBit 1%N) );
                              ( {| stags := NoInfo; str := "parser_error" |},
                                TypError );
                              ( {| stags := NoInfo; str := "priority" |},
                                (TypBit 3%N) )])])]
                         [(Some
                           (MkExpression NoInfo
                                (ExpTypeMember (
                                      {| stags := NoInfo;
                                         str := "CloneType" |})
                                     {| stags := NoInfo; str := "I2E" |})
                                (TypEnum
                                     {| stags := NoInfo;
                                        str := "CloneType" |} None
                                     [{| stags := NoInfo; str := "I2E" |};
                                      {| stags := NoInfo; str := "E2E" |}])
                                Directionless));
                          (Some
                           (MkExpression NoInfo
                                (ExpCast (TypBit 32%N)
                                     (MkExpression NoInfo
                                          (ExpInt
                                           {| itags := NoInfo; value := 250;
                                              width_signed := (Some
                                                               ( 32%N,
                                                                 false )) |})
                                          (TypBit 32%N) Directionless))
                                (TypBit 32%N) Directionless));
                          (Some
                           (MkExpression NoInfo
                                (ExpList
                                 [(MkExpression NoInfo
                                       (ExpName
                                        (BareName
                                         {| stags := NoInfo;
                                            str := "standard_metadata" |})
                                        NoLocator)
                                       (TypTypeName (
                                         {| stags := NoInfo;
                                            str := "standard_metadata_t" |}))
                                       InOut)])
                                (TypList
                                 [(TypStruct
                                   [( {| stags := NoInfo;
                                         str := "ingress_port" |},
                                      (TypBit 9%N) );
                                    ( {| stags := NoInfo;
                                         str := "egress_spec" |},
                                      (TypBit 9%N) );
                                    ( {| stags := NoInfo;
                                         str := "egress_port" |},
                                      (TypBit 9%N) );
                                    ( {| stags := NoInfo;
                                         str := "instance_type" |},
                                      (TypBit 32%N) );
                                    ( {| stags := NoInfo;
                                         str := "packet_length" |},
                                      (TypBit 32%N) );
                                    ( {| stags := NoInfo;
                                         str := "enq_timestamp" |},
                                      (TypBit 32%N) );
                                    ( {| stags := NoInfo;
                                         str := "enq_qdepth" |},
                                      (TypBit 19%N) );
                                    ( {| stags := NoInfo;
                                         str := "deq_timedelta" |},
                                      (TypBit 32%N) );
                                    ( {| stags := NoInfo;
                                         str := "deq_qdepth" |},
                                      (TypBit 19%N) );
                                    ( {| stags := NoInfo;
                                         str := "ingress_global_timestamp" |},
                                      (TypBit 48%N) );
                                    ( {| stags := NoInfo;
                                         str := "egress_global_timestamp" |},
                                      (TypBit 48%N) );
                                    ( {| stags := NoInfo;
                                         str := "mcast_grp" |},
                                      (TypBit 16%N) );
                                    ( {| stags := NoInfo;
                                         str := "egress_rid" |},
                                      (TypBit 16%N) );
                                    ( {| stags := NoInfo;
                                         str := "checksum_error" |},
                                      (TypBit 1%N) );
                                    ( {| stags := NoInfo;
                                         str := "parser_error" |}, TypError );
                                    ( {| stags := NoInfo;
                                         str := "priority" |}, (TypBit 3%N) )])])
                                Directionless))]) StmUnit)
               (BlockEmpty NoInfo)));
     (DeclAction NoInfo {| stags := NoInfo; str := "nat_miss_ext_to_int" |}
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
                                                       str := "meta" |})
                                                   NoLocator)
                                                  (TypTypeName (
                                                    {| stags := NoInfo;
                                                       str := "metadata" |}))
                                                  InOut)
                                             {| stags := NoInfo;
                                                str := "meta" |})
                                        (TypStruct
                                         [( {| stags := NoInfo;
                                               str := "do_forward" |},
                                            (TypBit 1%N) );
                                          ( {| stags := NoInfo;
                                               str := "ipv4_sa" |},
                                            (TypBit 32%N) );
                                          ( {| stags := NoInfo;
                                               str := "ipv4_da" |},
                                            (TypBit 32%N) );
                                          ( {| stags := NoInfo;
                                               str := "tcp_sp" |},
                                            (TypBit 16%N) );
                                          ( {| stags := NoInfo;
                                               str := "tcp_dp" |},
                                            (TypBit 16%N) );
                                          ( {| stags := NoInfo;
                                               str := "nhop_ipv4" |},
                                            (TypBit 32%N) );
                                          ( {| stags := NoInfo;
                                               str := "if_ipv4_addr" |},
                                            (TypBit 32%N) );
                                          ( {| stags := NoInfo;
                                               str := "if_mac_addr" |},
                                            (TypBit 48%N) );
                                          ( {| stags := NoInfo;
                                               str := "is_ext_if" |},
                                            (TypBit 1%N) );
                                          ( {| stags := NoInfo;
                                               str := "tcpLength" |},
                                            (TypBit 16%N) );
                                          ( {| stags := NoInfo;
                                               str := "if_index" |},
                                            (TypBit 8%N) );
                                          ( {| stags := NoInfo;
                                               str := "init_egress_spec" |},
                                            (TypBit 9%N) )]) Directionless)
                                   {| stags := NoInfo; str := "do_forward" |})
                              (TypBit 1%N) Directionless)
                         (MkExpression NoInfo
                              (ExpInt
                               {| itags := NoInfo; value := 0;
                                  width_signed := (Some ( 1%N, false )) |})
                              (TypBit 1%N) Directionless)) StmUnit)
               (BlockCons
                    (MkStatement NoInfo
                         (StatMethodCall
                              (MkExpression NoInfo
                                   (ExpName
                                    (BareName
                                     {| stags := NoInfo;
                                        str := "mark_to_drop" |}) NoLocator)
                                   (TypFunction
                                    (MkFunctionType nil
                                         [(MkParameter false InOut
                                               (TypTypeName (
                                                 {| stags := NoInfo;
                                                    str := "standard_metadata_t" |}))
                                               None
                                               {| stags := NoInfo;
                                                  str := "standard_metadata" |})]
                                         FunExtern TypVoid)) Directionless)
                              nil
                              [(Some
                                (MkExpression NoInfo
                                     (ExpName
                                      (BareName
                                       {| stags := NoInfo;
                                          str := "standard_metadata" |})
                                      NoLocator)
                                     (TypTypeName (
                                       {| stags := NoInfo;
                                          str := "standard_metadata_t" |}))
                                     InOut))]) StmUnit) (BlockEmpty NoInfo))));
     (DeclAction NoInfo {| stags := NoInfo; str := "nat_hit_int_to_ext" |}
          nil
          [(MkParameter false Directionless (TypBit 32%N) None
                {| stags := NoInfo; str := "srcAddr" |});
           (MkParameter false Directionless (TypBit 16%N) None
                {| stags := NoInfo; str := "srcPort" |})]
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
                                                       str := "meta" |})
                                                   NoLocator)
                                                  (TypTypeName (
                                                    {| stags := NoInfo;
                                                       str := "metadata" |}))
                                                  InOut)
                                             {| stags := NoInfo;
                                                str := "meta" |})
                                        (TypStruct
                                         [( {| stags := NoInfo;
                                               str := "do_forward" |},
                                            (TypBit 1%N) );
                                          ( {| stags := NoInfo;
                                               str := "ipv4_sa" |},
                                            (TypBit 32%N) );
                                          ( {| stags := NoInfo;
                                               str := "ipv4_da" |},
                                            (TypBit 32%N) );
                                          ( {| stags := NoInfo;
                                               str := "tcp_sp" |},
                                            (TypBit 16%N) );
                                          ( {| stags := NoInfo;
                                               str := "tcp_dp" |},
                                            (TypBit 16%N) );
                                          ( {| stags := NoInfo;
                                               str := "nhop_ipv4" |},
                                            (TypBit 32%N) );
                                          ( {| stags := NoInfo;
                                               str := "if_ipv4_addr" |},
                                            (TypBit 32%N) );
                                          ( {| stags := NoInfo;
                                               str := "if_mac_addr" |},
                                            (TypBit 48%N) );
                                          ( {| stags := NoInfo;
                                               str := "is_ext_if" |},
                                            (TypBit 1%N) );
                                          ( {| stags := NoInfo;
                                               str := "tcpLength" |},
                                            (TypBit 16%N) );
                                          ( {| stags := NoInfo;
                                               str := "if_index" |},
                                            (TypBit 8%N) );
                                          ( {| stags := NoInfo;
                                               str := "init_egress_spec" |},
                                            (TypBit 9%N) )]) Directionless)
                                   {| stags := NoInfo; str := "do_forward" |})
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
                                             (ExpExpressionMember
                                                  (MkExpression NoInfo
                                                       (ExpName
                                                        (BareName
                                                         {| stags := NoInfo;
                                                            str := "meta" |})
                                                        NoLocator)
                                                       (TypTypeName (
                                                         {| stags := NoInfo;
                                                            str := "metadata" |}))
                                                       InOut)
                                                  {| stags := NoInfo;
                                                     str := "meta" |})
                                             (TypStruct
                                              [( {| stags := NoInfo;
                                                    str := "do_forward" |},
                                                 (TypBit 1%N) );
                                               ( {| stags := NoInfo;
                                                    str := "ipv4_sa" |},
                                                 (TypBit 32%N) );
                                               ( {| stags := NoInfo;
                                                    str := "ipv4_da" |},
                                                 (TypBit 32%N) );
                                               ( {| stags := NoInfo;
                                                    str := "tcp_sp" |},
                                                 (TypBit 16%N) );
                                               ( {| stags := NoInfo;
                                                    str := "tcp_dp" |},
                                                 (TypBit 16%N) );
                                               ( {| stags := NoInfo;
                                                    str := "nhop_ipv4" |},
                                                 (TypBit 32%N) );
                                               ( {| stags := NoInfo;
                                                    str := "if_ipv4_addr" |},
                                                 (TypBit 32%N) );
                                               ( {| stags := NoInfo;
                                                    str := "if_mac_addr" |},
                                                 (TypBit 48%N) );
                                               ( {| stags := NoInfo;
                                                    str := "is_ext_if" |},
                                                 (TypBit 1%N) );
                                               ( {| stags := NoInfo;
                                                    str := "tcpLength" |},
                                                 (TypBit 16%N) );
                                               ( {| stags := NoInfo;
                                                    str := "if_index" |},
                                                 (TypBit 8%N) );
                                               ( {| stags := NoInfo;
                                                    str := "init_egress_spec" |},
                                                 (TypBit 9%N) )])
                                             Directionless)
                                        {| stags := NoInfo;
                                           str := "ipv4_sa" |}) (TypBit 32%N)
                                   Directionless)
                              (MkExpression NoInfo
                                   (ExpName
                                    (BareName
                                     {| stags := NoInfo; str := "srcAddr" |})
                                    NoLocator) (TypBit 32%N) In)) StmUnit)
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
                                                                 str := "meta" |})
                                                             NoLocator)
                                                            (TypTypeName (
                                                              {| stags := NoInfo;
                                                                 str := "metadata" |}))
                                                            InOut)
                                                       {| stags := NoInfo;
                                                          str := "meta" |})
                                                  (TypStruct
                                                   [( {| stags := NoInfo;
                                                         str := "do_forward" |},
                                                      (TypBit 1%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "ipv4_sa" |},
                                                      (TypBit 32%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "ipv4_da" |},
                                                      (TypBit 32%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "tcp_sp" |},
                                                      (TypBit 16%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "tcp_dp" |},
                                                      (TypBit 16%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "nhop_ipv4" |},
                                                      (TypBit 32%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "if_ipv4_addr" |},
                                                      (TypBit 32%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "if_mac_addr" |},
                                                      (TypBit 48%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "is_ext_if" |},
                                                      (TypBit 1%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "tcpLength" |},
                                                      (TypBit 16%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "if_index" |},
                                                      (TypBit 8%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "init_egress_spec" |},
                                                      (TypBit 9%N) )])
                                                  Directionless)
                                             {| stags := NoInfo;
                                                str := "tcp_sp" |})
                                        (TypBit 16%N) Directionless)
                                   (MkExpression NoInfo
                                        (ExpName
                                         (BareName
                                          {| stags := NoInfo;
                                             str := "srcPort" |}) NoLocator)
                                        (TypBit 16%N) In)) StmUnit)
                         (BlockEmpty NoInfo)))));
     (DeclAction NoInfo {| stags := NoInfo; str := "nat_hit_ext_to_int" |}
          nil
          [(MkParameter false Directionless (TypBit 32%N) None
                {| stags := NoInfo; str := "dstAddr" |});
           (MkParameter false Directionless (TypBit 16%N) None
                {| stags := NoInfo; str := "dstPort" |})]
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
                                                       str := "meta" |})
                                                   NoLocator)
                                                  (TypTypeName (
                                                    {| stags := NoInfo;
                                                       str := "metadata" |}))
                                                  InOut)
                                             {| stags := NoInfo;
                                                str := "meta" |})
                                        (TypStruct
                                         [( {| stags := NoInfo;
                                               str := "do_forward" |},
                                            (TypBit 1%N) );
                                          ( {| stags := NoInfo;
                                               str := "ipv4_sa" |},
                                            (TypBit 32%N) );
                                          ( {| stags := NoInfo;
                                               str := "ipv4_da" |},
                                            (TypBit 32%N) );
                                          ( {| stags := NoInfo;
                                               str := "tcp_sp" |},
                                            (TypBit 16%N) );
                                          ( {| stags := NoInfo;
                                               str := "tcp_dp" |},
                                            (TypBit 16%N) );
                                          ( {| stags := NoInfo;
                                               str := "nhop_ipv4" |},
                                            (TypBit 32%N) );
                                          ( {| stags := NoInfo;
                                               str := "if_ipv4_addr" |},
                                            (TypBit 32%N) );
                                          ( {| stags := NoInfo;
                                               str := "if_mac_addr" |},
                                            (TypBit 48%N) );
                                          ( {| stags := NoInfo;
                                               str := "is_ext_if" |},
                                            (TypBit 1%N) );
                                          ( {| stags := NoInfo;
                                               str := "tcpLength" |},
                                            (TypBit 16%N) );
                                          ( {| stags := NoInfo;
                                               str := "if_index" |},
                                            (TypBit 8%N) );
                                          ( {| stags := NoInfo;
                                               str := "init_egress_spec" |},
                                            (TypBit 9%N) )]) Directionless)
                                   {| stags := NoInfo; str := "do_forward" |})
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
                                             (ExpExpressionMember
                                                  (MkExpression NoInfo
                                                       (ExpName
                                                        (BareName
                                                         {| stags := NoInfo;
                                                            str := "meta" |})
                                                        NoLocator)
                                                       (TypTypeName (
                                                         {| stags := NoInfo;
                                                            str := "metadata" |}))
                                                       InOut)
                                                  {| stags := NoInfo;
                                                     str := "meta" |})
                                             (TypStruct
                                              [( {| stags := NoInfo;
                                                    str := "do_forward" |},
                                                 (TypBit 1%N) );
                                               ( {| stags := NoInfo;
                                                    str := "ipv4_sa" |},
                                                 (TypBit 32%N) );
                                               ( {| stags := NoInfo;
                                                    str := "ipv4_da" |},
                                                 (TypBit 32%N) );
                                               ( {| stags := NoInfo;
                                                    str := "tcp_sp" |},
                                                 (TypBit 16%N) );
                                               ( {| stags := NoInfo;
                                                    str := "tcp_dp" |},
                                                 (TypBit 16%N) );
                                               ( {| stags := NoInfo;
                                                    str := "nhop_ipv4" |},
                                                 (TypBit 32%N) );
                                               ( {| stags := NoInfo;
                                                    str := "if_ipv4_addr" |},
                                                 (TypBit 32%N) );
                                               ( {| stags := NoInfo;
                                                    str := "if_mac_addr" |},
                                                 (TypBit 48%N) );
                                               ( {| stags := NoInfo;
                                                    str := "is_ext_if" |},
                                                 (TypBit 1%N) );
                                               ( {| stags := NoInfo;
                                                    str := "tcpLength" |},
                                                 (TypBit 16%N) );
                                               ( {| stags := NoInfo;
                                                    str := "if_index" |},
                                                 (TypBit 8%N) );
                                               ( {| stags := NoInfo;
                                                    str := "init_egress_spec" |},
                                                 (TypBit 9%N) )])
                                             Directionless)
                                        {| stags := NoInfo;
                                           str := "ipv4_da" |}) (TypBit 32%N)
                                   Directionless)
                              (MkExpression NoInfo
                                   (ExpName
                                    (BareName
                                     {| stags := NoInfo; str := "dstAddr" |})
                                    NoLocator) (TypBit 32%N) In)) StmUnit)
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
                                                                 str := "meta" |})
                                                             NoLocator)
                                                            (TypTypeName (
                                                              {| stags := NoInfo;
                                                                 str := "metadata" |}))
                                                            InOut)
                                                       {| stags := NoInfo;
                                                          str := "meta" |})
                                                  (TypStruct
                                                   [( {| stags := NoInfo;
                                                         str := "do_forward" |},
                                                      (TypBit 1%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "ipv4_sa" |},
                                                      (TypBit 32%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "ipv4_da" |},
                                                      (TypBit 32%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "tcp_sp" |},
                                                      (TypBit 16%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "tcp_dp" |},
                                                      (TypBit 16%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "nhop_ipv4" |},
                                                      (TypBit 32%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "if_ipv4_addr" |},
                                                      (TypBit 32%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "if_mac_addr" |},
                                                      (TypBit 48%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "is_ext_if" |},
                                                      (TypBit 1%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "tcpLength" |},
                                                      (TypBit 16%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "if_index" |},
                                                      (TypBit 8%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "init_egress_spec" |},
                                                      (TypBit 9%N) )])
                                                  Directionless)
                                             {| stags := NoInfo;
                                                str := "tcp_dp" |})
                                        (TypBit 16%N) Directionless)
                                   (MkExpression NoInfo
                                        (ExpName
                                         (BareName
                                          {| stags := NoInfo;
                                             str := "dstPort" |}) NoLocator)
                                        (TypBit 16%N) In)) StmUnit)
                         (BlockEmpty NoInfo)))));
     (DeclAction NoInfo {| stags := NoInfo; str := "nat_no_nat" |} nil nil
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
                                                       str := "meta" |})
                                                   NoLocator)
                                                  (TypTypeName (
                                                    {| stags := NoInfo;
                                                       str := "metadata" |}))
                                                  InOut)
                                             {| stags := NoInfo;
                                                str := "meta" |})
                                        (TypStruct
                                         [( {| stags := NoInfo;
                                               str := "do_forward" |},
                                            (TypBit 1%N) );
                                          ( {| stags := NoInfo;
                                               str := "ipv4_sa" |},
                                            (TypBit 32%N) );
                                          ( {| stags := NoInfo;
                                               str := "ipv4_da" |},
                                            (TypBit 32%N) );
                                          ( {| stags := NoInfo;
                                               str := "tcp_sp" |},
                                            (TypBit 16%N) );
                                          ( {| stags := NoInfo;
                                               str := "tcp_dp" |},
                                            (TypBit 16%N) );
                                          ( {| stags := NoInfo;
                                               str := "nhop_ipv4" |},
                                            (TypBit 32%N) );
                                          ( {| stags := NoInfo;
                                               str := "if_ipv4_addr" |},
                                            (TypBit 32%N) );
                                          ( {| stags := NoInfo;
                                               str := "if_mac_addr" |},
                                            (TypBit 48%N) );
                                          ( {| stags := NoInfo;
                                               str := "is_ext_if" |},
                                            (TypBit 1%N) );
                                          ( {| stags := NoInfo;
                                               str := "tcpLength" |},
                                            (TypBit 16%N) );
                                          ( {| stags := NoInfo;
                                               str := "if_index" |},
                                            (TypBit 8%N) );
                                          ( {| stags := NoInfo;
                                               str := "init_egress_spec" |},
                                            (TypBit 9%N) )]) Directionless)
                                   {| stags := NoInfo; str := "do_forward" |})
                              (TypBit 1%N) Directionless)
                         (MkExpression NoInfo
                              (ExpInt
                               {| itags := NoInfo; value := 1;
                                  width_signed := (Some ( 1%N, false )) |})
                              (TypBit 1%N) Directionless)) StmUnit)
               (BlockEmpty NoInfo)));
     (DeclTable NoInfo {| stags := NoInfo; str := "forward" |}
          [(MkTableKey NoInfo
                (MkExpression NoInfo
                     (ExpExpressionMember
                          (MkExpression NoInfo
                               (ExpExpressionMember
                                    (MkExpression NoInfo
                                         (ExpName
                                          (BareName
                                           {| stags := NoInfo;
                                              str := "meta" |}) NoLocator)
                                         (TypTypeName (
                                           {| stags := NoInfo;
                                              str := "metadata" |})) InOut)
                                    {| stags := NoInfo; str := "meta" |})
                               (TypStruct
                                [( {| stags := NoInfo; str := "do_forward" |},
                                   (TypBit 1%N) );
                                 ( {| stags := NoInfo; str := "ipv4_sa" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "ipv4_da" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "tcp_sp" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "tcp_dp" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "nhop_ipv4" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo;
                                      str := "if_ipv4_addr" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo;
                                      str := "if_mac_addr" |},
                                   (TypBit 48%N) );
                                 ( {| stags := NoInfo; str := "is_ext_if" |},
                                   (TypBit 1%N) );
                                 ( {| stags := NoInfo; str := "tcpLength" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "if_index" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo;
                                      str := "init_egress_spec" |},
                                   (TypBit 9%N) )]) Directionless)
                          {| stags := NoInfo; str := "nhop_ipv4" |})
                     (TypBit 32%N) Directionless)
                {| stags := NoInfo; str := "exact" |})]
          [(MkTableActionRef NoInfo
                (MkTablePreActionRef
                     (BareName {| stags := NoInfo; str := "set_dmac" |}) nil)
                (TypAction nil
                     [(MkParameter false Directionless (TypBit 48%N) 
                           None {| stags := NoInfo; str := "dmac" |})]));
           (MkTableActionRef NoInfo
                (MkTablePreActionRef
                     (BareName {| stags := NoInfo; str := "_drop" |}) nil)
                (TypAction nil nil))] None None (Some 512%N) nil);
     (DeclTable NoInfo {| stags := NoInfo; str := "if_info" |}
          [(MkTableKey NoInfo
                (MkExpression NoInfo
                     (ExpExpressionMember
                          (MkExpression NoInfo
                               (ExpExpressionMember
                                    (MkExpression NoInfo
                                         (ExpName
                                          (BareName
                                           {| stags := NoInfo;
                                              str := "meta" |}) NoLocator)
                                         (TypTypeName (
                                           {| stags := NoInfo;
                                              str := "metadata" |})) InOut)
                                    {| stags := NoInfo; str := "meta" |})
                               (TypStruct
                                [( {| stags := NoInfo; str := "do_forward" |},
                                   (TypBit 1%N) );
                                 ( {| stags := NoInfo; str := "ipv4_sa" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "ipv4_da" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "tcp_sp" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "tcp_dp" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "nhop_ipv4" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo;
                                      str := "if_ipv4_addr" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo;
                                      str := "if_mac_addr" |},
                                   (TypBit 48%N) );
                                 ( {| stags := NoInfo; str := "is_ext_if" |},
                                   (TypBit 1%N) );
                                 ( {| stags := NoInfo; str := "tcpLength" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "if_index" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo;
                                      str := "init_egress_spec" |},
                                   (TypBit 9%N) )]) Directionless)
                          {| stags := NoInfo; str := "if_index" |})
                     (TypBit 8%N) Directionless)
                {| stags := NoInfo; str := "exact" |})]
          [(MkTableActionRef NoInfo
                (MkTablePreActionRef
                     (BareName {| stags := NoInfo; str := "_drop" |}) nil)
                (TypAction nil nil));
           (MkTableActionRef NoInfo
                (MkTablePreActionRef
                     (BareName {| stags := NoInfo; str := "set_if_info" |})
                     nil)
                (TypAction nil
                     [(MkParameter false Directionless (TypBit 32%N) 
                           None {| stags := NoInfo; str := "ipv4_addr" |});
                      (MkParameter false Directionless (TypBit 48%N) 
                           None {| stags := NoInfo; str := "mac_addr" |});
                      (MkParameter false Directionless (TypBit 1%N) None
                           {| stags := NoInfo; str := "is_ext" |})]))] 
          None None None nil);
     (DeclTable NoInfo {| stags := NoInfo; str := "ipv4_lpm" |}
          [(MkTableKey NoInfo
                (MkExpression NoInfo
                     (ExpExpressionMember
                          (MkExpression NoInfo
                               (ExpExpressionMember
                                    (MkExpression NoInfo
                                         (ExpName
                                          (BareName
                                           {| stags := NoInfo;
                                              str := "meta" |}) NoLocator)
                                         (TypTypeName (
                                           {| stags := NoInfo;
                                              str := "metadata" |})) InOut)
                                    {| stags := NoInfo; str := "meta" |})
                               (TypStruct
                                [( {| stags := NoInfo; str := "do_forward" |},
                                   (TypBit 1%N) );
                                 ( {| stags := NoInfo; str := "ipv4_sa" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "ipv4_da" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "tcp_sp" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "tcp_dp" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "nhop_ipv4" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo;
                                      str := "if_ipv4_addr" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo;
                                      str := "if_mac_addr" |},
                                   (TypBit 48%N) );
                                 ( {| stags := NoInfo; str := "is_ext_if" |},
                                   (TypBit 1%N) );
                                 ( {| stags := NoInfo; str := "tcpLength" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "if_index" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo;
                                      str := "init_egress_spec" |},
                                   (TypBit 9%N) )]) Directionless)
                          {| stags := NoInfo; str := "ipv4_da" |})
                     (TypBit 32%N) Directionless)
                {| stags := NoInfo; str := "lpm" |})]
          [(MkTableActionRef NoInfo
                (MkTablePreActionRef
                     (BareName {| stags := NoInfo; str := "set_nhop" |}) nil)
                (TypAction nil
                     [(MkParameter false Directionless (TypBit 32%N) 
                           None {| stags := NoInfo; str := "nhop_ipv4" |});
                      (MkParameter false Directionless (TypBit 9%N) None
                           {| stags := NoInfo; str := "port" |})]));
           (MkTableActionRef NoInfo
                (MkTablePreActionRef
                     (BareName {| stags := NoInfo; str := "_drop" |}) nil)
                (TypAction nil nil))] None None (Some 1024%N) nil);
     (DeclTable NoInfo {| stags := NoInfo; str := "nat" |}
          [(MkTableKey NoInfo
                (MkExpression NoInfo
                     (ExpExpressionMember
                          (MkExpression NoInfo
                               (ExpExpressionMember
                                    (MkExpression NoInfo
                                         (ExpName
                                          (BareName
                                           {| stags := NoInfo;
                                              str := "meta" |}) NoLocator)
                                         (TypTypeName (
                                           {| stags := NoInfo;
                                              str := "metadata" |})) InOut)
                                    {| stags := NoInfo; str := "meta" |})
                               (TypStruct
                                [( {| stags := NoInfo; str := "do_forward" |},
                                   (TypBit 1%N) );
                                 ( {| stags := NoInfo; str := "ipv4_sa" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "ipv4_da" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "tcp_sp" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "tcp_dp" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "nhop_ipv4" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo;
                                      str := "if_ipv4_addr" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo;
                                      str := "if_mac_addr" |},
                                   (TypBit 48%N) );
                                 ( {| stags := NoInfo; str := "is_ext_if" |},
                                   (TypBit 1%N) );
                                 ( {| stags := NoInfo; str := "tcpLength" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "if_index" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo;
                                      str := "init_egress_spec" |},
                                   (TypBit 9%N) )]) Directionless)
                          {| stags := NoInfo; str := "is_ext_if" |})
                     (TypBit 1%N) Directionless)
                {| stags := NoInfo; str := "exact" |});
           (MkTableKey NoInfo
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
                                                   (TypTypeName (
                                                     {| stags := NoInfo;
                                                        str := "headers" |}))
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
                                    {| stags := NoInfo; str := "isValid" |})
                               (TypFunction
                                (MkFunctionType nil nil FunBuiltin TypBool))
                               Directionless) nil nil) TypBool Directionless)
                {| stags := NoInfo; str := "exact" |});
           (MkTableKey NoInfo
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
                                                   (TypTypeName (
                                                     {| stags := NoInfo;
                                                        str := "headers" |}))
                                                   InOut)
                                              {| stags := NoInfo;
                                                 str := "tcp" |})
                                         (TypHeader
                                          [( {| stags := NoInfo;
                                                str := "srcPort" |},
                                             (TypBit 16%N) );
                                           ( {| stags := NoInfo;
                                                str := "dstPort" |},
                                             (TypBit 16%N) );
                                           ( {| stags := NoInfo;
                                                str := "seqNo" |},
                                             (TypBit 32%N) );
                                           ( {| stags := NoInfo;
                                                str := "ackNo" |},
                                             (TypBit 32%N) );
                                           ( {| stags := NoInfo;
                                                str := "dataOffset" |},
                                             (TypBit 4%N) );
                                           ( {| stags := NoInfo;
                                                str := "res" |},
                                             (TypBit 4%N) );
                                           ( {| stags := NoInfo;
                                                str := "flags" |},
                                             (TypBit 8%N) );
                                           ( {| stags := NoInfo;
                                                str := "window" |},
                                             (TypBit 16%N) );
                                           ( {| stags := NoInfo;
                                                str := "checksum" |},
                                             (TypBit 16%N) );
                                           ( {| stags := NoInfo;
                                                str := "urgentPtr" |},
                                             (TypBit 16%N) )]) Directionless)
                                    {| stags := NoInfo; str := "isValid" |})
                               (TypFunction
                                (MkFunctionType nil nil FunBuiltin TypBool))
                               Directionless) nil nil) TypBool Directionless)
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
                                         (TypTypeName (
                                           {| stags := NoInfo;
                                              str := "headers" |})) InOut)
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
                {| stags := NoInfo; str := "ternary" |});
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
                                         (TypTypeName (
                                           {| stags := NoInfo;
                                              str := "headers" |})) InOut)
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
                {| stags := NoInfo; str := "ternary" |});
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
                                         (TypTypeName (
                                           {| stags := NoInfo;
                                              str := "headers" |})) InOut)
                                    {| stags := NoInfo; str := "tcp" |})
                               (TypHeader
                                [( {| stags := NoInfo; str := "srcPort" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "dstPort" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "seqNo" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "ackNo" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "dataOffset" |},
                                   (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "res" |},
                                   (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "flags" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo; str := "window" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "checksum" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "urgentPtr" |},
                                   (TypBit 16%N) )]) Directionless)
                          {| stags := NoInfo; str := "srcPort" |})
                     (TypBit 16%N) Directionless)
                {| stags := NoInfo; str := "ternary" |});
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
                                         (TypTypeName (
                                           {| stags := NoInfo;
                                              str := "headers" |})) InOut)
                                    {| stags := NoInfo; str := "tcp" |})
                               (TypHeader
                                [( {| stags := NoInfo; str := "srcPort" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "dstPort" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "seqNo" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "ackNo" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "dataOffset" |},
                                   (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "res" |},
                                   (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "flags" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo; str := "window" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "checksum" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "urgentPtr" |},
                                   (TypBit 16%N) )]) Directionless)
                          {| stags := NoInfo; str := "dstPort" |})
                     (TypBit 16%N) Directionless)
                {| stags := NoInfo; str := "ternary" |})]
          [(MkTableActionRef NoInfo
                (MkTablePreActionRef
                     (BareName {| stags := NoInfo; str := "_drop" |}) nil)
                (TypAction nil nil));
           (MkTableActionRef NoInfo
                (MkTablePreActionRef
                     (BareName
                      {| stags := NoInfo; str := "nat_miss_int_to_ext" |})
                     nil) (TypAction nil nil));
           (MkTableActionRef NoInfo
                (MkTablePreActionRef
                     (BareName
                      {| stags := NoInfo; str := "nat_miss_ext_to_int" |})
                     nil) (TypAction nil nil));
           (MkTableActionRef NoInfo
                (MkTablePreActionRef
                     (BareName
                      {| stags := NoInfo; str := "nat_hit_int_to_ext" |})
                     nil)
                (TypAction nil
                     [(MkParameter false Directionless (TypBit 32%N) 
                           None {| stags := NoInfo; str := "srcAddr" |});
                      (MkParameter false Directionless (TypBit 16%N) 
                           None {| stags := NoInfo; str := "srcPort" |})]));
           (MkTableActionRef NoInfo
                (MkTablePreActionRef
                     (BareName
                      {| stags := NoInfo; str := "nat_hit_ext_to_int" |})
                     nil)
                (TypAction nil
                     [(MkParameter false Directionless (TypBit 32%N) 
                           None {| stags := NoInfo; str := "dstAddr" |});
                      (MkParameter false Directionless (TypBit 16%N) 
                           None {| stags := NoInfo; str := "dstPort" |})]));
           (MkTableActionRef NoInfo
                (MkTablePreActionRef
                     (BareName {| stags := NoInfo; str := "nat_no_nat" |})
                     nil) (TypAction nil nil))] None None (Some 128%N) nil)]
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
                                                 str := "meta" |}) NoLocator)
                                            (TypTypeName (
                                              {| stags := NoInfo;
                                                 str := "metadata" |}))
                                            InOut)
                                       {| stags := NoInfo; str := "meta" |})
                                  (TypStruct
                                   [( {| stags := NoInfo;
                                         str := "do_forward" |},
                                      (TypBit 1%N) );
                                    ( {| stags := NoInfo; str := "ipv4_sa" |},
                                      (TypBit 32%N) );
                                    ( {| stags := NoInfo; str := "ipv4_da" |},
                                      (TypBit 32%N) );
                                    ( {| stags := NoInfo; str := "tcp_sp" |},
                                      (TypBit 16%N) );
                                    ( {| stags := NoInfo; str := "tcp_dp" |},
                                      (TypBit 16%N) );
                                    ( {| stags := NoInfo;
                                         str := "nhop_ipv4" |},
                                      (TypBit 32%N) );
                                    ( {| stags := NoInfo;
                                         str := "if_ipv4_addr" |},
                                      (TypBit 32%N) );
                                    ( {| stags := NoInfo;
                                         str := "if_mac_addr" |},
                                      (TypBit 48%N) );
                                    ( {| stags := NoInfo;
                                         str := "is_ext_if" |},
                                      (TypBit 1%N) );
                                    ( {| stags := NoInfo;
                                         str := "tcpLength" |},
                                      (TypBit 16%N) );
                                    ( {| stags := NoInfo;
                                         str := "if_index" |}, (TypBit 8%N) );
                                    ( {| stags := NoInfo;
                                         str := "init_egress_spec" |},
                                      (TypBit 9%N) )]) Directionless)
                             {| stags := NoInfo; str := "init_egress_spec" |})
                        (TypBit 9%N) Directionless)
                   (MkExpression NoInfo
                        (ExpExpressionMember
                             (MkExpression NoInfo
                                  (ExpName
                                   (BareName
                                    {| stags := NoInfo;
                                       str := "standard_metadata" |})
                                   NoLocator)
                                  (TypTypeName (
                                    {| stags := NoInfo;
                                       str := "standard_metadata_t" |}))
                                  InOut)
                             {| stags := NoInfo; str := "egress_spec" |})
                        (TypBit 9%N) Directionless)) StmUnit)
         (BlockCons
              (MkStatement NoInfo
                   (StatMethodCall
                        (MkExpression NoInfo
                             (ExpExpressionMember
                                  (MkExpression NoInfo
                                       (ExpName
                                        (BareName
                                         {| stags := NoInfo;
                                            str := "if_info" |}) NoLocator)
                                       (TypTable
                                        {| stags := NoInfo;
                                           str := "apply_result_if_info" |})
                                       Directionless)
                                  {| stags := NoInfo; str := "apply" |})
                             (TypFunction
                              (MkFunctionType nil nil FunTable
                                   (TypTypeName (
                                     {| stags := NoInfo;
                                        str := "apply_result_if_info" |}))))
                             Directionless) nil nil) StmUnit)
              (BlockCons
                   (MkStatement NoInfo
                        (StatMethodCall
                             (MkExpression NoInfo
                                  (ExpExpressionMember
                                       (MkExpression NoInfo
                                            (ExpName
                                             (BareName
                                              {| stags := NoInfo;
                                                 str := "nat" |}) NoLocator)
                                            (TypTable
                                             {| stags := NoInfo;
                                                str := "apply_result_nat" |})
                                            Directionless)
                                       {| stags := NoInfo; str := "apply" |})
                                  (TypFunction
                                   (MkFunctionType nil nil FunTable
                                        (TypTypeName (
                                          {| stags := NoInfo;
                                             str := "apply_result_nat" |}))))
                                  Directionless) nil nil) StmUnit)
                   (BlockCons
                        (MkStatement NoInfo
                             (StatConditional
                                  (MkExpression NoInfo
                                       (ExpBinaryOp And
                                                    (MkExpression NoInfo
                                                                    (ExpBinaryOp Eq
                                                                (MkExpression
                                                             NoInfo
                                                               (ExpExpressionMember
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
                                                                    (TypTypeName (
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "metadata" |}))
                                                                    InOut)
                                                                    {| stags := NoInfo;
                                                                    str := "meta" |})
                                                                    (TypStruct
                                                                    [( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "do_forward" |},
                                                                    (
                                                                    TypBit
                                                                    1%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "ipv4_sa" |},
                                                                    (
                                                                    TypBit
                                                                    32%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "ipv4_da" |},
                                                                    (
                                                                    TypBit
                                                                    32%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "tcp_sp" |},
                                                                    (
                                                                    TypBit
                                                                    16%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "tcp_dp" |},
                                                                    (
                                                                    TypBit
                                                                    16%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "nhop_ipv4" |},
                                                                    (
                                                                    TypBit
                                                                    32%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "if_ipv4_addr" |},
                                                                    (
                                                                    TypBit
                                                                    32%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "if_mac_addr" |},
                                                                    (
                                                                    TypBit
                                                                    48%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "is_ext_if" |},
                                                                    (
                                                                    TypBit
                                                                    1%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "tcpLength" |},
                                                                    (
                                                                    TypBit
                                                                    16%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "if_index" |},
                                                                    (
                                                                    TypBit
                                                                    8%N) );
                                                                    ( 
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "init_egress_spec" |},
                                                                    (
                                                                    TypBit
                                                                    9%N) )])
                                                                    Directionless)
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "do_forward" |})
                                                               (TypBit 1%N)
                                                               Directionless)
                                                          (MkExpression
                                                               NoInfo
                                                               (ExpInt
                                                                {| itags := NoInfo;
                                                                   value := 1;
                                                                   width_signed := (
                                                                   Some
                                                                   ( 
                                                                   1%N,
                                                                   false )) |})
                                                               (TypBit 1%N)
                                                               Directionless))
                                                   TypBool Directionless)
                                              (MkExpression NoInfo
                                                   (ExpBinaryOp Gt
                                                                (MkExpression
                                                               NoInfo
                                                               (ExpExpressionMember
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
                                                                    str := "hdr" |})
                                                                    NoLocator)
                                                                    (TypTypeName (
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "headers" |}))
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
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "ttl" |})
                                                               (TypBit 8%N)
                                                               Directionless)
                                                          (MkExpression
                                                               NoInfo
                                                               (ExpInt
                                                                {| itags := NoInfo;
                                                                   value := 0;
                                                                   width_signed := (
                                                                   Some
                                                                   ( 
                                                                   8%N,
                                                                   false )) |})
                                                               (TypBit 8%N)
                                                               Directionless))
                                                   TypBool Directionless))
                                       TypBool Directionless)
                                  (MkStatement NoInfo
                                       (StatBlock
                                        (BlockCons
                                             (MkStatement NoInfo
                                                  (StatMethodCall
                                                       (MkExpression NoInfo
                                                            (ExpExpressionMember
                                                                 (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "ipv4_lpm" |})
                                                                    NoLocator)
                                                                    (TypTable
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "apply_result_ipv4_lpm" |})
                                                                    Directionless)
                                                                 {| stags := NoInfo;
                                                                    str := "apply" |})
                                                            (TypFunction
                                                             (MkFunctionType
                                                                  nil nil
                                                                  FunTable
                                                                  (TypTypeName (
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "apply_result_ipv4_lpm" |}))))
                                                            Directionless)
                                                       nil nil) StmUnit)
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
                                                                    str := "forward" |})
                                                                    NoLocator)
                                                                    (TypTable
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "apply_result_forward" |})
                                                                    Directionless)
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "apply" |})
                                                                 (TypFunction
                                                                  (MkFunctionType
                                                                    nil nil
                                                                    FunTable
                                                                    (TypTypeName (
                                                                    {| 
                                                                    stags := NoInfo;
                                                                    str := "apply_result_forward" |}))))
                                                                 Directionless)
                                                            nil nil) StmUnit)
                                                  (BlockEmpty NoInfo))))
                                       StmUnit) None) StmUnit)
                        (BlockEmpty NoInfo))))).

Definition DeparserImpl := DeclControl NoInfo
    {| stags := NoInfo; str := "DeparserImpl" |} nil
    [(MkParameter false Directionless
          (TypTypeName ( {| stags := NoInfo; str := "packet_out" |}))
          None {| stags := NoInfo; str := "packet" |});
     (MkParameter false In
          (TypTypeName ( {| stags := NoInfo; str := "headers" |}))
          None {| stags := NoInfo; str := "hdr" |})] nil nil
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
                                  (TypTypeName (
                                    {| stags := NoInfo;
                                       str := "packet_out" |}))
                                  Directionless)
                             {| stags := NoInfo; str := "emit" |})
                        (TypFunction
                         (MkFunctionType [{| stags := NoInfo; str := "T2" |}]
                              [(MkParameter false In
                                    (TypTypeName (
                                      {| stags := NoInfo; str := "T2" |}))
                                    None {| stags := NoInfo; str := "hdr" |})]
                              FunExtern TypVoid)) Directionless)
                   [(TypHeader
                     [( {| stags := NoInfo; str := "preamble" |},
                        (TypBit 64%N) );
                      ( {| stags := NoInfo; str := "device" |},
                        (TypBit 8%N) );
                      ( {| stags := NoInfo; str := "reason" |},
                        (TypBit 8%N) );
                      ( {| stags := NoInfo; str := "if_index" |},
                        (TypBit 8%N) )])]
                   [(Some
                     (MkExpression NoInfo
                          (ExpExpressionMember
                               (MkExpression NoInfo
                                    (ExpName
                                     (BareName
                                      {| stags := NoInfo; str := "hdr" |})
                                     NoLocator)
                                    (TypTypeName (
                                      {| stags := NoInfo; str := "headers" |}))
                                    In)
                               {| stags := NoInfo; str := "cpu_header" |})
                          (TypHeader
                           [( {| stags := NoInfo; str := "preamble" |},
                              (TypBit 64%N) );
                            ( {| stags := NoInfo; str := "device" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "reason" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "if_index" |},
                              (TypBit 8%N) )]) Directionless))]) StmUnit)
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
                                       (TypTypeName (
                                         {| stags := NoInfo;
                                            str := "packet_out" |}))
                                       Directionless)
                                  {| stags := NoInfo; str := "emit" |})
                             (TypFunction
                              (MkFunctionType
                                   [{| stags := NoInfo; str := "T2" |}]
                                   [(MkParameter false In
                                         (TypTypeName (
                                           {| stags := NoInfo; str := "T2" |}))
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
                                           {| stags := NoInfo;
                                              str := "hdr" |}) NoLocator)
                                         (TypTypeName (
                                           {| stags := NoInfo;
                                              str := "headers" |})) In)
                                    {| stags := NoInfo; str := "ethernet" |})
                               (TypHeader
                                [( {| stags := NoInfo; str := "dstAddr" |},
                                   (TypBit 48%N) );
                                 ( {| stags := NoInfo; str := "srcAddr" |},
                                   (TypBit 48%N) );
                                 ( {| stags := NoInfo; str := "etherType" |},
                                   (TypBit 16%N) )]) Directionless))])
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
                                            (TypTypeName (
                                              {| stags := NoInfo;
                                                 str := "packet_out" |}))
                                            Directionless)
                                       {| stags := NoInfo; str := "emit" |})
                                  (TypFunction
                                   (MkFunctionType
                                        [{| stags := NoInfo; str := "T2" |}]
                                        [(MkParameter false In
                                              (TypTypeName (
                                                {| stags := NoInfo;
                                                   str := "T2" |})) None
                                              {| stags := NoInfo;
                                                 str := "hdr" |})] FunExtern
                                        TypVoid)) Directionless)
                             [(TypHeader
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
                                              (TypTypeName (
                                                {| stags := NoInfo;
                                                   str := "headers" |})) In)
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
                                                 (TypTypeName (
                                                   {| stags := NoInfo;
                                                      str := "packet_out" |}))
                                                 Directionless)
                                            {| stags := NoInfo;
                                               str := "emit" |})
                                       (TypFunction
                                        (MkFunctionType
                                             [{| stags := NoInfo;
                                                 str := "T2" |}]
                                             [(MkParameter false In
                                                   (TypTypeName (
                                                     {| stags := NoInfo;
                                                        str := "T2" |})) 
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
                                     ( {| stags := NoInfo; str := "seqNo" |},
                                       (TypBit 32%N) );
                                     ( {| stags := NoInfo; str := "ackNo" |},
                                       (TypBit 32%N) );
                                     ( {| stags := NoInfo;
                                          str := "dataOffset" |},
                                       (TypBit 4%N) );
                                     ( {| stags := NoInfo; str := "res" |},
                                       (TypBit 4%N) );
                                     ( {| stags := NoInfo; str := "flags" |},
                                       (TypBit 8%N) );
                                     ( {| stags := NoInfo; str := "window" |},
                                       (TypBit 16%N) );
                                     ( {| stags := NoInfo;
                                          str := "checksum" |},
                                       (TypBit 16%N) );
                                     ( {| stags := NoInfo;
                                          str := "urgentPtr" |},
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
                                                   (TypTypeName (
                                                     {| stags := NoInfo;
                                                        str := "headers" |}))
                                                   In)
                                              {| stags := NoInfo;
                                                 str := "tcp" |})
                                         (TypHeader
                                          [( {| stags := NoInfo;
                                                str := "srcPort" |},
                                             (TypBit 16%N) );
                                           ( {| stags := NoInfo;
                                                str := "dstPort" |},
                                             (TypBit 16%N) );
                                           ( {| stags := NoInfo;
                                                str := "seqNo" |},
                                             (TypBit 32%N) );
                                           ( {| stags := NoInfo;
                                                str := "ackNo" |},
                                             (TypBit 32%N) );
                                           ( {| stags := NoInfo;
                                                str := "dataOffset" |},
                                             (TypBit 4%N) );
                                           ( {| stags := NoInfo;
                                                str := "res" |},
                                             (TypBit 4%N) );
                                           ( {| stags := NoInfo;
                                                str := "flags" |},
                                             (TypBit 8%N) );
                                           ( {| stags := NoInfo;
                                                str := "window" |},
                                             (TypBit 16%N) );
                                           ( {| stags := NoInfo;
                                                str := "checksum" |},
                                             (TypBit 16%N) );
                                           ( {| stags := NoInfo;
                                                str := "urgentPtr" |},
                                             (TypBit 16%N) )]) Directionless))])
                             StmUnit) (BlockEmpty NoInfo))))).

Definition verifyChecksum := DeclControl NoInfo
    {| stags := NoInfo; str := "verifyChecksum" |} nil
    [(MkParameter false InOut
          (TypTypeName ( {| stags := NoInfo; str := "headers" |}))
          None {| stags := NoInfo; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName ( {| stags := NoInfo; str := "metadata" |}))
          None {| stags := NoInfo; str := "meta" |})] nil nil
    (BlockCons
         (MkStatement NoInfo
              (StatMethodCall
                   (MkExpression NoInfo
                        (ExpName
                         (BareName
                          {| stags := NoInfo; str := "verify_checksum" |})
                         NoLocator)
                        (TypFunction
                         (MkFunctionType
                              [{| stags := NoInfo; str := "T10" |};
                               {| stags := NoInfo; str := "O11" |}]
                              [(MkParameter false In TypBool None
                                    {| stags := NoInfo; str := "condition" |});
                               (MkParameter false In
                                    (TypTypeName (
                                      {| stags := NoInfo; str := "T10" |}))
                                    None
                                    {| stags := NoInfo; str := "data" |});
                               (MkParameter false In
                                    (TypTypeName (
                                      {| stags := NoInfo; str := "O11" |}))
                                    None
                                    {| stags := NoInfo; str := "checksum" |});
                               (MkParameter false Directionless
                                    (TypTypeName (
                                      {| stags := NoInfo;
                                         str := "HashAlgorithm" |})) 
                                    None
                                    {| stags := NoInfo; str := "algo" |})]
                              FunExtern TypVoid)) Directionless)
                   [(TypList
                     [(TypBit 4%N); (TypBit 4%N); (TypBit 8%N);
                      (TypBit 16%N); (TypBit 16%N); (TypBit 3%N);
                      (TypBit 13%N); (TypBit 8%N); (TypBit 8%N);
                      (TypBit 32%N); (TypBit 32%N)]); (TypBit 16%N)]
                   [(Some
                     (MkExpression NoInfo (ExpBool true) TypBool
                          Directionless));
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
                                                     (TypTypeName (
                                                       {| stags := NoInfo;
                                                          str := "headers" |}))
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
                                                     (TypTypeName (
                                                       {| stags := NoInfo;
                                                          str := "headers" |}))
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
                                                     (TypTypeName (
                                                       {| stags := NoInfo;
                                                          str := "headers" |}))
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
                                                     (TypTypeName (
                                                       {| stags := NoInfo;
                                                          str := "headers" |}))
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
                                                     (TypTypeName (
                                                       {| stags := NoInfo;
                                                          str := "headers" |}))
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
                                                     (TypTypeName (
                                                       {| stags := NoInfo;
                                                          str := "headers" |}))
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
                                                     (TypTypeName (
                                                       {| stags := NoInfo;
                                                          str := "headers" |}))
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
                                                     (TypTypeName (
                                                       {| stags := NoInfo;
                                                          str := "headers" |}))
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
                                                     (TypTypeName (
                                                       {| stags := NoInfo;
                                                          str := "headers" |}))
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
                                                     (TypTypeName (
                                                       {| stags := NoInfo;
                                                          str := "headers" |}))
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
                                                     (TypTypeName (
                                                       {| stags := NoInfo;
                                                          str := "headers" |}))
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
                                              (TypTypeName (
                                                {| stags := NoInfo;
                                                   str := "headers" |}))
                                              InOut)
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
                          (ExpTypeMember (
                                {| stags := NoInfo; str := "HashAlgorithm" |})
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
                          Directionless))]) StmUnit)
         (BlockCons
              (MkStatement NoInfo
                   (StatMethodCall
                        (MkExpression NoInfo
                             (ExpName
                              (BareName
                               {| stags := NoInfo;
                                  str := "verify_checksum_with_payload" |})
                              NoLocator)
                             (TypFunction
                              (MkFunctionType
                                   [{| stags := NoInfo; str := "T14" |};
                                    {| stags := NoInfo; str := "O15" |}]
                                   [(MkParameter false In TypBool None
                                         {| stags := NoInfo;
                                            str := "condition" |});
                                    (MkParameter false In
                                         (TypTypeName (
                                           {| stags := NoInfo;
                                              str := "T14" |})) None
                                         {| stags := NoInfo; str := "data" |});
                                    (MkParameter false In
                                         (TypTypeName (
                                           {| stags := NoInfo;
                                              str := "O15" |})) None
                                         {| stags := NoInfo;
                                            str := "checksum" |});
                                    (MkParameter false Directionless
                                         (TypTypeName (
                                           {| stags := NoInfo;
                                              str := "HashAlgorithm" |}))
                                         None
                                         {| stags := NoInfo; str := "algo" |})]
                                   FunExtern TypVoid)) Directionless)
                        [(TypList
                          [(TypBit 32%N); (TypBit 32%N); (TypBit 8%N);
                           (TypBit 8%N); (TypBit 16%N); (TypBit 16%N);
                           (TypBit 16%N); (TypBit 32%N); (TypBit 32%N);
                           (TypBit 4%N); (TypBit 4%N); (TypBit 8%N);
                           (TypBit 16%N); (TypBit 16%N)]); (TypBit 16%N)]
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
                                                             (TypTypeName (
                                                               {| stags := NoInfo;
                                                                  str := "headers" |}))
                                                             InOut)
                                                        {| stags := NoInfo;
                                                           str := "tcp" |})
                                                   (TypHeader
                                                    [( {| stags := NoInfo;
                                                          str := "srcPort" |},
                                                       (TypBit 16%N) );
                                                     ( {| stags := NoInfo;
                                                          str := "dstPort" |},
                                                       (TypBit 16%N) );
                                                     ( {| stags := NoInfo;
                                                          str := "seqNo" |},
                                                       (TypBit 32%N) );
                                                     ( {| stags := NoInfo;
                                                          str := "ackNo" |},
                                                       (TypBit 32%N) );
                                                     ( {| stags := NoInfo;
                                                          str := "dataOffset" |},
                                                       (TypBit 4%N) );
                                                     ( {| stags := NoInfo;
                                                          str := "res" |},
                                                       (TypBit 4%N) );
                                                     ( {| stags := NoInfo;
                                                          str := "flags" |},
                                                       (TypBit 8%N) );
                                                     ( {| stags := NoInfo;
                                                          str := "window" |},
                                                       (TypBit 16%N) );
                                                     ( {| stags := NoInfo;
                                                          str := "checksum" |},
                                                       (TypBit 16%N) );
                                                     ( {| stags := NoInfo;
                                                          str := "urgentPtr" |},
                                                       (TypBit 16%N) )])
                                                   Directionless)
                                              {| stags := NoInfo;
                                                 str := "isValid" |})
                                         (TypFunction
                                          (MkFunctionType nil nil FunBuiltin
                                               TypBool)) Directionless) nil
                                    nil) TypBool Directionless));
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
                                                          (TypTypeName (
                                                            {| stags := NoInfo;
                                                               str := "headers" |}))
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
                                              str := "srcAddr" |})
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
                                                          (TypTypeName (
                                                            {| stags := NoInfo;
                                                               str := "headers" |}))
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
                                              str := "dstAddr" |})
                                      (TypBit 32%N) Directionless);
                                 (MkExpression NoInfo
                                      (ExpInt
                                       {| itags := NoInfo; value := 0;
                                          width_signed := (Some
                                                           ( 8%N, false )) |})
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
                                                          (TypTypeName (
                                                            {| stags := NoInfo;
                                                               str := "headers" |}))
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
                                              str := "protocol" |})
                                      (TypBit 8%N) Directionless);
                                 (MkExpression NoInfo
                                      (ExpExpressionMember
                                           (MkExpression NoInfo
                                                (ExpExpressionMember
                                                     (MkExpression NoInfo
                                                          (ExpName
                                                           (BareName
                                                            {| stags := NoInfo;
                                                               str := "meta" |})
                                                           NoLocator)
                                                          (TypTypeName (
                                                            {| stags := NoInfo;
                                                               str := "metadata" |}))
                                                          InOut)
                                                     {| stags := NoInfo;
                                                        str := "meta" |})
                                                (TypStruct
                                                 [( {| stags := NoInfo;
                                                       str := "do_forward" |},
                                                    (TypBit 1%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "ipv4_sa" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "ipv4_da" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "tcp_sp" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "tcp_dp" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "nhop_ipv4" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "if_ipv4_addr" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "if_mac_addr" |},
                                                    (TypBit 48%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "is_ext_if" |},
                                                    (TypBit 1%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "tcpLength" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "if_index" |},
                                                    (TypBit 8%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "init_egress_spec" |},
                                                    (TypBit 9%N) )])
                                                Directionless)
                                           {| stags := NoInfo;
                                              str := "tcpLength" |})
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
                                                          (TypTypeName (
                                                            {| stags := NoInfo;
                                                               str := "headers" |}))
                                                          InOut)
                                                     {| stags := NoInfo;
                                                        str := "tcp" |})
                                                (TypHeader
                                                 [( {| stags := NoInfo;
                                                       str := "srcPort" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "dstPort" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "seqNo" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "ackNo" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "dataOffset" |},
                                                    (TypBit 4%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "res" |},
                                                    (TypBit 4%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "flags" |},
                                                    (TypBit 8%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "window" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "checksum" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "urgentPtr" |},
                                                    (TypBit 16%N) )])
                                                Directionless)
                                           {| stags := NoInfo;
                                              str := "srcPort" |})
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
                                                          (TypTypeName (
                                                            {| stags := NoInfo;
                                                               str := "headers" |}))
                                                          InOut)
                                                     {| stags := NoInfo;
                                                        str := "tcp" |})
                                                (TypHeader
                                                 [( {| stags := NoInfo;
                                                       str := "srcPort" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "dstPort" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "seqNo" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "ackNo" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "dataOffset" |},
                                                    (TypBit 4%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "res" |},
                                                    (TypBit 4%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "flags" |},
                                                    (TypBit 8%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "window" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "checksum" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "urgentPtr" |},
                                                    (TypBit 16%N) )])
                                                Directionless)
                                           {| stags := NoInfo;
                                              str := "dstPort" |})
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
                                                          (TypTypeName (
                                                            {| stags := NoInfo;
                                                               str := "headers" |}))
                                                          InOut)
                                                     {| stags := NoInfo;
                                                        str := "tcp" |})
                                                (TypHeader
                                                 [( {| stags := NoInfo;
                                                       str := "srcPort" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "dstPort" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "seqNo" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "ackNo" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "dataOffset" |},
                                                    (TypBit 4%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "res" |},
                                                    (TypBit 4%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "flags" |},
                                                    (TypBit 8%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "window" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "checksum" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "urgentPtr" |},
                                                    (TypBit 16%N) )])
                                                Directionless)
                                           {| stags := NoInfo;
                                              str := "seqNo" |})
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
                                                          (TypTypeName (
                                                            {| stags := NoInfo;
                                                               str := "headers" |}))
                                                          InOut)
                                                     {| stags := NoInfo;
                                                        str := "tcp" |})
                                                (TypHeader
                                                 [( {| stags := NoInfo;
                                                       str := "srcPort" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "dstPort" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "seqNo" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "ackNo" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "dataOffset" |},
                                                    (TypBit 4%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "res" |},
                                                    (TypBit 4%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "flags" |},
                                                    (TypBit 8%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "window" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "checksum" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "urgentPtr" |},
                                                    (TypBit 16%N) )])
                                                Directionless)
                                           {| stags := NoInfo;
                                              str := "ackNo" |})
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
                                                          (TypTypeName (
                                                            {| stags := NoInfo;
                                                               str := "headers" |}))
                                                          InOut)
                                                     {| stags := NoInfo;
                                                        str := "tcp" |})
                                                (TypHeader
                                                 [( {| stags := NoInfo;
                                                       str := "srcPort" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "dstPort" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "seqNo" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "ackNo" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "dataOffset" |},
                                                    (TypBit 4%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "res" |},
                                                    (TypBit 4%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "flags" |},
                                                    (TypBit 8%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "window" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "checksum" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "urgentPtr" |},
                                                    (TypBit 16%N) )])
                                                Directionless)
                                           {| stags := NoInfo;
                                              str := "dataOffset" |})
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
                                                          (TypTypeName (
                                                            {| stags := NoInfo;
                                                               str := "headers" |}))
                                                          InOut)
                                                     {| stags := NoInfo;
                                                        str := "tcp" |})
                                                (TypHeader
                                                 [( {| stags := NoInfo;
                                                       str := "srcPort" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "dstPort" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "seqNo" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "ackNo" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "dataOffset" |},
                                                    (TypBit 4%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "res" |},
                                                    (TypBit 4%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "flags" |},
                                                    (TypBit 8%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "window" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "checksum" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "urgentPtr" |},
                                                    (TypBit 16%N) )])
                                                Directionless)
                                           {| stags := NoInfo;
                                              str := "res" |}) (TypBit 4%N)
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
                                                          (TypTypeName (
                                                            {| stags := NoInfo;
                                                               str := "headers" |}))
                                                          InOut)
                                                     {| stags := NoInfo;
                                                        str := "tcp" |})
                                                (TypHeader
                                                 [( {| stags := NoInfo;
                                                       str := "srcPort" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "dstPort" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "seqNo" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "ackNo" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "dataOffset" |},
                                                    (TypBit 4%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "res" |},
                                                    (TypBit 4%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "flags" |},
                                                    (TypBit 8%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "window" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "checksum" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "urgentPtr" |},
                                                    (TypBit 16%N) )])
                                                Directionless)
                                           {| stags := NoInfo;
                                              str := "flags" |}) (TypBit 8%N)
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
                                                          (TypTypeName (
                                                            {| stags := NoInfo;
                                                               str := "headers" |}))
                                                          InOut)
                                                     {| stags := NoInfo;
                                                        str := "tcp" |})
                                                (TypHeader
                                                 [( {| stags := NoInfo;
                                                       str := "srcPort" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "dstPort" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "seqNo" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "ackNo" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "dataOffset" |},
                                                    (TypBit 4%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "res" |},
                                                    (TypBit 4%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "flags" |},
                                                    (TypBit 8%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "window" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "checksum" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "urgentPtr" |},
                                                    (TypBit 16%N) )])
                                                Directionless)
                                           {| stags := NoInfo;
                                              str := "window" |})
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
                                                          (TypTypeName (
                                                            {| stags := NoInfo;
                                                               str := "headers" |}))
                                                          InOut)
                                                     {| stags := NoInfo;
                                                        str := "tcp" |})
                                                (TypHeader
                                                 [( {| stags := NoInfo;
                                                       str := "srcPort" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "dstPort" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "seqNo" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "ackNo" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "dataOffset" |},
                                                    (TypBit 4%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "res" |},
                                                    (TypBit 4%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "flags" |},
                                                    (TypBit 8%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "window" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "checksum" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "urgentPtr" |},
                                                    (TypBit 16%N) )])
                                                Directionless)
                                           {| stags := NoInfo;
                                              str := "urgentPtr" |})
                                      (TypBit 16%N) Directionless)])
                               (TypList
                                [(TypBit 32%N); (TypBit 32%N); (TypBit 8%N);
                                 (TypBit 8%N); (TypBit 16%N); (TypBit 16%N);
                                 (TypBit 16%N); (TypBit 32%N); (TypBit 32%N);
                                 (TypBit 4%N); (TypBit 4%N); (TypBit 8%N);
                                 (TypBit 16%N); (TypBit 16%N)])
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
                                                   (TypTypeName (
                                                     {| stags := NoInfo;
                                                        str := "headers" |}))
                                                   InOut)
                                              {| stags := NoInfo;
                                                 str := "tcp" |})
                                         (TypHeader
                                          [( {| stags := NoInfo;
                                                str := "srcPort" |},
                                             (TypBit 16%N) );
                                           ( {| stags := NoInfo;
                                                str := "dstPort" |},
                                             (TypBit 16%N) );
                                           ( {| stags := NoInfo;
                                                str := "seqNo" |},
                                             (TypBit 32%N) );
                                           ( {| stags := NoInfo;
                                                str := "ackNo" |},
                                             (TypBit 32%N) );
                                           ( {| stags := NoInfo;
                                                str := "dataOffset" |},
                                             (TypBit 4%N) );
                                           ( {| stags := NoInfo;
                                                str := "res" |},
                                             (TypBit 4%N) );
                                           ( {| stags := NoInfo;
                                                str := "flags" |},
                                             (TypBit 8%N) );
                                           ( {| stags := NoInfo;
                                                str := "window" |},
                                             (TypBit 16%N) );
                                           ( {| stags := NoInfo;
                                                str := "checksum" |},
                                             (TypBit 16%N) );
                                           ( {| stags := NoInfo;
                                                str := "urgentPtr" |},
                                             (TypBit 16%N) )]) Directionless)
                                    {| stags := NoInfo; str := "checksum" |})
                               (TypBit 16%N) Directionless));
                         (Some
                          (MkExpression NoInfo
                               (ExpTypeMember (
                                     {| stags := NoInfo;
                                        str := "HashAlgorithm" |})
                                    {| stags := NoInfo; str := "csum16" |})
                               (TypEnum
                                    {| stags := NoInfo;
                                       str := "HashAlgorithm" |} None
                                    [{| stags := NoInfo; str := "crc32" |};
                                     {| stags := NoInfo;
                                        str := "crc32_custom" |};
                                     {| stags := NoInfo; str := "crc16" |};
                                     {| stags := NoInfo;
                                        str := "crc16_custom" |};
                                     {| stags := NoInfo; str := "random" |};
                                     {| stags := NoInfo; str := "identity" |};
                                     {| stags := NoInfo; str := "csum16" |};
                                     {| stags := NoInfo; str := "xor16" |}])
                               Directionless))]) StmUnit)
              (BlockEmpty NoInfo))).

Definition computeChecksum := DeclControl NoInfo
    {| stags := NoInfo; str := "computeChecksum" |} nil
    [(MkParameter false InOut
          (TypTypeName ( {| stags := NoInfo; str := "headers" |}))
          None {| stags := NoInfo; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName ( {| stags := NoInfo; str := "metadata" |}))
          None {| stags := NoInfo; str := "meta" |})] nil nil
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
                                    (TypTypeName (
                                      {| stags := NoInfo; str := "T12" |}))
                                    None
                                    {| stags := NoInfo; str := "data" |});
                               (MkParameter false InOut
                                    (TypTypeName (
                                      {| stags := NoInfo; str := "O13" |}))
                                    None
                                    {| stags := NoInfo; str := "checksum" |});
                               (MkParameter false Directionless
                                    (TypTypeName (
                                      {| stags := NoInfo;
                                         str := "HashAlgorithm" |})) 
                                    None
                                    {| stags := NoInfo; str := "algo" |})]
                              FunExtern TypVoid)) Directionless)
                   [(TypList
                     [(TypBit 4%N); (TypBit 4%N); (TypBit 8%N);
                      (TypBit 16%N); (TypBit 16%N); (TypBit 3%N);
                      (TypBit 13%N); (TypBit 8%N); (TypBit 8%N);
                      (TypBit 32%N); (TypBit 32%N)]); (TypBit 16%N)]
                   [(Some
                     (MkExpression NoInfo (ExpBool true) TypBool
                          Directionless));
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
                                                     (TypTypeName (
                                                       {| stags := NoInfo;
                                                          str := "headers" |}))
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
                                                     (TypTypeName (
                                                       {| stags := NoInfo;
                                                          str := "headers" |}))
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
                                                     (TypTypeName (
                                                       {| stags := NoInfo;
                                                          str := "headers" |}))
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
                                                     (TypTypeName (
                                                       {| stags := NoInfo;
                                                          str := "headers" |}))
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
                                                     (TypTypeName (
                                                       {| stags := NoInfo;
                                                          str := "headers" |}))
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
                                                     (TypTypeName (
                                                       {| stags := NoInfo;
                                                          str := "headers" |}))
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
                                                     (TypTypeName (
                                                       {| stags := NoInfo;
                                                          str := "headers" |}))
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
                                                     (TypTypeName (
                                                       {| stags := NoInfo;
                                                          str := "headers" |}))
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
                                                     (TypTypeName (
                                                       {| stags := NoInfo;
                                                          str := "headers" |}))
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
                                                     (TypTypeName (
                                                       {| stags := NoInfo;
                                                          str := "headers" |}))
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
                                                     (TypTypeName (
                                                       {| stags := NoInfo;
                                                          str := "headers" |}))
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
                                              (TypTypeName (
                                                {| stags := NoInfo;
                                                   str := "headers" |}))
                                              InOut)
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
                          (ExpTypeMember (
                                {| stags := NoInfo; str := "HashAlgorithm" |})
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
                          Directionless))]) StmUnit)
         (BlockCons
              (MkStatement NoInfo
                   (StatMethodCall
                        (MkExpression NoInfo
                             (ExpName
                              (BareName
                               {| stags := NoInfo;
                                  str := "update_checksum_with_payload" |})
                              NoLocator)
                             (TypFunction
                              (MkFunctionType
                                   [{| stags := NoInfo; str := "T16" |};
                                    {| stags := NoInfo; str := "O17" |}]
                                   [(MkParameter false In TypBool None
                                         {| stags := NoInfo;
                                            str := "condition" |});
                                    (MkParameter false In
                                         (TypTypeName (
                                           {| stags := NoInfo;
                                              str := "T16" |})) None
                                         {| stags := NoInfo; str := "data" |});
                                    (MkParameter false InOut
                                         (TypTypeName (
                                           {| stags := NoInfo;
                                              str := "O17" |})) None
                                         {| stags := NoInfo;
                                            str := "checksum" |});
                                    (MkParameter false Directionless
                                         (TypTypeName (
                                           {| stags := NoInfo;
                                              str := "HashAlgorithm" |}))
                                         None
                                         {| stags := NoInfo; str := "algo" |})]
                                   FunExtern TypVoid)) Directionless)
                        [(TypList
                          [(TypBit 32%N); (TypBit 32%N); (TypBit 8%N);
                           (TypBit 8%N); (TypBit 16%N); (TypBit 16%N);
                           (TypBit 16%N); (TypBit 32%N); (TypBit 32%N);
                           (TypBit 4%N); (TypBit 4%N); (TypBit 8%N);
                           (TypBit 16%N); (TypBit 16%N)]); (TypBit 16%N)]
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
                                                             (TypTypeName (
                                                               {| stags := NoInfo;
                                                                  str := "headers" |}))
                                                             InOut)
                                                        {| stags := NoInfo;
                                                           str := "tcp" |})
                                                   (TypHeader
                                                    [( {| stags := NoInfo;
                                                          str := "srcPort" |},
                                                       (TypBit 16%N) );
                                                     ( {| stags := NoInfo;
                                                          str := "dstPort" |},
                                                       (TypBit 16%N) );
                                                     ( {| stags := NoInfo;
                                                          str := "seqNo" |},
                                                       (TypBit 32%N) );
                                                     ( {| stags := NoInfo;
                                                          str := "ackNo" |},
                                                       (TypBit 32%N) );
                                                     ( {| stags := NoInfo;
                                                          str := "dataOffset" |},
                                                       (TypBit 4%N) );
                                                     ( {| stags := NoInfo;
                                                          str := "res" |},
                                                       (TypBit 4%N) );
                                                     ( {| stags := NoInfo;
                                                          str := "flags" |},
                                                       (TypBit 8%N) );
                                                     ( {| stags := NoInfo;
                                                          str := "window" |},
                                                       (TypBit 16%N) );
                                                     ( {| stags := NoInfo;
                                                          str := "checksum" |},
                                                       (TypBit 16%N) );
                                                     ( {| stags := NoInfo;
                                                          str := "urgentPtr" |},
                                                       (TypBit 16%N) )])
                                                   Directionless)
                                              {| stags := NoInfo;
                                                 str := "isValid" |})
                                         (TypFunction
                                          (MkFunctionType nil nil FunBuiltin
                                               TypBool)) Directionless) nil
                                    nil) TypBool Directionless));
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
                                                          (TypTypeName (
                                                            {| stags := NoInfo;
                                                               str := "headers" |}))
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
                                              str := "srcAddr" |})
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
                                                          (TypTypeName (
                                                            {| stags := NoInfo;
                                                               str := "headers" |}))
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
                                              str := "dstAddr" |})
                                      (TypBit 32%N) Directionless);
                                 (MkExpression NoInfo
                                      (ExpInt
                                       {| itags := NoInfo; value := 0;
                                          width_signed := (Some
                                                           ( 8%N, false )) |})
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
                                                          (TypTypeName (
                                                            {| stags := NoInfo;
                                                               str := "headers" |}))
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
                                              str := "protocol" |})
                                      (TypBit 8%N) Directionless);
                                 (MkExpression NoInfo
                                      (ExpExpressionMember
                                           (MkExpression NoInfo
                                                (ExpExpressionMember
                                                     (MkExpression NoInfo
                                                          (ExpName
                                                           (BareName
                                                            {| stags := NoInfo;
                                                               str := "meta" |})
                                                           NoLocator)
                                                          (TypTypeName (
                                                            {| stags := NoInfo;
                                                               str := "metadata" |}))
                                                          InOut)
                                                     {| stags := NoInfo;
                                                        str := "meta" |})
                                                (TypStruct
                                                 [( {| stags := NoInfo;
                                                       str := "do_forward" |},
                                                    (TypBit 1%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "ipv4_sa" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "ipv4_da" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "tcp_sp" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "tcp_dp" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "nhop_ipv4" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "if_ipv4_addr" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "if_mac_addr" |},
                                                    (TypBit 48%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "is_ext_if" |},
                                                    (TypBit 1%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "tcpLength" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "if_index" |},
                                                    (TypBit 8%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "init_egress_spec" |},
                                                    (TypBit 9%N) )])
                                                Directionless)
                                           {| stags := NoInfo;
                                              str := "tcpLength" |})
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
                                                          (TypTypeName (
                                                            {| stags := NoInfo;
                                                               str := "headers" |}))
                                                          InOut)
                                                     {| stags := NoInfo;
                                                        str := "tcp" |})
                                                (TypHeader
                                                 [( {| stags := NoInfo;
                                                       str := "srcPort" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "dstPort" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "seqNo" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "ackNo" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "dataOffset" |},
                                                    (TypBit 4%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "res" |},
                                                    (TypBit 4%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "flags" |},
                                                    (TypBit 8%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "window" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "checksum" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "urgentPtr" |},
                                                    (TypBit 16%N) )])
                                                Directionless)
                                           {| stags := NoInfo;
                                              str := "srcPort" |})
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
                                                          (TypTypeName (
                                                            {| stags := NoInfo;
                                                               str := "headers" |}))
                                                          InOut)
                                                     {| stags := NoInfo;
                                                        str := "tcp" |})
                                                (TypHeader
                                                 [( {| stags := NoInfo;
                                                       str := "srcPort" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "dstPort" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "seqNo" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "ackNo" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "dataOffset" |},
                                                    (TypBit 4%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "res" |},
                                                    (TypBit 4%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "flags" |},
                                                    (TypBit 8%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "window" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "checksum" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "urgentPtr" |},
                                                    (TypBit 16%N) )])
                                                Directionless)
                                           {| stags := NoInfo;
                                              str := "dstPort" |})
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
                                                          (TypTypeName (
                                                            {| stags := NoInfo;
                                                               str := "headers" |}))
                                                          InOut)
                                                     {| stags := NoInfo;
                                                        str := "tcp" |})
                                                (TypHeader
                                                 [( {| stags := NoInfo;
                                                       str := "srcPort" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "dstPort" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "seqNo" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "ackNo" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "dataOffset" |},
                                                    (TypBit 4%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "res" |},
                                                    (TypBit 4%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "flags" |},
                                                    (TypBit 8%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "window" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "checksum" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "urgentPtr" |},
                                                    (TypBit 16%N) )])
                                                Directionless)
                                           {| stags := NoInfo;
                                              str := "seqNo" |})
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
                                                          (TypTypeName (
                                                            {| stags := NoInfo;
                                                               str := "headers" |}))
                                                          InOut)
                                                     {| stags := NoInfo;
                                                        str := "tcp" |})
                                                (TypHeader
                                                 [( {| stags := NoInfo;
                                                       str := "srcPort" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "dstPort" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "seqNo" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "ackNo" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "dataOffset" |},
                                                    (TypBit 4%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "res" |},
                                                    (TypBit 4%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "flags" |},
                                                    (TypBit 8%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "window" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "checksum" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "urgentPtr" |},
                                                    (TypBit 16%N) )])
                                                Directionless)
                                           {| stags := NoInfo;
                                              str := "ackNo" |})
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
                                                          (TypTypeName (
                                                            {| stags := NoInfo;
                                                               str := "headers" |}))
                                                          InOut)
                                                     {| stags := NoInfo;
                                                        str := "tcp" |})
                                                (TypHeader
                                                 [( {| stags := NoInfo;
                                                       str := "srcPort" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "dstPort" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "seqNo" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "ackNo" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "dataOffset" |},
                                                    (TypBit 4%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "res" |},
                                                    (TypBit 4%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "flags" |},
                                                    (TypBit 8%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "window" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "checksum" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "urgentPtr" |},
                                                    (TypBit 16%N) )])
                                                Directionless)
                                           {| stags := NoInfo;
                                              str := "dataOffset" |})
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
                                                          (TypTypeName (
                                                            {| stags := NoInfo;
                                                               str := "headers" |}))
                                                          InOut)
                                                     {| stags := NoInfo;
                                                        str := "tcp" |})
                                                (TypHeader
                                                 [( {| stags := NoInfo;
                                                       str := "srcPort" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "dstPort" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "seqNo" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "ackNo" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "dataOffset" |},
                                                    (TypBit 4%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "res" |},
                                                    (TypBit 4%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "flags" |},
                                                    (TypBit 8%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "window" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "checksum" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "urgentPtr" |},
                                                    (TypBit 16%N) )])
                                                Directionless)
                                           {| stags := NoInfo;
                                              str := "res" |}) (TypBit 4%N)
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
                                                          (TypTypeName (
                                                            {| stags := NoInfo;
                                                               str := "headers" |}))
                                                          InOut)
                                                     {| stags := NoInfo;
                                                        str := "tcp" |})
                                                (TypHeader
                                                 [( {| stags := NoInfo;
                                                       str := "srcPort" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "dstPort" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "seqNo" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "ackNo" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "dataOffset" |},
                                                    (TypBit 4%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "res" |},
                                                    (TypBit 4%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "flags" |},
                                                    (TypBit 8%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "window" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "checksum" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "urgentPtr" |},
                                                    (TypBit 16%N) )])
                                                Directionless)
                                           {| stags := NoInfo;
                                              str := "flags" |}) (TypBit 8%N)
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
                                                          (TypTypeName (
                                                            {| stags := NoInfo;
                                                               str := "headers" |}))
                                                          InOut)
                                                     {| stags := NoInfo;
                                                        str := "tcp" |})
                                                (TypHeader
                                                 [( {| stags := NoInfo;
                                                       str := "srcPort" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "dstPort" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "seqNo" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "ackNo" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "dataOffset" |},
                                                    (TypBit 4%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "res" |},
                                                    (TypBit 4%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "flags" |},
                                                    (TypBit 8%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "window" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "checksum" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "urgentPtr" |},
                                                    (TypBit 16%N) )])
                                                Directionless)
                                           {| stags := NoInfo;
                                              str := "window" |})
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
                                                          (TypTypeName (
                                                            {| stags := NoInfo;
                                                               str := "headers" |}))
                                                          InOut)
                                                     {| stags := NoInfo;
                                                        str := "tcp" |})
                                                (TypHeader
                                                 [( {| stags := NoInfo;
                                                       str := "srcPort" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "dstPort" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "seqNo" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "ackNo" |},
                                                    (TypBit 32%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "dataOffset" |},
                                                    (TypBit 4%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "res" |},
                                                    (TypBit 4%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "flags" |},
                                                    (TypBit 8%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "window" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "checksum" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "urgentPtr" |},
                                                    (TypBit 16%N) )])
                                                Directionless)
                                           {| stags := NoInfo;
                                              str := "urgentPtr" |})
                                      (TypBit 16%N) Directionless)])
                               (TypList
                                [(TypBit 32%N); (TypBit 32%N); (TypBit 8%N);
                                 (TypBit 8%N); (TypBit 16%N); (TypBit 16%N);
                                 (TypBit 16%N); (TypBit 32%N); (TypBit 32%N);
                                 (TypBit 4%N); (TypBit 4%N); (TypBit 8%N);
                                 (TypBit 16%N); (TypBit 16%N)])
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
                                                   (TypTypeName (
                                                     {| stags := NoInfo;
                                                        str := "headers" |}))
                                                   InOut)
                                              {| stags := NoInfo;
                                                 str := "tcp" |})
                                         (TypHeader
                                          [( {| stags := NoInfo;
                                                str := "srcPort" |},
                                             (TypBit 16%N) );
                                           ( {| stags := NoInfo;
                                                str := "dstPort" |},
                                             (TypBit 16%N) );
                                           ( {| stags := NoInfo;
                                                str := "seqNo" |},
                                             (TypBit 32%N) );
                                           ( {| stags := NoInfo;
                                                str := "ackNo" |},
                                             (TypBit 32%N) );
                                           ( {| stags := NoInfo;
                                                str := "dataOffset" |},
                                             (TypBit 4%N) );
                                           ( {| stags := NoInfo;
                                                str := "res" |},
                                             (TypBit 4%N) );
                                           ( {| stags := NoInfo;
                                                str := "flags" |},
                                             (TypBit 8%N) );
                                           ( {| stags := NoInfo;
                                                str := "window" |},
                                             (TypBit 16%N) );
                                           ( {| stags := NoInfo;
                                                str := "checksum" |},
                                             (TypBit 16%N) );
                                           ( {| stags := NoInfo;
                                                str := "urgentPtr" |},
                                             (TypBit 16%N) )]) Directionless)
                                    {| stags := NoInfo; str := "checksum" |})
                               (TypBit 16%N) Directionless));
                         (Some
                          (MkExpression NoInfo
                               (ExpTypeMember (
                                     {| stags := NoInfo;
                                        str := "HashAlgorithm" |})
                                    {| stags := NoInfo; str := "csum16" |})
                               (TypEnum
                                    {| stags := NoInfo;
                                       str := "HashAlgorithm" |} None
                                    [{| stags := NoInfo; str := "crc32" |};
                                     {| stags := NoInfo;
                                        str := "crc32_custom" |};
                                     {| stags := NoInfo; str := "crc16" |};
                                     {| stags := NoInfo;
                                        str := "crc16_custom" |};
                                     {| stags := NoInfo; str := "random" |};
                                     {| stags := NoInfo; str := "identity" |};
                                     {| stags := NoInfo; str := "csum16" |};
                                     {| stags := NoInfo; str := "xor16" |}])
                               Directionless))]) StmUnit)
              (BlockEmpty NoInfo))).

Definition main := DeclInstantiation NoInfo
    (TypSpecializedType
         (TypTypeName ( {| stags := NoInfo; str := "V1Switch" |}))
         [(TypStruct
           [( {| stags := NoInfo; str := "cpu_header" |},
              (TypHeader
               [( {| stags := NoInfo; str := "preamble" |}, (TypBit 64%N) );
                ( {| stags := NoInfo; str := "device" |}, (TypBit 8%N) );
                ( {| stags := NoInfo; str := "reason" |}, (TypBit 8%N) );
                ( {| stags := NoInfo; str := "if_index" |}, (TypBit 8%N) )]) );
            ( {| stags := NoInfo; str := "ethernet" |},
              (TypHeader
               [( {| stags := NoInfo; str := "dstAddr" |}, (TypBit 48%N) );
                ( {| stags := NoInfo; str := "srcAddr" |}, (TypBit 48%N) );
                ( {| stags := NoInfo; str := "etherType" |}, (TypBit 16%N) )]) );
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
            ( {| stags := NoInfo; str := "tcp" |},
              (TypHeader
               [( {| stags := NoInfo; str := "srcPort" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "dstPort" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "seqNo" |}, (TypBit 32%N) );
                ( {| stags := NoInfo; str := "ackNo" |}, (TypBit 32%N) );
                ( {| stags := NoInfo; str := "dataOffset" |}, (TypBit 4%N) );
                ( {| stags := NoInfo; str := "res" |}, (TypBit 4%N) );
                ( {| stags := NoInfo; str := "flags" |}, (TypBit 8%N) );
                ( {| stags := NoInfo; str := "window" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "checksum" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "urgentPtr" |}, (TypBit 16%N) )]) )]);
          (TypStruct
           [( {| stags := NoInfo; str := "meta" |},
              (TypStruct
               [( {| stags := NoInfo; str := "do_forward" |}, (TypBit 1%N) );
                ( {| stags := NoInfo; str := "ipv4_sa" |}, (TypBit 32%N) );
                ( {| stags := NoInfo; str := "ipv4_da" |}, (TypBit 32%N) );
                ( {| stags := NoInfo; str := "tcp_sp" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "tcp_dp" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "nhop_ipv4" |}, (TypBit 32%N) );
                ( {| stags := NoInfo; str := "if_ipv4_addr" |},
                  (TypBit 32%N) );
                ( {| stags := NoInfo; str := "if_mac_addr" |},
                  (TypBit 48%N) );
                ( {| stags := NoInfo; str := "is_ext_if" |}, (TypBit 1%N) );
                ( {| stags := NoInfo; str := "tcpLength" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "if_index" |}, (TypBit 8%N) );
                ( {| stags := NoInfo; str := "init_egress_spec" |},
                  (TypBit 9%N) )]) )])])
    [(MkExpression NoInfo
          (ExpNamelessInstantiation
               (TypSpecializedType
                    (TypTypeName ( {| stags := NoInfo; str := "ParserImpl" |}))
                    nil) nil)
          (TypParser
           (MkControlType nil
                [(MkParameter false Directionless
                      (TypExtern {| stags := NoInfo; str := "packet_in" |})
                      None {| stags := NoInfo; str := "packet" |});
                 (MkParameter false Out
                      (TypStruct
                       [( {| stags := NoInfo; str := "cpu_header" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "preamble" |},
                              (TypBit 64%N) );
                            ( {| stags := NoInfo; str := "device" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "reason" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "if_index" |},
                              (TypBit 8%N) )]) );
                        ( {| stags := NoInfo; str := "ethernet" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "dstAddr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "srcAddr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "etherType" |},
                              (TypBit 16%N) )]) );
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
                        ( {| stags := NoInfo; str := "tcp" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "srcPort" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "dstPort" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "seqNo" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "ackNo" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "dataOffset" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "res" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "flags" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "window" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "checksum" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "urgentPtr" |},
                              (TypBit 16%N) )]) )]) None
                      {| stags := NoInfo; str := "hdr" |});
                 (MkParameter false InOut
                      (TypStruct
                       [( {| stags := NoInfo; str := "meta" |},
                          (TypStruct
                           [( {| stags := NoInfo; str := "do_forward" |},
                              (TypBit 1%N) );
                            ( {| stags := NoInfo; str := "ipv4_sa" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "ipv4_da" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "tcp_sp" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "tcp_dp" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "nhop_ipv4" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "if_ipv4_addr" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "if_mac_addr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "is_ext_if" |},
                              (TypBit 1%N) );
                            ( {| stags := NoInfo; str := "tcpLength" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "if_index" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo;
                                 str := "init_egress_spec" |}, (TypBit 9%N) )]) )])
                      None {| stags := NoInfo; str := "meta" |});
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
                    (TypTypeName (
                      {| stags := NoInfo; str := "verifyChecksum" |})) nil)
               nil)
          (TypControl
           (MkControlType nil
                [(MkParameter false InOut
                      (TypStruct
                       [( {| stags := NoInfo; str := "cpu_header" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "preamble" |},
                              (TypBit 64%N) );
                            ( {| stags := NoInfo; str := "device" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "reason" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "if_index" |},
                              (TypBit 8%N) )]) );
                        ( {| stags := NoInfo; str := "ethernet" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "dstAddr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "srcAddr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "etherType" |},
                              (TypBit 16%N) )]) );
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
                        ( {| stags := NoInfo; str := "tcp" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "srcPort" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "dstPort" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "seqNo" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "ackNo" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "dataOffset" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "res" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "flags" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "window" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "checksum" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "urgentPtr" |},
                              (TypBit 16%N) )]) )]) None
                      {| stags := NoInfo; str := "hdr" |});
                 (MkParameter false InOut
                      (TypStruct
                       [( {| stags := NoInfo; str := "meta" |},
                          (TypStruct
                           [( {| stags := NoInfo; str := "do_forward" |},
                              (TypBit 1%N) );
                            ( {| stags := NoInfo; str := "ipv4_sa" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "ipv4_da" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "tcp_sp" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "tcp_dp" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "nhop_ipv4" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "if_ipv4_addr" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "if_mac_addr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "is_ext_if" |},
                              (TypBit 1%N) );
                            ( {| stags := NoInfo; str := "tcpLength" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "if_index" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo;
                                 str := "init_egress_spec" |}, (TypBit 9%N) )]) )])
                      None {| stags := NoInfo; str := "meta" |})]))
          Directionless);
     (MkExpression NoInfo
          (ExpNamelessInstantiation
               (TypSpecializedType
                    (TypTypeName ( {| stags := NoInfo; str := "ingress" |})) nil)
               nil)
          (TypControl
           (MkControlType nil
                [(MkParameter false InOut
                      (TypStruct
                       [( {| stags := NoInfo; str := "cpu_header" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "preamble" |},
                              (TypBit 64%N) );
                            ( {| stags := NoInfo; str := "device" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "reason" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "if_index" |},
                              (TypBit 8%N) )]) );
                        ( {| stags := NoInfo; str := "ethernet" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "dstAddr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "srcAddr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "etherType" |},
                              (TypBit 16%N) )]) );
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
                        ( {| stags := NoInfo; str := "tcp" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "srcPort" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "dstPort" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "seqNo" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "ackNo" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "dataOffset" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "res" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "flags" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "window" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "checksum" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "urgentPtr" |},
                              (TypBit 16%N) )]) )]) None
                      {| stags := NoInfo; str := "hdr" |});
                 (MkParameter false InOut
                      (TypStruct
                       [( {| stags := NoInfo; str := "meta" |},
                          (TypStruct
                           [( {| stags := NoInfo; str := "do_forward" |},
                              (TypBit 1%N) );
                            ( {| stags := NoInfo; str := "ipv4_sa" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "ipv4_da" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "tcp_sp" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "tcp_dp" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "nhop_ipv4" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "if_ipv4_addr" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "if_mac_addr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "is_ext_if" |},
                              (TypBit 1%N) );
                            ( {| stags := NoInfo; str := "tcpLength" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "if_index" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo;
                                 str := "init_egress_spec" |}, (TypBit 9%N) )]) )])
                      None {| stags := NoInfo; str := "meta" |});
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
                    (TypTypeName ( {| stags := NoInfo; str := "egress" |})) nil)
               nil)
          (TypControl
           (MkControlType nil
                [(MkParameter false InOut
                      (TypStruct
                       [( {| stags := NoInfo; str := "cpu_header" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "preamble" |},
                              (TypBit 64%N) );
                            ( {| stags := NoInfo; str := "device" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "reason" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "if_index" |},
                              (TypBit 8%N) )]) );
                        ( {| stags := NoInfo; str := "ethernet" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "dstAddr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "srcAddr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "etherType" |},
                              (TypBit 16%N) )]) );
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
                        ( {| stags := NoInfo; str := "tcp" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "srcPort" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "dstPort" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "seqNo" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "ackNo" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "dataOffset" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "res" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "flags" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "window" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "checksum" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "urgentPtr" |},
                              (TypBit 16%N) )]) )]) None
                      {| stags := NoInfo; str := "hdr" |});
                 (MkParameter false InOut
                      (TypStruct
                       [( {| stags := NoInfo; str := "meta" |},
                          (TypStruct
                           [( {| stags := NoInfo; str := "do_forward" |},
                              (TypBit 1%N) );
                            ( {| stags := NoInfo; str := "ipv4_sa" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "ipv4_da" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "tcp_sp" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "tcp_dp" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "nhop_ipv4" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "if_ipv4_addr" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "if_mac_addr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "is_ext_if" |},
                              (TypBit 1%N) );
                            ( {| stags := NoInfo; str := "tcpLength" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "if_index" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo;
                                 str := "init_egress_spec" |}, (TypBit 9%N) )]) )])
                      None {| stags := NoInfo; str := "meta" |});
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
                    (TypTypeName (
                      {| stags := NoInfo; str := "computeChecksum" |})) nil)
               nil)
          (TypControl
           (MkControlType nil
                [(MkParameter false InOut
                      (TypStruct
                       [( {| stags := NoInfo; str := "cpu_header" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "preamble" |},
                              (TypBit 64%N) );
                            ( {| stags := NoInfo; str := "device" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "reason" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "if_index" |},
                              (TypBit 8%N) )]) );
                        ( {| stags := NoInfo; str := "ethernet" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "dstAddr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "srcAddr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "etherType" |},
                              (TypBit 16%N) )]) );
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
                        ( {| stags := NoInfo; str := "tcp" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "srcPort" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "dstPort" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "seqNo" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "ackNo" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "dataOffset" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "res" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "flags" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "window" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "checksum" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "urgentPtr" |},
                              (TypBit 16%N) )]) )]) None
                      {| stags := NoInfo; str := "hdr" |});
                 (MkParameter false InOut
                      (TypStruct
                       [( {| stags := NoInfo; str := "meta" |},
                          (TypStruct
                           [( {| stags := NoInfo; str := "do_forward" |},
                              (TypBit 1%N) );
                            ( {| stags := NoInfo; str := "ipv4_sa" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "ipv4_da" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "tcp_sp" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "tcp_dp" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "nhop_ipv4" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "if_ipv4_addr" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "if_mac_addr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "is_ext_if" |},
                              (TypBit 1%N) );
                            ( {| stags := NoInfo; str := "tcpLength" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "if_index" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo;
                                 str := "init_egress_spec" |}, (TypBit 9%N) )]) )])
                      None {| stags := NoInfo; str := "meta" |})]))
          Directionless);
     (MkExpression NoInfo
          (ExpNamelessInstantiation
               (TypSpecializedType
                    (TypTypeName ( {| stags := NoInfo; str := "DeparserImpl" |}))
                    nil) nil)
          (TypControl
           (MkControlType nil
                [(MkParameter false Directionless
                      (TypExtern {| stags := NoInfo; str := "packet_out" |})
                      None {| stags := NoInfo; str := "packet" |});
                 (MkParameter false In
                      (TypStruct
                       [( {| stags := NoInfo; str := "cpu_header" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "preamble" |},
                              (TypBit 64%N) );
                            ( {| stags := NoInfo; str := "device" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "reason" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "if_index" |},
                              (TypBit 8%N) )]) );
                        ( {| stags := NoInfo; str := "ethernet" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "dstAddr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "srcAddr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "etherType" |},
                              (TypBit 16%N) )]) );
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
                        ( {| stags := NoInfo; str := "tcp" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "srcPort" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "dstPort" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "seqNo" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "ackNo" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "dataOffset" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "res" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "flags" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "window" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "checksum" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "urgentPtr" |},
                              (TypBit 16%N) )]) )]) None
                      {| stags := NoInfo; str := "hdr" |})])) Directionless)]
    {| stags := NoInfo; str := "main" |} nil.

Definition prog := Syntax.Program
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
     ComputeChecksum; Deparser; V1Switch; intrinsic_metadata_t; meta_t;
     cpu_header_t; ethernet_t; ipv4_t; tcp_t; metadata; headers; ParserImpl;
     egress; ingress; DeparserImpl; verifyChecksum; computeChecksum; main].
*)
