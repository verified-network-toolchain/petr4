open Types
open Info


let default_packet = failwith "unimplemented"

let make_p4String s = M ("default p4String"), s

let default_varbit =
  let open P4Int in
  let i = { value = Bigint.zero; width_signed = None } in
  (M ("Expression"), Expression.Int(M ("default varbit"), i))

let default_unsigned_bit width =
  let open P4Int in
  let i = { value = Bigint.zero; width_signed = Some (width, false) } in
  (M ("Expression"), Expression.Int(M ("default unsigned bit"), i))

let default_signed_bit width =
  let open P4Int in
  let i = { value = Bigint.zero ; width_signed = Some (width, true) } in
  (M ("Expression"), Expression.Int(M ("default unsigned bit"), i))

(* let make_name_arg name =
   let open Argument in
   let open Expression in
   ( M ("default arguments"),
    { value = (M ("default Expression"), make_p4String name ) } ) *)

let default_args =
  let open Argument in (M ("default p4String"), Missing)

let make_annotation ((name: string), (args: 'a list)) =
  let open Annotation in
  ( M ("default annotations"),
    { name = make_p4String name; args = List.map (fun x -> default_args) args})
(* TODO: change default args to make arg *)

let make_field_bit (annote_pair, (name: string), (width: int)) =
  let n = make_p4String name in
  let open TypeDeclaration in
  let open Type in
  (M("Field"),
   { annotations = List.map make_annotation annote_pair;
     typ = (M ("Type"), IntType(default_unsigned_bit width)); name = n })

let make_field_error (name: string) =
  let n = make_p4String name in
  let open TypeDeclaration in
  let open Type in
  (M("Field"), { annotations = []; typ = (M ("Type"), Error); name = n })

let make_header annote_pairs (name: string) field_pairs =
  let n = make_p4String name in
  let open TypeDeclaration in
  let annotations = List.map make_annotation annote_pairs in
  (* FIX IT: not handled fields that are not bit; hard coded for standard metadata currently*)
  let fields = (make_field_error "parser_err")::
               List.map make_field_bit field_pairs in
  ( M("default varbit"), Header({ annotations; name = n ; fields }))



let default_metadata = make_header [] "meta" []

(* Hard coded default value for metadata *)
let default_standard_metadata =
  let annote_pairs = [("metadata", []); ("name", ["standard_metadata"])] in
  let field_pairs = [([], "ingress_port", 9);
                     ([], "egress_spec", 9);
                     ([], "egress_port", 9);
                     ([], "clone_spec", 32);
                     ([], "instance_type", 32);
                     ([], "drop", 1);
                     ([], "recirculate_port", 16);
                     ([], "packet_length", 32);
                     ([], "enq_timestamp", 32);
                     ([], "enq_qdepth", 19);
                     ([], "deq_timedelta", 32);
                     ([], "deq_qdepth", 19);
                     ([], "ingress_global_timestamp", 48);
                     ([], "egress_global_timestamp", 48);
                     ([], "lf_field_list", 32);
                     ([], "mcast_grp", 16);
                     ([], "resubmit_flag", 32);
                     ([], "egress_rid", 16);
                     ([], "recirculate_flag", 32);
                     ([], "priority", 3);
                    ] in
  make_header annote_pairs "standard_metadata" field_pairs
