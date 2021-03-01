external setup_raw : string -> int = "caml_setup_raw"

external recv_raw : int -> string = "caml_recv_raw"

external send_raw : int -> unit = "caml_send_raw"
