open Core

module IO : Common.DriverIO = struct
  let colorize colors s = ANSITerminal.sprintf colors "%s" s
  let red s = colorize [ANSITerminal.red] s
  let green s = colorize [ANSITerminal.green] s
  
  let preprocess include_dirs p4file =
    let cmd =
      String.concat ~sep:" "
        (["cc"] @
           (List.map include_dirs ~f:(Printf.sprintf "-I%s") @
              ["-undef"; "-nostdinc"; "-E"; "-x"; "c"; p4file])) in
    let in_chan = Core_unix.open_process_in cmd in
    let str = In_channel.input_all in_chan in
    let _ = Core_unix.close_process_in in_chan in
    str

  let open_file path =
    Out_channel.create path

  let close_file ochan =
    Out_channel.close ochan
end

module Driver = Common.MakeDriver(IO)
