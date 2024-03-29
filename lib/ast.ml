type qualified_name = string

type id = string
type number = string
type port = string
type packet_data = string
type expect_data = string


type arg = id * number

type action = qualified_name * arg list

type number_or_lpm =
  | Slash of number * number
  | Num of number

type match_ = qualified_name * number_or_lpm

type id_or_index =
  | Id of string
  | Index of number

type logical_cond =
  | Eqeq
  | Neq
  | Leq
  | Le
  | Geq
  | Gt

type count_type =
  | Bytes
  | Packets

type statement =
  | Wait
  | Remove_all
  | Expect of port * expect_data option
  | Packet of port * packet_data
  | No_packet
  | Add of qualified_name * int option * match_ list * action * id option
  | Set_default of qualified_name * action
  | Check_counter of id * id_or_index * (count_type option * logical_cond * number)
