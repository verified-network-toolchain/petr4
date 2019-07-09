open Value

type packet
type value = packet pre_value

val fixed_width_extract : packet -> value -> packet * value
val var_width_extract : packet -> value -> value -> packet * value
val lookahead : packet -> value -> packet
val packet_length : packet -> value
val advance : packet -> value -> packet
val emit : packet -> value -> packet

val packet_of_list : bool list -> packet
