open Value

type packet
type value = packet pre_value

val fixed_width_extract : packet -> value -> packet * value
val emit : packet -> value -> packet
val packet_of_list : bool list -> packet
