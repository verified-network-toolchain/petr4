extern packet_in {
}

parser filter(packet_in packet, out bool drop);
