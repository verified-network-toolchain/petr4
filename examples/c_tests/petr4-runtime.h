// Need to expose GMP operations for each P4 construct

#include <stdlib.h>
#include <stdio.h>
#include <string.h>

typedef char bool;
#define true 1
#define false 0

typedef char bit8;

typedef void* packet_in;
typedef void* packet_out;

void extract(packet_in pkt, void* data, int len);
void emit(packet_out pkt, void* data, int len);
