#include <gmp.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

typedef char bool;
#define true 1
#define false 0

typedef char bit;

typedef void *packet_in;
typedef void *packet_out;

void extract(packet_in pkt, void *data, int len);
void emit(packet_out pkt, void *data, int len);
