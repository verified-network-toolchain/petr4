#include "petr4-runtime.h"

void extract(packet_in pkt, void *data, int len)
{
  ((char *)data)[0] = 1;
  memcpy(data + 1, pkt, len / 8);
}
void emit(packet_in pkt, void *data, int len)
{
  if (((char *)data)[0])
  {
    memcpy(pkt, data + 1, len / 8);
  }
}
