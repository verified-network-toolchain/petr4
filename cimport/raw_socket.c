#define CAML_NAME_SPACE
#include "caml/mlvalues.h"
#include <stdio.h>
#include <sys/socket.h>
#include <arpa/inet.h>
#include <linux/if_packet.h>
#include <netinet/ether.h>
#include <net/if.h>
#include <unistd.h>
#include <string.h>

CAMLprim value caml_setup_raw(value addr) {
    char* ifname = String_val(addr);
    int sd;
    sd = socket(AF_PACKET, SOCK_RAW, htons(ETH_P_ALL));
    if (sd < 0) {
        perror("socket creation error");
    }
    printf("%s interface index: %d\n", iface_name, addr.sll_ifindex);

    addr.sll_family = AF_PACKET;
    addr.sll_halen = 6;
    addr.sll_hatype = ARPHRD_VOID;
    
    if (bind(sd, (struct sockaddr*) &addr, sizeof(addr)) == -1) {
        perror("bind error");
    }

    return Int_val(sd);
}

CAMLprim value caml_recv_raw {
    perror("unimplemented");
}

CAMLprim value caml_send_raw {
    perror("unimplemented");
}
