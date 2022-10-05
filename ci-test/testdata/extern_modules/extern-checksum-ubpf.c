#include  "test.h"

/*
 * This file implements sample C extern function. It contains definition of two C extern functions:
 *
 * 1. bit<16> incremental_checksum(in bit<16> csum, in bit<32> old, in bit<32> new)
 * 2. bool verify_ipv4_checksum(in IPv4_h iphdr)
 */

inline uint16_t csum_fold(uint32_t csum) {
    uint32_t r = csum << 16 | csum >> 16;
    csum = ~csum;
    csum -= r;
    return (uint16_t)(csum >> 16);
}

inline uint32_t csum_unfold(uint16_t csum) {
    return (uint32_t) csum;
}

inline uint32_t csum32_add(uint32_t csum, uint32_t addend) {
    uint32_t res = csum;
    res += addend;
    return (res + (res < addend));
}

inline uint32_t csum32_sub(uint32_t csum, uint32_t addend) {
    return csum32_add(csum, ~addend);
}

inline uint16_t csum_uint32_t(uint16_t csum, uint32_t from, uint32_t to) {
    uint32_t tmp = csum32_sub(~csum_unfold(csum), from);
    return csum_fold(csum32_add(tmp, to));
}

/**
 * Sample C extern function.
 *
 * This function implements method to compute checksum incrementally. Altough it is useless for eBPF (as p4c-ebpf
 * does not allow for writes to packets), this function can be used for XDP or uBPF.
 * @param csum Current value of checksum field.
 * @param old Old value of a field that has been changed.
 * @param new New value of a field that has been changed.
 * @return Calculated checksum.
 */
uint16_t incremental_checksum(uint16_t csum, uint32_t old, uint32_t new) {
    uint32_t res = csum_uint32_t(csum, old, new);
    return res;
}

/**
 * This function implements method to verify IP checksum. It shows how to write C extern function for P4 program.
 * @param iphdr Structure representing IP header. The IP header is generated by the P4 compiler.
 * @return True if checksum is correct.
 */
uint8_t verify_ipv4_checksum(struct IPv4_h iphdr)
{
    uint8_t correct = 0;
    uint32_t checksum = htons(((uint16_t) iphdr.version << 12) | ((uint16_t) iphdr.ihl << 8) | (uint16_t) iphdr.diffserv);
    checksum += htons(iphdr.totalLen);
    checksum += htons(iphdr.identification);
    checksum += htons(((uint16_t) iphdr.flags << 13) | iphdr.fragOffset);
    checksum += htons(((uint16_t) iphdr.ttl << 8) | (uint16_t) iphdr.protocol);
    checksum += htons(iphdr.hdrChecksum);
    uint32_t srcAddr = htonl(iphdr.srcAddr);
    uint32_t dstAddr = htonl(iphdr.dstAddr);
    checksum += (srcAddr >> 16) + (uint16_t) srcAddr;
    checksum += (dstAddr >> 16) + (uint16_t) dstAddr;

    uint16_t res = __constant_ntohs(~((checksum & 0xFFFF) + (checksum >> 16)));

    if (res == 0)
        correct = 1;
    return correct;
}

