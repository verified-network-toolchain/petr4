/* -*- P4_16 -*- */

/**
 * Copyright (c) Intel Corporation
 * SPDX-License-Identifier: CC-BY-ND-4.0
 */

/* https://github.com/barefootnetworks/Open-Tofino/blob/master/share/p4c/p4include/tna.p4 */

#if __TARGET_TOFINO__ == 1
#include "tofino1arch.p4"
#else
#include "tofino1arch.p4"
// #error Target does not support tofino native architecture
#endif
