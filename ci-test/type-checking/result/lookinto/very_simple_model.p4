/petr4/ci-test/type-checking/testdata/p4_16_samples/very_simple_model.p4
\n
/*
Copyright 2013-present Barefoot Networks, Inc.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/

#ifndef _SIMPLE_MODEL_P4_
#define _SIMPLE_MODEL_P4_

#include <core.p4>

/* Various constants and structure definitions */
/* ports are represented using 4-bit values */
typedef bit<4> PortId;
/* only 8 ports are "real" */
const PortId REAL_PORT_COUNT = 4w8;  // 4w8 is the number 8 in 4 bits
/* metadata accompanying an input packet */
struct InControl {
    PortId inputPort;
}

/* special input port values */
const PortId RECIRCULATE_IN_PORT = 0xD;
const PortId CPU_IN_PORT = 0xE;
/* metadata that must be computed for outgoing packets */
struct OutControl {
    PortId outputPort;
}

/* special output port values for outgoing packet */
const PortId DROP_PORT = 0xF;
const PortId CPU_OUT_PORT = 0xE;
const PortId RECIRCULATE_OUT_PORT = 0xD;
/* Prototypes for all programmable blocks */
/**
 * Programmable parser.
 * @param <H> type of headers; defined by user
 * @param b input packet
 * @param parsedHeaders headers constructed by parser
 */
parser Parser<H>(packet_in b,
                 out H parsedHeaders);
/**
 * Match-action pipeline
 * @param <H> type of input and output headers
 * @param headers headers received from the parser and sent to the deparser
 * @param parseError error that may have surfaced during parsing
 * @param inCtrl information from target, accompanying input packet
 * @param outCtrl information for target, accompanying output packet
 */
control Pipe<H>(inout H headers,
                in error parseError, // parser error
                in InControl inCtrl, // input port
                out OutControl outCtrl); // output port
/**
 * Switch deparser.
 * @param <H> type of headers; defined by user
 * @param b output packet
 * @param outputHeaders headers for output packet
 */
control Deparser<H>(inout H outputHeaders,
                    packet_out b);

/**
 * Top-level package declaration – must be instantiated by user.
 * The arguments to the package indicate blocks that
 * must be instantiated by the user.
 * @param <H> user-defined type of the headers processed.
 */
package VSS<H>(Parser<H> p,
               Pipe<H> map,
               Deparser<H> d);

// Target-specific objects that can be instantiated

// Checksum unit
extern Ck16 {
    Ck16();
    void clear();           // prepare unit for computation
    void update<T>(in T data); // add data to checksum
    bit<16> get(); // get the checksum for the data added since last clear
}

#endif
************************\n******** petr4 type checking result: ********\n************************\n
error {
  NoError, PacketTooShort, NoMatch, StackOutOfBounds, HeaderTooShort,
  ParserTimeout, ParserInvalidArgument
}
extern packet_in {
  void extract<T>(out T hdr);
  void extract<T0>(out T0 variableSizeHeader,
                   in bit<32> variableFieldSizeInBits);
  T1 lookahead<T1>();
  void advance(in bit<32> sizeInBits);
  bit<32> length();
}

extern packet_out {
  void emit<T2>(in T2 hdr);
}

extern void verify(in bool check, in error toSignal);
@noWarn("unused")
action NoAction() { 
}
match_kind {
  exact, ternary, lpm
}
typedef bit<4> PortId;
const PortId REAL_PORT_COUNT = 4w8;
struct InControl {
  PortId inputPort;
}
const PortId RECIRCULATE_IN_PORT = 13;
const PortId CPU_IN_PORT = 14;
struct OutControl {
  PortId outputPort;
}
const PortId DROP_PORT = 15;
const PortId CPU_OUT_PORT = 14;
const PortId RECIRCULATE_OUT_PORT = 13;
parser Parser<H> (packet_in b, out H parsedHeaders);
control Pipe<H3>
  (inout H3 headers,
   in error parseError,
   in InControl inCtrl,
   out OutControl outCtrl);
control Deparser<H4> (inout H4 outputHeaders, packet_out b);
package VSS<H5> (Parser<H5> p, Pipe<H5> map, Deparser<H5> d);
extern Ck16 {
  Ck16();
  void clear();
  void update<T6>(in T6 data);
  bit<16> get();
}


