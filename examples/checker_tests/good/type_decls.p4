// Program with Type declarations for
// controls, parsers, and package types.

parser Parser<IH>(in IH b, out IH parsedHeaders); // ingress match-action pipeline

control IPipe<T, IH, OH>(in IH inputHeaders,
                         out OH outputHeaders,
                         out T toEgress);

// egress match-action pipeline
control EPipe<T, IH, OH>(in IH inputHeaders,
                         in T fromIngress,
                         out OH outputHeaders);

control Deparser<OH>(in OH outputHeaders);

// package Ingress<T, IH, OH>(Parser<IH> p,
//                            IPipe<T, IH, OH> map,
//                            Deparser<OH> d);

// package Egress<T, IH, OH>(Parser<IH> p,
//                           EPipe<T, IH, OH> map,
//                           Deparser<OH> d);
