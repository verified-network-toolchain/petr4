(lang dune 2.8)
(using menhir 2.0)
(name petr4)

(generate_opam_files true)

(package
 (name petr4)
 (version 0.1.2)
 (synopsis     "Petr4: Formal Semantics for the P4 Programming Language")
 (maintainers  "jnfoster@cs.cornell.edu")
 (authors      "Ryan Doenges" "Mina Tahmasbi Arashloo" "Santiago Bautista" "Alexander Chang" "Newton Ni" "Samwise Parkinson" "Rudy Peterson" "Alaia Solko-Breslin" "Amanda Xu" "Nate Foster")
 (homepage     "https://github.com/verified-network-toolchain/petr4")
 (bug_reports  "https://github.com/verified-network-toolchain/petr4")
 (license      "Apache-2.0")
 (depends
   poulet4
   poulet4_Ccomp
   coq-compcert
   alcotest
   bignum
   (ocaml (>= "4.09.1"))
   (dune (>= "1.2"))
   cstruct
   cstruct-sexp
   menhir
   ANSITerminal
   (core (>= "0.15.0"))
   ppx_deriving_yojson
   (ppx_import (>= "0.15.0"))
   (ppx_jane (>= "0.15.0"))
   (ppx_js_style (>= "0.15.0"))
   ppx_let
   (yojson (>= "1.7.0"))
   js_of_ocaml
   js_of_ocaml-lwt
   js_of_ocaml-ppx
   (p4pp (>= "0.1.11"))
   odoc
   (coq (and (<= "8.15.2" ) :build))
 )
)
