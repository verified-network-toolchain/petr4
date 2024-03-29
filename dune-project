(lang dune 2.8)
(using menhir 2.0)
(using coq 0.2)
(name petr4)

(generate_opam_files true)

(package
 (name petr4)
 (version 0.1.2)
 (synopsis     "Petr4: Formal Semantics for the P4 Programming Language")
 (maintainers  "jnfoster@cs.cornell.edu")
 (authors      "Ryan Doenges"
               "Mina Tahmasbi Arashloo"
               "Santiago Bautista" "Alexander Chang"
               "Newton Ni"
               "Samwise Parkinson"
               "Rudy Peterson"
               "Alaia Solko-Breslin"
               "Amanda Xu"
               "Nate Foster")
 (homepage     "https://github.com/verified-network-toolchain/petr4")
 (bug_reports  "https://github.com/verified-network-toolchain/petr4")
 (license      "Apache-2.0")
 (depends
   conf-gmp
   conf-m4
   poulet4
   poulet4_Ccomp
   alcotest
   bignum
   (ocaml (>= "4.09.1"))
   (dune (>= "1.2"))
   cstruct
   cstruct-sexp
   menhir
   ANSITerminal
   (core (and (>= "v0.15.0") (< "v0.16.0")))
   (pp (>= "1.1.2"))
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
   (coq (and (>= "8.15.0" ) (< "8.17.0") :build))))

(package
 (name poulet4)
 (version 0.1.0)
 (synopsis     "Poulet4: Petr4 in Coq")
 (maintainers  "jnfoster@cs.cornell.edu")
 (authors      "Ryan Doenges"
               "Rudy Peterson"
               "Qinshi Wang"
               "Molly Pan"
               "Shengyi Wang"
               "John Chen"
               "Eric Hayden Campbell"
               "Parisa Ataei"
               "Andrew Appel"
               "Nate Foster" )
 (homepage     "https://github.com/verified-network-toolchain/petr4")
 (bug_reports  "https://github.com/verified-network-toolchain/petr4")
 (license      "Apache-2.0")
 (depends
   bignum
  (dune :build)
  (coq (and (>= "8.15.0") (< "8.17.0") :build))
  (coq-equations :build)
  (coq-record-update :build)
  (coq-compcert :build)
  (coq-vst-zlist :build)
  (coq-stdpp :build)))

(package
 (name poulet4_Ccomp)
 (version 0.1.0)
 (synopsis "Poulet4-Ccompiler: P4 to C Compiler in Coq")
 (maintainers "jnfoster@cs.cornell.edu")
 (authors "John Chen"
          "Nate Foster"
          "Natalie Isak")
 (homepage     "https://github.com/verified-network-toolchain/petr4")
 (bug_reports  "https://github.com/verified-network-toolchain/petr4")
 (license      "Apache-2.0")
 (depends
   bignum
   poulet4
   zarith
   coq-compcert
   (coq (and (>= "8.15.0") (< "8.17.0") :build))
   (coq-equations :build)))
