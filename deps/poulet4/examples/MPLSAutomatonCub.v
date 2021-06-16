
(* This time with P4cub syntax! *)
Require Import Poulet4.Examples.MPLS.
Require Import Poulet4.P4cub.Metamorphosis.
Require Import Poulet4.P4automata.Translation.
Require Import Poulet4.P4automata.Compiler.
Require Import Poulet4.P4automata.P4automaton.
Module PR := P4cub.Parser.
Module S := P4cub.Stmt.

Require Import Poulet4.P4defs.
Require Import Poulet4.P4String.

Module MPLSCub.
  Definition decl_env := 
    let decls := ({| tags := NoInfo; str := "mpls_h" |}, mpls_h) :: nil in 
    map (fun '(k, v) => (k, decl_to_type _ v)) decls.
  
  Definition fixed_cub_parser := decl_to_cub _ decl_env MPLSFixedWidthParser.

  Definition fixed_autos := decl_to_autos _ decl_env MPLSFixedWidthParser.
  
  Definition vect_cub_parser := decl_to_cub _ decl_env MPLSVectorizedParser.
  Definition vect_autos := decl_to_autos _ decl_env MPLSVectorizedParser.
  
  (* TODO: the automata compiler doesn't handle fixed_cub_parser, and also vect_autos is extremely slow *)
  (* Compute fixed_autos. *)
  (* Compute vect_autos. *)
  
  Lemma compiled_bisimilar : 
    exists fixed_auto vect_auto, 
      fixed_autos = inl [fixed_auto] /\ 
      vect_autos = inl [vect_auto].
      (* TODO: something about a bisimulation between them *)
  Admitted.
    
End MPLSCub.
  