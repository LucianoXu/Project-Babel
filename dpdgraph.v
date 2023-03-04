(** dpdgraph.v : can be used to print dependent graphs*)

Require dpdgraph.dpdgraph.


(** Import the modules here. *)
Require Import ?.


(*
    - STEP 1

[Print DependGraph ?.]
    Recursively print the item dependencies of one Coq item.

[Print FileDependGraph ?...? .]
    Print Coq items and dependencies only in the specified models.
    Connections to Coq items outside the modules will be neglected.

*)


Print DependGraph ?.
Print FileDependGraph ?.


(*

    - STEP 2

in bash : 

dpd2dot graph.dpd
dot -Tsvg graph.dot > graph.svg

or 

dpd2dot graph.dpd -without-defs
dot -Tsvg graph.dot > graph.svg


Usage : ./dpd2dot [options]
  -o : name of output file (default: name of input file .dot)
  -with-defs : show everything (default)
  -without-defs : show only Prop objects
  -rm-trans : remove transitive dependencies (default)
  -keep-trans : keep transitive dependencies
  -debug : set debug mode
  -help  Display this list of options
  --help  Display this list of options

*)