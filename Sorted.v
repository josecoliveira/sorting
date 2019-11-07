Require Export Coq.Lists.List.
Require Export Permutation.
From sorting Require Export Utils.

Inductive sorted: list nat -> Prop := 
  | sorted_nil: sorted nil
  | sorted_1: forall x, sorted (x::nil)
  | sorted_cons: forall x y l, x <= y -> sorted (y::l) -> sorted (x::y::l).

Definition is_a_sorting_algorithm (f: list nat -> list nat) :=
  forall al, Permutation al (f al) /\ sorted (f al).