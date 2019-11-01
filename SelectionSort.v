Require Export Coq.Init.Datatypes.
From sorting Require Export Utils.
From sorting Require Export Sorted.
Export ListNotations.


(** * Definition  *)

Fixpoint select (x: nat) (l: list nat) : nat * list nat :=
  match l with
  |  nil => (x, nil)
  |  h::t => if x <=? h
                 then let (j, l') := select x t in (j, h::l')
                 else let (j, l') := select h t in (j, x::l')
  end.

Fixpoint selsort l n {struct n} :=
  match l, n with
  | x::r, S n' => let (y,r') := select x r
                 in y :: selsort r' n'
  | nil, _ => nil
  | _::_, O => nil
  end.

Definition selection_sort l :=
  selsort l (length l).


(** * Correctness goal  *)

Definition selection_sort_correct : Prop :=
  is_a_sorting_algorithm selection_sort.


(** * Theorems with permutations *)

Lemma select_perm: forall x l,
  let (y, r) := select x l in Permutation (x :: l) (y :: r).
Proof.
  intros x l; revert x.
  induction l; intros; simpl in *. {
    apply Permutation_refl.
  } {
    unfold select.
    bdestruct (x <=? a); fold select. {
      specialize (IHl x).
      destruct (select x l) eqn:Seq.
      apply perm_trans with (a :: n :: l0). {
        Search Permutation.
        apply Permutation_sym.
        apply perm_trans with (a :: x :: l). {
          now apply perm_skip.
        } {
          apply perm_swap.
        }
      } {
        apply perm_swap.
      }
    } {
      specialize (IHl a).
      destruct (select a l) eqn:Seq.
      apply perm_trans with (x :: n :: l0). {
        now apply perm_skip.
      } {
        apply perm_swap.
      }
    }
  }
Qed.

Lemma selsort_perm:
  forall n l, length l = n -> Permutation l (selsort l n).
Proof.
  induction n. {
    intros.
    destruct l. {
      apply perm_nil.
    } {
      inversion H.
    }
  } {
    intros.
    destruct l. {
      intros.
      inversion H.
    } {
      simpl.
      destruct (select n0 l) eqn:Seq.
      apply perm_trans with (n1 :: l0). {
        assert (let (y, r) := select n0 l in Permutation (n0 :: l) (y :: r)). {
          apply (select_perm n0 l).
        }
        destruct (select n0 l).
        inv Seq.
        apply H0.
      } {
        apply perm_skip.
        apply IHn.
        assert (length (n0::l) = (length (n1::l0))). {
          apply Permutation_length.
          assert (let (y, r) := select n0 l in Permutation (n0 :: l) (y :: r)). {
            apply (select_perm n0 l).
          }
          destruct (select n0 l).
          inv Seq.
          apply H0.
        }
        inv H0.
        inv H.
        reflexivity.
      }
    }
  }
Qed.

Theorem selection_sort_perm:
  forall l, Permutation l (selection_sort l).
Proof.
  unfold selection_sort.
  intros.
  apply selsort_perm.
  reflexivity.
Qed.


(** * [select] selects the smallest element of a list *)