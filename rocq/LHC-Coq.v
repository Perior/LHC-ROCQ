(*
  Formal Verification of Successive Running Sums (SRS) in Coq
  Translated from HOL4 proofs from:
  "Formal Verification of Real-Time Data Processing of the LHC Beam Loss Monitoring System"
*)

Require Import Arith Lia List.
Import ListNotations.
Require Import Coq.Program.Wf.

Definition tap (n x : nat) : nat :=
  match n, x with
  | 0, 0 => 0         | 0, _ => 0
  | 1, 0 => 1 - 1     | 1, _ => 2 - 1
  | 2, 0 => 8 - 1     | 2, _ => 16 - 1
  | 3, 0 => 32 - 1    | 3, _ => 128 - 1
  | 4, 0 => 32 - 1    | 4, _ => 256 - 1
  | 5, 0 => 16 - 1    | 5, _ => 64 - 1
  | 6, 0 => 32 - 1    | 6, _ => 128 - 1
  | _, _ => 0
  end.

Definition input (n : nat) : (nat * nat) :=
  match n with
  | 0 => (0, 0)
  | 1 => (0, 0) | 2 => (0, 0) | 3 => (1, 1)
  | 4 => (3, 0) | 5 => (4, 0) | 6 => (4, 1)
  | _ => (n - 1, 0)
  end.

Lemma input_earlier : forall n,
  0 < n -> fst (input n) < n.
Proof.
  intros n H.
  destruct n; simpl; try lia. (* n = 1 *)
  destruct n; simpl; try lia. (* n = 2 *)
  destruct n; simpl; try lia. (* n = 3 *)
  destruct n; simpl; try lia. (* n = 4 *)
  destruct n; simpl; try lia. (* n = 5 *)
  destruct n; simpl; try lia. (* n = 6 *)
  destruct n; simpl; try lia. (* n > 6 *)
Qed.

Fixpoint delay_aux (fuel : nat) (n : nat) : nat :=
  match fuel with
  | 0 => 1
  | S f =>
      match n with
      | 0 => 1
      | _ =>
          let '(a, b) := input n in
          delay_aux f a * S (tap a b)
      end
  end.

Definition delay (n : nat) : nat := delay_aux n n.

(* 
  Compute S (tap (fst (input 1)) (snd (input 1))).
  Compute delay 6. 
*)

Fixpoint delay_sum_aux (fuel n : nat) : nat :=
  match fuel with
  | 0 => 0
  | S f =>
      match n with
      | 0 => 0
      | _ =>
          let '(a, _) := input n in
          delay a + delay_sum_aux f a
      end
  end.

Definition delay_sum (n : nat) : nat :=
  delay_sum_aux n n.

  (* Compute delay 4.
  Compute delay 3.
  Compute delay 1.
  Compute delay 0.
  Compute delay_sum 6. *)

Definition update_time (n t : nat) : bool :=
  (t mod delay n) =? 0.
(* Compute update_time 3 10. *)

Section SliceDef.

Variable output : (nat -> nat) -> nat -> nat -> nat -> nat.
Variable SR : (nat -> nat) -> nat -> nat -> nat -> nat.

Program Fixpoint source (D : nat -> nat) (n m t : nat) {measure m} : nat :=
  match m with
  | 0 =>
      let '(n', x) := input n in
      output D n' x t
  | S m' => SR D n m' t
  end.

Program Fixpoint SR_def (D : nat -> nat) (n m t : nat) {measure t} : nat :=
  match t with
  | 0 => 0
  | S t' =>
      if update_time n (S t') then
        source D n m t'
      else
        SR_def D n m t'
  end.

Program Fixpoint output_def (D : nat -> nat) (n x t : nat) {measure t} : nat :=
  match t with
  | 0 =>
      match n with
      | 0 => D 0
      | _ => 0
      end
  | S t' =>
      if update_time n (S t') then
        output_def D n x t' + source D n 0 t' - SR D n (tap n x) t'
      else
        output_def D n x t'
  end.

End SliceDef.

Compute output_def 1 0 1 2.