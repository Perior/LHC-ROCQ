(*
  Formal Verification of Successive Running Sums (SRS) in Coq
  Translated from HOL4 proofs from:
  "Formal Verification of Real-Time Data Processing of the LHC Beam Loss Monitoring System"


  Theorem 1. 
  Theorem 2. better_max_error
  Theorem 3. max_error_eq / max_relative_error
*)

Require Import Arith Lia List.
Import ListNotations.
Require Import Program.Wf.
Require Import Arith.Arith.
Require Import Relations.Relation_Definitions.
Require Import Wellfounded.

From Equations Require Import Equations.
Set Equations With UIP.

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

(* Section SliceDef.

Variable output_var : (nat -> nat) -> nat -> nat -> nat -> nat.
Variable SR_var : (nat -> nat) -> nat -> nat -> nat -> nat.

Program Fixpoint source (D : nat -> nat) (n m t : nat) {measure m} : nat :=
  match m with
  | 0 =>
      let '(n', x) := input n in
      output_var D n' x t
  | S m' => SR_var D n m' t
  end.
  Next Obligation. apply well_founded_ltof. Defined.

Program Fixpoint SR (D : nat -> nat) (n m t : nat) {measure t} : nat :=
  match t with
  | 0 => 0
  | S t' =>
      if update_time n (S t') then
        source D n m t'
      else
        SR D n m t'
  end.
  Next Obligation. apply well_founded_ltof. Defined.

Program Fixpoint output (D : nat -> nat) (n x t : nat) {measure t} : nat :=
  match t with
  | 0 =>
      match n with
      | 0 => D 0
      | _ => 0
      end
  | S t' =>
      if update_time n (S t') then
        output D n x t' + source D n 0 t' - SR D n (tap n x) t'
      else
        output D n x t'
  end.
  Next Obligation. apply well_founded_ltof. Defined.

End SliceDef. *)

Section SliceDef.

Inductive slice_prot :=
  | Src : (nat -> nat) -> nat -> nat -> nat -> slice_prot
  | SRr : (nat -> nat) -> nat -> nat -> nat -> slice_prot
  | Out : (nat -> nat) -> nat -> nat -> nat -> slice_prot.

Definition slice_measure (d : slice_prot) : (nat * (nat * (nat * nat))) :=
  match d with
  | Src D n m t  => (n, (m, (t, 3)))
  | SRr D n m t  => (n, (m, (t, 2)))
  | Out D n x t  => (n, (tap n x, (t, 1)))
  end.

Definition slice_lt : _ -> _ -> Prop :=
  lexprod nat (nat * (nat * nat))
    lt (lexprod nat (nat * nat)
          lt (lexprod nat nat lt lt)).

Instance slice_lt_wf : WellFounded (fun a b => slice_lt (slice_measure a) (slice_measure b)).
Proof.
  apply wf_inverse_image.
  repeat apply wf_lexprod; apply lt_wf.
Qed.

Equations? slice (d : slice_prot) : nat by wf d (fun a b => slice_lt (slice_measure a) (slice_measure b)) :=
slice (Src D n m t) :=
  match m with
  | 0 =>
      let (n', x) := input n in
      slice (Out D n' x t)
  | S m' =>
      slice (SRr D n m' t)
  end;
  
slice (SRr D n m t) :=
  match t with
  | 0 => 0
  | S t' =>
      if update_time n (S t')
      then slice (Src D n m t')
      else slice (SRr D n m t')
  end;

slice (Out D n x t) :=
  match t with
  | 0 =>
      if Nat.eqb n 0 then D 0 else 0
  | S t' =>
      if update_time n (S t')
      then slice (Out D n x t') + slice (Src D n 0 t') - slice (SRr D n (tap n x) t')
      else slice (Out D n x t')
  end.
Proof.
  all: try (unfold slice_measure, slice_lt; simpl).

  - (* slice Src D n 0 t → Out D n' x t *)
    destruct (input n) as [n' x] eqn:Hinput.
    assert (n' < n) by (apply input_earlier; lia).
    apply lexprod_left; assumption.

  - (* slice Src D n (S m') t → SRr D n m' t *)
    apply lexprod_right, lexprod_left. lia.

  - (* slice SRr D n m (S t') when update_time = true → Src D n m t' *)
    apply lexprod_right, lexprod_right, lexprod_left. lia.

  - (* slice SRr D n m (S t') when update_time = false → SRr D n m t' *)
    apply lexprod_right, lexprod_right, lexprod_left. lia.

  - (* slice Out D n x (S t') when update_time = true → Out D n x t' *)
    apply lexprod_right, lexprod_right, lexprod_right. lia.

  - (* slice Out D n x (S t') when update_time = true → Src D n 0 t' *)
    apply lexprod_right, lexprod_left. lia.

  - (* slice Out D n x (S t') when update_time = true → SRr D n (tap n x) t' *)
    apply lexprod_right, lexprod_right, lexprod_left. lia.

  - (* slice Out D n x (S t') when update_time = false → Out D n x t' *)
    apply lexprod_right, lexprod_right, lexprod_right. lia.
Qed.

Definition source (D : nat -> nat) n m t := slice (Src D n m t).
Definition SR     (D : nat -> nat) n m t := slice (SRr D n m t).
Definition output (D : nat -> nat) n x t := slice (Out D n x t).

End SliceDef.
