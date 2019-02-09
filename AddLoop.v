(* TODO: Replace Z with 32bit datatype
   everywhere applicable.
   TODO: Switch from using strings as register
   names to using an inductive type; will require
   defnining decisional equality for the type.
*)

Require Import List String Omega ZArith.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

Import ListNotations.


Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.
Definition total_map (A : Type) := string -> A.
 Definition t_empty {A : Type} (v : A) : total_map A := (fun _ => v).
Definition t_update {A : Type} (m : total_map A) (x : string) (v : A) :=
  fun x' => if (eqb_string x x') then v else m x'.

Definition reg_state := total_map Z.
(* Inductive reg : Set := | r6. *)

Inductive ins : Set :=
| mov : string -> Z -> ins.

Inductive arm : Set :=
| AArm : list ins -> arm.

Inductive armR : ins -> reg_state -> reg_state -> Prop :=
| EMov : forall st st' reg cnst,
    armR (mov reg cnst) st (t_update st' reg cnst).

(* ====================================================================== *)

Definition AddLoopArm : arm :=
  (AArm [
       (mov "r6" 5)
  ]).



Definition safety1 (st' : netstate) : Prop := st'.(t) >= 0 /\ st'.(r) >= 0.
      
Lemma safety1_holds: forall st st' : netstate,
         (netEvalR st st') ->
         safety1 st'.
Proof.
  intros st st' H. split; induction H; simpl; omega.
Qed.

Definition safety2 (st' : netstate) : Prop :=
  Zlength st'.(c1) + Zlength st'.(c2) + st'.(t) + st'.(r) = 10.

Lemma safety2_holds : forall st st' : netstate,
    (netEvalR st st') ->
    safety2 st'.
Proof.
  intros st st' H. unfold safety2. induction H; simpl;
    try reflexivity;                           (* Initial state *)
    try (rewrite Zlength_cons; omega);         (* Steps 1 and 4 *)
    [destruct (c2 st') | destruct (c1 st')];   (* Steps 2 and 3 *)
      try contradiction;
      (simpl; rewrite Zlength_cons in IHnetEvalR; omega).
Qed.

Theorem safety_holds : forall st st' : netstate,
      (netEvalR st st') -> safety1 st' /\ safety2 st'.
Proof.
  intros st st' H. split;
  [apply (safety1_holds st st') | apply (safety2_holds st st')];
    assumption.
Qed.