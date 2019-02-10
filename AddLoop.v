(* TODO: Replace Z with 32bit datatype
   everywhere applicable.
*)

Require Import List String Omega ZArith.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

Import ListNotations.

Inductive reg : Set := r3 | r6 | r8.
Definition reg_dec : forall r r' : reg, {r = r'} + {r <> r'}.
Proof. intros. decide equality. Defined.


Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.
Definition total_map (A : Type) := reg -> A.
 Definition t_empty {A : Type} (v : A) : total_map A := (fun _ => v).
Definition t_update {A : Type} (m : total_map A) (x : reg) (v : A) :=
  fun x' => if (reg_dec x x') then v else m x'.

Definition reg_state := total_map Z.

Inductive ins : Type :=
| seq : ins -> ins -> ins
| mov : reg -> Z -> ins.

Notation "i1 ;; i2" :=
  (seq i1 i2) (at level 80, right associativity).

Inductive armR : ins -> reg_state -> reg_state -> Prop :=
| ESeq : forall i1 i2 st st' st'',
    armR i1 st st' ->
    armR i2 st' st'' ->
    armR (i1 ;; i2) st st''
| EMov : forall st st' reg cnst,
    armR (mov reg cnst) st (t_update st' reg cnst).

(* ====================================================================== *)

Definition AddLoopArm : ins :=
  (mov r6 5) ;;
  (mov r3 2) ;;
  (mov r6 8).
  
Lemma finalstate8: forall st st' : reg_state,
         (armR AddLoopArm st st') ->
         st' r6 = 8.
Proof.
  unfold AddLoopArm. intros. inversion H. subst.
  inversion H5. subst. inversion H7. subst. unfold t_update.
  reflexivity.
Qed.