(* TODO: Replace Z with 32bit datatype
   everywhere applicable.
*)

Require Import Omega String ZArith Vector.

Local Open Scope vector_scope.
Local Open Scope Z_scope.

Import VectorNotations.

Inductive reg : Set := r3 | r6 | r8.
Definition reg_dec : forall r r' : reg, {r = r'} + {r <> r'}.
Proof. intros. decide equality. Defined.

Inductive bitvec (n : nat): Type :=
| BEndian (v: Vector.t bool n)
| LEndian (v: Vector.t bool n).

Fixpoint bitvecstr {n} (lendian : bool) (v : Vector.t bool n) : string :=
  match lendian, v with
  | false, true :: tl => "1" ++ bitvecstr lendian tl
  | false, false :: tl => "0" ++ bitvecstr lendian tl
  | true, true :: tl =>  bitvecstr lendian tl ++ "1"
  | true, false :: tl => bitvecstr lendian tl ++ "0"
  | _, [] => ""
  end.

Definition bvstr {n} (bv : bitvec n) : string :=
  match bv with
  | BEndian _ v => bitvecstr false v
  | LEndian _ v => bitvecstr true v
  end.

Definition ex1 := BEndian 4 ([true; true; true; false]).
Compute bvstr ex1.
Definition ex2 := LEndian 4 ([true; true; true; false]).
Compute bvstr ex2.

Fixpoint add_bv {n} (v1: bitvec n) (v2: bitvec n) : bitvec n :=
  match (bvunwrap v1), (bvunwrap v2) with
  | , _ => v1
  end.



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