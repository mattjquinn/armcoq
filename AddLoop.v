From Coq Require Import ZArith.ZArith Strings.String.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq fintype tuple.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import Ascii.

Definition BITS n := n.-tuple bool.
Notation eta_expand x := (fst x, snd x).
Definition splitlsb {n} (p: BITS n.+1): BITS n*bool := (behead_tuple p, thead p).
Definition joinlsb {n} (pair: BITS n*bool) : BITS n.+1 := cons_tuple pair.2 pair.1.
Notation "'nilB'" := (nil_tuple _).
Coercion singleBit b : BITS 1 := joinlsb (nilB, b).

(* Extend by one bit at the most significant bit. Again, signExtend 1 n does not work
   because BITS (n+1) is not definitionally equal to BITS n.+1  *)
Fixpoint joinmsb {n} : bool * BITS n -> BITS n.+1 :=
  if n is _.+1
  then fun p => let (hibit, p) := p in
                let (p,b) := splitlsb p in joinlsb (joinmsb (hibit, p), b)
  else fun p => joinlsb (nilB, p.1).
Definition joinmsb0 {n} (p: BITS n) : BITS n.+1 := joinmsb (false,p).

(* Special case: split at the most significant bit.
   split 1 n doesn't work because it requires BITS (n+1) not BITS n.+1 *)
Fixpoint splitmsb {n} : BITS n.+1 -> bool * BITS n :=
  if n is _.+1
  then fun p => let (p,b) := splitlsb p in let (c,r) := splitmsb p in (c,joinlsb(r,b))
  else fun p => let (p,b) := splitlsb p in (b,p).
Arguments splitmsb : simpl never.

Definition dropmsb {n} (p: BITS n.+1) := (splitmsb p).2.

Definition fullAdder carry b1 b2 : bool * bool :=
    match carry, b1, b2 with
    | false, false, false => (false, false)
    | true, false, false | false, true, false | false, false, true => (false, true)
    | true, true, false | false, true, true | true, false, true => (true, false)
    | true, true, true => (true, true)
    end.

(* Add with carry, producing a word one bit larger than the inputs *)
Fixpoint adcBmain n carry : BITS n -> BITS n -> BITS n.+1 :=
  if n is _.+1 then
    fun p1 p2 => let (p1,b1) := eta_expand (splitlsb p1) in
                 let (p2,b2) := eta_expand (splitlsb p2) in
                 let (carry',b) := fullAdder carry b1 b2 in
                   joinlsb (adcBmain carry' p1 p2, b)
  else fun _ _ => singleBit carry.
Arguments adcBmain n carry a b : simpl never.

Definition adcB {n} carry (p1 p2: BITS n) := splitmsb (adcBmain carry p1 p2).

Fixpoint fromNat {n} m : BITS n :=
  if n is _.+1
  then joinlsb (fromNat m./2, odd m)
  else nilB.
Notation "# m" := (fromNat m) (at level 0).
Arguments fromNat n m : simpl never.

Definition toNat {n} (p: BITS n) := foldr (fun (b:bool) n => b + n.*2) 0 p.

Definition charToBit c : bool := ascii_dec c "1".

Fixpoint fromBin s : BITS (length s) :=
  if s is String c s
  then joinmsb (charToBit c, fromBin s) else #0.

Notation "#b y" := (fromBin y) (at level 0).

Check #0.
Check #b"0111".

Check adcBmain false.
Definition a1 := #b"111".
Definition a2 := #b"001".
Compute (toNat a1).
Compute (toNat a2).
Definition res := (adcBmain false a1 a2).
Compute (toNat res).
Compute (fst (splitmsb res)).
Compute (splitmsb res).
Example e1 : (adcBmain false #b"01" #b"01") = (fromNat 2).
Proof.
  simpl. unfold adcBmain. unfold fullAdder. simpl.
  unfold joinlsb. simpl. unfold cons_tuple. reflexivity.
Qed.


Inductive Reg : Set := r1 | r2 | r3 | r6 | r8.
Definition reg_dec : forall r r' : Reg, {r = r'} + {r <> r'}.
Proof. intros. decide equality. Defined.

Definition total_map (A : Type) := Reg -> A.
Definition t_empty {A : Type} (v : A) : total_map A := (fun _ => v).
Definition beq_reg x y :=
  if reg_dec x y then true else false.
Definition t_update {A : Type} (m : total_map A) (x : Reg) (v : A) :=
  fun x' => if (beq_reg x x') then v else m x'.
Theorem reg_dec_refl : forall x, true  = reg_dec x x.
Proof.
  intros x. induction x; reflexivity.
Qed.
Lemma t_update_eq : forall A (m : total_map A) x v,
  (t_update m x v) x = v.
Proof. intros. unfold t_update.
       unfold beq_reg.
       rewrite <- reg_dec_refl. reflexivity.
Qed.
Theorem beq_reg_true_iff : forall x y,
  beq_reg x y = true <-> x = y.
Proof.
  intros [] []; split; try reflexivity; try intro H; inversion H.
Qed.
Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - unfold not in H. exfalso. apply H. reflexivity. reflexivity.
Qed.
Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  intros b. split.
  - apply not_true_is_false.
  - intros H. rewrite H. intros H'. inversion H'.
Qed.
Theorem beq_reg_false_iff : forall x y,
    beq_reg x y = false <-> x <> y.
    intros x y. rewrite <- beq_reg_true_iff.
  rewrite not_true_iff_false. reflexivity.
Qed.
Theorem t_update_neq : forall (X : Type) v x1 x2 (m : total_map X),
  x1 <> x2 -> (t_update m x1 v) x2 = m x2.
Proof.
  intros. unfold t_update.  apply beq_reg_false_iff in H. 
  rewrite H. reflexivity.
Qed.

Definition reg_state := total_map (BITS 32).

Inductive ins : Type :=
| seq : ins -> ins -> ins
| add : Reg -> Reg -> Reg -> ins
| mov : Reg -> (BITS 32) -> ins.

Notation "i1 ;; i2" :=
  (seq i1 i2) (at level 80, right associativity).

Inductive armR : ins -> reg_state -> reg_state -> Prop :=
| ESeq : forall i1 i2 st st' st'',
    armR i1 st st' ->
    armR i2 st' st'' ->
    armR (i1 ;; i2) st st''
| EAdd : forall rd rn rop2 st,
    armR (add rd rn rop2) st (t_update st rd
                               (snd (splitmsb (adcBmain false (st rn) (st rop2)))))
| EMov : forall st reg cnst,
    armR (mov reg cnst) st (t_update st reg cnst).

(* ====================================================================== *)

Definition AddLoopArm : ins :=
  (mov r1 (fromNat 5)) ;;
  (mov r3 (fromNat 0)) ;;
  (mov r2 (fromNat 1)) ;;
  (add r6 r1 r2).
  
Lemma finalstate8: forall st st' : reg_state,
         (armR AddLoopArm st st') ->
         (toNat (st' r6)) = 6.
Proof.
  unfold AddLoopArm. intros. inversion H.
  inversion H5. inversion H11. inversion H14.
  inversion H2. inversion H8. subst.
  inversion H17. rewrite t_update_eq.
  rewrite t_update_neq. rewrite t_update_eq.
  rewrite t_update_neq. rewrite t_update_eq.
  
  
  reflexivity.
  


  inversion H. subst.
  inversion H5. subst. inversion H7. subst. inversion H9.
  subst. inversion H4. subst.