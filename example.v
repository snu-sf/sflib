(* *********************************************************************)
(*                                                                     *)
(*           Software Foundations Laboratory's Lemmas & Tactic         *)
(*               based on Viktor and Gil's lemmas & tactic             *)
(*                                                                     *)
(* *********************************************************************)

(** This file contains example usages of sflib. *)
Require Import "./sflib".

(** list notations *)
Check [1].
Check [1; 2].
Check [1; 2; 3].

(** negation *)
Check ~True.
(* Check (~nat:Type). *) (* TODO: why ~ is defined? *)

(** composition **)
Definition mul2 l := l * 2.
Definition add3 l := l + 3.
Definition mul2_then_add3 := add3 <*> mul2.
Goal mul2_then_add3 0 = 3. Proof. reflexivity. Qed.

(** coercion of bools into Prop *)
Goal true. Proof. reflexivity. Qed.

(** catch-all tactics: done, edone, by X, clarify, vauto *)
Goal 2 * 3 = 6.
Proof. done.
Restart. edone. (* evariable version *)
Qed.
Goal exists x, x * 3 = 6.
Proof. by exists 2. (* by X = X; done *) Qed.

(** inv & hinv: inversion *)
Module Example_Inv.
  Inductive p: forall (n:nat), Prop :=
  | p0: p 0
  | p3: p 3.

  Goal forall n, p n -> n = 0 \/ n = 3.
  Proof. i. inv H. auto. auto.
  Restart. i. hinv H. auto. auto.
  Qed.
End Example_Inv.

(** simpls, ins *)
Goal (2 * 3 = 5 \/ 3 * 4 = 11 -> 4 * 5 = 19).
Proof. simpls.
Restart. ins. destruct H. inv H. inv H.
Qed.

(** <<x:X>>, des, splits *)
Module Example_Des.
  Variable (P Q R:Prop).

  Goal <<PQ: P -> Q>> /\ <<QR: Q -> R>> -> <<PR: P -> R>>.
  Proof.
    i. des. auto.
  Qed.

  Goal <<PR: P -> R>> /\ <<QR: Q -> R>> ->
       (<<p: P>> \/ <<q: Q>>) -> R.
  Proof.
    i. des. auto. auto.
  Qed.

  Goal <<PQ: P -> Q>> /\ <<PR: P -> R>> ->
       <<p: P>> ->
       <<q: Q>> /\ <<r: R>>.
  Proof.
    i. des. splits. auto. auto. (* cf: esplits *)
  Qed.
End Example_Des.

(** case tacticals *)
Goal True.
Proof.
  destruct (Even.even_odd_dec 3).
  - destruct (Even.even_odd_dec 4).
    + destruct (Even.even_odd_dec 5).
      * auto.
      * auto.
    + auto.          
  - auto.
Qed.

(** exploit, hexploit: they are similar; if you are stuck with one tactic, try another. *)
Module Example_Exploit.
  Variable (P Q R:Prop).

  Goal <<PQ: P -> Q>> /\ <<QR: Q -> R>> -> <<PR: P -> R>>.
  Proof. ii. des. exploit PQ. auto. auto.
  Restart. ii. des. hexploit PQ. auto. auto.
  Qed.
End Example_Exploit.

(** destructs **)
Goal forall (n m:nat), True.
Proof. i. destructs n m. auto. auto. auto. auto.
Restart. i. edestructs n m. auto. auto. auto. auto. (* evariable version *)
Restart. i. depdes n m. auto. auto. auto. auto. (* dependent destruction version *)
Qed.

(** depgen: generalize dependent *)
Goal forall n:nat, True.
Proof. i. depgen n. auto. Qed.

(** mark *)
Module Example_Mark.
  Variable (P Q R:Prop).

  Goal <<PQ: P -> Q>> /\ <<QR: Q -> R>> -> <<PR: P -> R>>.
  Proof.
    ii. des.
    exploit PQ; [M|]; Mdo auto.
  Restart.
    ii. des.
    exploit PQ; [M|]; Mskip auto.
  Abort.
End Example_Mark.

(** revert_until *)
Goal forall (n m p q r:nat), True.
Proof. i. revert_until p. Abort.

(** eadmit *)
Goal exists m:nat, m + 1 = 2.
Proof.
  eexists. eadmit.
Grab Existential Variables.
  admit.
Qed.

Module Example_Guard.
  Variable (P Q R:Prop).

  Goal <<PQ: P -> Q>> /\ <<QR: Q -> R>> -> <<PR: P -> R>>.
  Proof.
    i. guardH H. des.
    unguardH H. des.
    auto.
  Restart.
    i. guard. des. (* guard all *)
    unguard. des. (* unguard all *)
    auto.
  Restart.
    i. guard. desH H. (* des in spite of guard *)
    auto.
  Restart.
    i. guard (P -> Q) in H. desH H.
  Restart.
    i. sguard (P -> Q) in H. desH H. (* "super" guard *)
    auto.
  Qed.
End Example_Guard.
