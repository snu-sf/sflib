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

(* TODO: remaining *)
