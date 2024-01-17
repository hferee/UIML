Require Import List.
Export ListNotations.
Require Import Lia.
Require Import PeanoNat.

Require Import KS_calc.
Require Import KS_dec.
Require Import KS_termination_measure.
Require Import KS_termination_prelims.

(* Obviously, we can obtain the same result for initial sequents. *)

Lemma finite_IdP_premises_of_S : forall (s : Seq), existsT2 listIdPprems,
              (forall prems, ((IdPRule prems s) -> (InT prems listIdPprems)) *
                             ((InT prems listIdPprems) -> (IdPRule prems s))).
Proof.
intros s. destruct (dec_IdP_rule s).
- exists [[]]. intros. split ; intro.
  * inversion H. subst. apply InT_eq.
  * inversion H. subst. assumption. inversion H1.
- exists []. intros. split ; intro.
  * inversion H. subst. exfalso. apply f. assumption.
  * inversion H.
Qed.

Lemma finite_BotL_premises_of_S : forall (s : Seq), existsT2 listBotLprems,
              (forall prems, ((BotLRule prems s) -> (InT prems listBotLprems)) *
                             ((InT prems listBotLprems) -> (BotLRule prems s))).
Proof.
intros. destruct (dec_BotL_rule s).
- exists [[]]. intros. split ; intro.
  * inversion H. subst. apply InT_eq.
  * inversion H. subst. assumption. inversion H1.
- exists []. intros. split ; intro.
  * inversion H. subst. exfalso. apply f. assumption.
  * inversion H.
Qed.