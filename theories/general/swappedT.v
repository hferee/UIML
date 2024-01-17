
(* Add LoadPath "../tense-lns". *)

Require Import List.
Require Import existsT.
Require Import gen_tacs.
Require Import gen.
Require Import List_lemmasT.

Set Implicit Arguments.
Import ListNotations.

(* Contains definitions and lemmas for swapped swapped_spec and swapped_gen, all used for contraction. *)

Inductive swapped T: list T -> list T -> Type :=
| swapped_I : forall (X Y A B C D : list T),
    X = (A ++ B ++ C ++ D) -> Y = (A ++ C ++ B ++ D) -> swapped X Y.

Lemma swapped_I': forall T (A B C D : list T),
  swapped (A ++ B ++ C ++ D) (A ++ C ++ B ++ D).
Proof.  intros.  eapply swapped_I ; reflexivity. Qed.
   
Lemma swapped_same: forall T X, swapped X (X : list T).
Proof.  intros.  apply (swapped_I [] [] [] X) ; simpl ; reflexivity. Qed.

Lemma swapped_L: forall T X Y Z,
  swapped X (Y : list T) -> swapped (Z ++ X) (Z ++ Y).
Proof.  intros until 0; intros X0. inversion X0. subst. 
  rewrite !(app_assoc Z). apply swapped_I'. Qed.

Lemma swapped_R: forall T X Y Z,
  swapped X (Y : list T) -> swapped (X ++ Z) (Y ++ Z).
Proof.  intros until 0; intros X0. destruct X0. subst. rewrite <- !app_assoc. apply swapped_I'. Qed.

Lemma swapped_cons: forall T (x : T) Y Z,
  swapped Y Z -> swapped (x :: Y) (x :: Z).
Proof.
  intros until 0; intros H. destruct H.
  subst. repeat rewrite app_comm_cons.
  apply swapped_I'.
Qed.

Definition swapped_single T (x : T) := swapped_cons x (swapped_same []).

Lemma swapped_nilLE T Y: @swapped T [] Y -> Y = [].
Proof. intro sw. inversion sw. subst.
repeat (list_eq_ncT ; cD ; subst) ;
simpl ; rewrite ?app_nil_r ; try reflexivity. Qed.

Lemma swapped_nilRE T Y: @swapped T Y [] -> Y = [].
Proof. intro sw. inversion sw. subst.
repeat (list_eq_ncT ; cD ; subst) ;
simpl ; rewrite ?app_nil_r ; try reflexivity. Qed.

Lemma swapped_singleLE T (x : T) Y: swapped [x] Y -> Y = [x].
Proof. intro sw. inversion sw. subst.
acacD'T2 ; subst ; repeat (list_eq_ncT ; cD ; subst) ;
simpl ; rewrite ?app_nil_r ; try reflexivity. Qed.

Lemma swapped_singleRE T (x : T) Y: swapped Y [x] -> Y = [x].
Proof. intro sw. inversion sw. subst.
acacD'T2 ; subst ; repeat (list_eq_ncT ; cD ; subst) ;
simpl ; rewrite ?app_nil_r ; try reflexivity. Qed.

Lemma swapped_simple: forall T U V X Y,
  U = X ++ Y -> V = Y ++ X -> swapped U (V : list T).
Proof.  intros. subst. 
  apply (swapped_I [] X Y []) ; simpl ; rewrite app_nil_r ; reflexivity. Qed.

Lemma swapped_simple': forall T X Y, swapped (X ++ Y : list T) (Y ++ X).
Proof.  intros. eapply swapped_simple ; reflexivity. Qed. 

Lemma swapped_simpleL: forall T X Y Z,
  Y = Z -> swapped (X ++ Y) (Z ++ X : list T).
Proof.  intros. subst. apply swapped_simple'. Qed.

Lemma swapped_simpleR: forall T X Y Z,
  Y = Z -> swapped (Y ++ X) (X ++ Z : list T).
Proof.  intros. subst. apply swapped_simple'. Qed.

Lemma swapped_comm : forall {T} (A B : list T),
    swapped A B ->
    swapped B A.
Proof.
  intros T A B H.
  inversion H. subst.
  eapply swapped_I'.
Qed.

Definition single X (a : X) := [a].

Lemma cons_app_single X (a : X) xs : a :: xs = single a ++ xs.
Proof. unfold single. simpl. reflexivity. Qed.

Lemma single_eq X a : [a : X] = single a.
Proof. unfold single. reflexivity. Qed.

(* note some of the complexity of swap_tac involving cons
  may be avoided by rewriting with cons_app_single and single_eq *)

Lemma swapped_Rc2 T A H B C: 
  swapped C (H ++ [A : T]) -> swapped (C ++ B) (H ++ A :: B).
Proof. intros sw. eapply swapped_R in sw. revert sw.
rewrite <- app_assoc. simpl.  intro. eassumption. Qed.

Lemma swapped_Rc1 T A H B C: 
  swapped (H ++ [A : T]) C -> swapped (H ++ A :: B) (C ++ B).
Proof. intros sw. eapply swapped_R in sw. revert sw.
rewrite <- app_assoc. simpl.  intro. eassumption. Qed.

Lemma swapped_ca1 T A H: swapped (A :: H) (H ++ [A : T]).
Proof. pose (swapped_simple' [A] H). simpl in s. exact s. Qed.

Lemma swapped_ca2 T A H: swapped (H ++ [A : T]) (A :: H).
Proof. pose (swapped_simple' H [A]). simpl in s. exact s. Qed.

Lemma swapped_map_ex T U (f : T -> U) xs ys:
  swapped (map f xs) ys -> sigT2 (swapped xs) (fun zs => ys = map f zs).
Proof. intro sw. inversion sw. subst. clear sw.
repeat (match goal with | [ H : _ |- _ ] => eapply map_app_ex in H ; cD end).
subst. eexists. apply swapped_I'. rewrite !map_app. reflexivity. Qed.

Lemma swapped_map T U (f : T -> U) xs ys:
  swapped xs ys -> swapped (map f xs) (map f ys).
Proof. intro sw. inversion sw. subst. clear sw.
rewrite !map_app. apply swapped_I'. Qed.

(* Sequences of swaps of length n+1. *)
Inductive swapped_spec {T} : nat -> list T -> list T -> Type :=
  swapped_spec_I X Y : swapped X Y -> swapped_spec 0 X Y
| swapped_spec_step n A B C :
    swapped_spec n A B -> swapped B C -> swapped_spec (S n) A C.

Lemma swapped_spec_refl : forall {T} n (A : list T),
    swapped_spec n A A.
Proof.
  induction n; intros. econstructor. apply swapped_same.
  econstructor. apply IHn.
  apply swapped_same.
Qed. 

Lemma swapped_app_L : forall {T} n (l A B : list T),
    swapped_spec n A B ->
    swapped_spec n (l ++ A) (l ++ B).
Proof.
  induction n; intros until 0; intros Hswap.
  constructor. apply swapped_L. inversion Hswap. auto.
  inversion Hswap as [ | ? ? ? ? X X0]. subst.
  econstructor. eapply IHn. exact X.
  apply swapped_L. assumption.
Qed.

Lemma swapped_spec_trans : forall {T} n1 n2 (l1 l2 l3 : list T),
    swapped_spec n1 l1 l2 ->
    swapped_spec n2 l2 l3 ->
    existsT2 m, swapped_spec m l1 l3.
Proof.
  induction n2; intros until 0; intros H1 H2.
  inversion H2. subst. exists (S n1).
  econstructor. apply H1. assumption.
  inversion H2 as [ | ? ? ? ? X X0]. subst.
  eapply IHn2 in H1. destruct H1 as [m H1].
  exists (S m). econstructor.
  apply H1. apply X0. apply X.
Qed.

Lemma swapped_spec_trans_exact : forall {T} n1 n2 (l1 l2 l3 : list T),
    swapped_spec n1 l1 l2 ->
    swapped_spec n2 l2 l3 ->
    swapped_spec (S (n1 + n2)) l1 l3.
Proof.
  induction n2; intros until 0; intros H1 H2.
  inversion H2 as [? ?  X | ]. subst. rewrite PeanoNat.Nat.add_0_r. 
  econstructor. apply H1. apply X.
  inversion H2 as [| ? ? ? ? X X0]. subst.
  eapply IHn2 in H1. simpl.  econstructor.
  rewrite <- PeanoNat.Nat.add_succ_comm.
  apply H1. apply X0. assumption.
Qed.

Lemma swapped_spec_comm : forall {T} n (A B : list T),
    swapped_spec n A B ->
    swapped_spec n B A.
Proof.
  induction n; intros until 0; intros H.
  constructor. inversion H as [? ? X | ]. subst.
  eapply swapped_comm. assumption.
  inversion H as [ | ? ? ? ? X X0]. subst.
  eapply swapped_comm in X0.
  eapply swapped_spec_I in X0.
  apply IHn in X.
  apply (@swapped_spec_trans_exact T _ _ _ _ _ X0 X).
Qed.

Lemma swapped_spec_conv : forall {T} n m (A B : list T),
  n = m ->
  swapped_spec n A B ->
  swapped_spec m A B.
Proof.  intros. subst. auto. Qed.

Lemma swapped_app_mid_L : forall {T} n (A B C D E : list T),
    swapped_spec n (A ++ B ++ C ++ D) E ->
    swapped_spec (S n) (A ++ C ++ B ++ D) E.
Proof.
  intros until 0; intros Hswap.
  assert (S n = S (0 + n)) as Hass.
  reflexivity.
  eapply swapped_spec_conv. symmetry. apply Hass.
  eapply swapped_spec_trans_exact.
  constructor. apply swapped_I'.
  apply Hswap.
Qed.

Lemma swapped_app_mid_R : forall {T} n (A B C D E : list T),
    swapped_spec n E (A ++ B ++ C ++ D) ->
    swapped_spec (S n) E (A ++ C ++ B ++ D).
Proof.
  intros until 0; intros H.
  eapply swapped_spec_comm in H.
  eapply swapped_spec_comm.
  eapply swapped_app_mid_L.
  apply H.
Qed.

Lemma swapped_spec_front_mid : forall {T} n (A B C D : list T),
    swapped_spec n B (C ++ D) ->
    existsT2 m, swapped_spec m (A ++ B) (C ++ A ++ D).
Proof.
  intros T n A B C D Hswap.
  eapply swapped_app_L in Hswap.
  eapply swapped_spec_trans. exact Hswap.
  rewrite <- app_nil_l.
  eapply swapped_app_mid_R.
  apply swapped_spec_refl.
  Unshelve. apply 0.
Qed.

Lemma swapped__n_mid : forall {T} m (l Gam1 Gam2 Gam1' Gam2' : list T),
    swapped_spec m (Gam1 ++ Gam2) (Gam1' ++ Gam2') ->
    existsT2 n, swapped_spec n (Gam1 ++ l ++ Gam2) (Gam1' ++ l ++ Gam2').
Proof.
  intros until 0.
  intros H. eapply swapped_app_L in H.
  rewrite <- app_nil_l in H.
  eexists.
  replace (Gam1 ++ l ++ Gam2) with (nil ++ Gam1 ++ l ++ Gam2).
  replace (Gam1' ++ l ++ Gam2') with (nil ++ Gam1' ++ l ++ Gam2').
  eapply swapped_app_mid_R.
  eapply swapped_app_mid_L.
  eapply H. all : reflexivity. 
Qed.

(* Sequences of swaps, length implicit. *)
Inductive swapped_gen {T} Gam Delt  :=
  swapped_gen_I : (existsT2 n, @swapped_spec T n Gam Delt) -> swapped_gen Gam Delt.

Lemma swapped_gen_front_mid : forall {T} (A B C D : list T),
    swapped_gen B (C ++ D) ->
    swapped_gen (A ++ B) (C ++ A ++ D).
Proof.
  intros T A B C D Hswap. inversion Hswap as [Hs].
  destruct Hs as [n Hs].
  constructor.
  eapply swapped_spec_front_mid. exact Hs.
Qed.

Lemma swapped_spec_opp : forall {T} n (A B C : list T),
    swapped_spec n B C ->
    swapped A B ->
    swapped_spec (S n) A C.
Proof.
  intros until 0; intros H1 H2.
  eapply swapped_spec_I in H2.
  eapply swapped_spec_trans_exact in H1.
  2 : eapply H2. auto.
Qed.

Lemma swapped__gen : forall {T} (A B : list T),
  swapped A B -> swapped_gen A B.
Proof.
  intros T A B H. constructor.
  exists 0. constructor. exact H.
Qed.

Lemma swapped_gen_app_L : forall {T} (l A B : list T),
    swapped_gen A B ->
    swapped_gen (l ++ A) (l ++ B).
Proof.
  intros T l A B H. inversion H as [H2].
  destruct H2 as [n H2]. constructor.
  eapply swapped_app_L in H2. exists n. exact H2.
Qed.

Lemma swapped_gen_refl : forall {T} (A : list T),
    swapped_gen A A.
Proof.
  intros T A. constructor.
  exists 0. apply swapped_spec_refl.
Qed.

(* tactics to identify swapped lists, where one of swap is single list *)

Ltac show_swapped_1 := 
  list_assoc_r' ;
  try (eapply arg_cong_imp ; [> list_assoc_l' ; reflexivity | ] ; 
    apply swapped_simpleL ; list_eq_assoc) ;
  try (eapply arg1_cong_imp ; [> list_assoc_l' ; reflexivity | ] ; 
    apply swapped_simpleR ; list_eq_assoc).

Ltac show_swapped_1_ns := 
  list_assoc_r ; (* not the ssreflext version *)
  try (eapply arg_cong_imp ; [> list_assoc_l' ; reflexivity | ] ; 
    apply swapped_simpleL ; list_eq_assoc) ;
  try (eapply arg1_cong_imp ; [> list_assoc_l' ; reflexivity | ] ; 
    apply swapped_simpleR ; list_eq_assoc).

(* this should work wherever swap_tac does, but trying to use it in place of
  swap_tac produces occasional failures - why?? - to investigate *)
Ltac swap_tac_Rc :=
  list_assoc_r ; try (apply swapped_same) ; 
    repeat (apply swapped_L || apply swapped_cons) ;  
    list_assoc_l ; 
    repeat (apply swapped_R || apply swapped_Rc1 || apply swapped_Rc2) ;
    (show_swapped_1 || apply swapped_ca2 || apply swapped_ca1).

Ltac swap_tac :=
  list_assoc_r ; try (apply swapped_same) ; 
    repeat (apply swapped_L || apply swapped_cons) ;  
    list_assoc_l ; repeat (apply swapped_R) ; show_swapped_1.

Ltac swap_tac_ns :=
  list_assoc_r ; try (apply swapped_same) ; 
    repeat (apply swapped_L || apply swapped_cons) ;  
    list_assoc_l ; repeat (apply swapped_R) ; show_swapped_1_ns.

Goal forall T A B C D, swapped (A ++ B ++ C ++ D : list T) (D ++ A ++ B ++ C).
Proof. intros.  show_swapped_1.  Qed.

Goal forall T A B C D, swapped (D ++ A ++ B ++ C) (A ++ B ++ C ++ D : list T).
Proof. intros.  show_swapped_1.  Qed.

