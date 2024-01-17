
Require Export List.
Set Implicit Arguments.
Export ListNotations.

From Coq Require Import ssreflect.

Require Import genT gen.
Require Import List_lemmasT.
(*
Require Import swappedT.
*)

Definition rel (W : Type) : Type := prod W W.
Definition trf (W : Type) : Type := W -> W.  

Lemma midI: forall T (a b c d : list T) x,
  a = c -> b = d -> a ++ x :: b = c ++ x :: d.
Proof. intros. subst. reflexivity. Qed.

Lemma appI: forall T (a b c d : list T),
  a = b -> c = d -> a ++ c = b ++ d.
Proof. intros. subst. reflexivity. Qed.

Lemma apprI: forall T (a b c : list T),
  a = b -> a ++ c = b ++ c.
Proof. intros. subst. reflexivity. Qed.

Lemma appl_cong: forall {T} (a b c : list T),
  (c ++ a = c ++ b) <-> (a = b).
Proof.  intros. unfold iff. apply conj ; intro.  
  induction c. simpl in H. exact H.
  simpl in H. inversion H. tauto.
  intros. subst. reflexivity. Qed.

Lemma appr_cong: forall {T} (a b c : list T),
  (a ++ c = b ++ c) <-> (a = b).
Proof.  intros. unfold iff. apply conj ; intro.  
pose (@if_eq_rev_eq T (a ++ c) (b ++ c) H).
rewrite -> !rev_app_distr in e.
rewrite -> appl_cong in e.
apply if_rev_eq in e.  exact e.
subst. reflexivity.  Qed.

Lemma app_eq_nil_iff: forall {A} (l l' : list A), 
  l ++ l' = [] <-> l = [] /\ l' = [].
Proof. intros. unfold iff. split ; intros.
  destruct l ; simpl in H ; [ tauto | discriminate]. 
  destruct H. subst. simpl. tauto. Qed.

Lemma applI: forall {T} (a b c : list T),
  a = b -> c ++ a = c ++ b.
Proof. intros. subst. reflexivity. Qed.

Definition app_assoc_cons {A} (x : A) l m xs := app_assoc l m (x :: xs).

(* in ssreflect *)
Ltac list_assoc_l' := repeat (rewrite !app_assoc || rewrite !app_comm_cons).
Ltac list_assoc_r' :=
  repeat (rewrite - !app_assoc || rewrite - !app_comm_cons).
(* tactic to strip off same sublists on lhs or rhs of append sequence *)
Ltac apps_eq_tac := list_assoc_r' ; rewrite ?eq_app_canc1 ;
  list_assoc_l' ; rewrite ?eq_app_canc2 ; reflexivity.

(* to rearrange a ++ b ++ l ++ d ++ e so that l is central, 
  ie to give (a ++ b) ++ l ++ (d ++ e),
  can affect terms not containing l *)
Ltac assoc_mid l := 
  list_assoc_r' ;
  rewrite ?app_comm_cons ;
  repeat ((rewrite - (app_assoc _ l _) ; fail 1) || rewrite app_assoc) ;
  rewrite - (app_assoc _ l _).

(* to rearrange a ++ b ++ x :: d ++ e so that x is central,
  ie to give (a ++ b) ++ x :: d ++ e *)
Ltac assoc_single_mid := list_assoc_r' ; rewrite ?app_assoc_cons.

(* as assoc_single_mid, but to specify x *)
Ltac assoc_single_mid' x := list_assoc_r' ;
  repeat (rewrite (app_assoc_cons x) || rewrite (list_rearr23 x)).  

(* test of assoc_mid
Lemma x : forall T (a b c d e f g : list T) (x y z : T),
  a ++ x :: b ++ c ++ y :: d ++ e ++ z :: f = g.
intros.
assoc_mid b. (* doesn't work *)
assoc_mid c.
assoc_mid d. (* doesn't work *)
assoc_mid e.
*)

Ltac acacE :=
  repeat match goal with
    | [ H : _ |- _ ] => apply app_eq_app in H ; sE
    | [ H : _ |- _ ] => apply cons_eq_app in H ; sE
    | [ H : _ |- _ ] => apply app_eq_cons in H ; sE
    end.

Ltac acacD :=
  repeat match goal with
    | [ H : _ |- _ ] => apply app_eq_app in H ; sD
    | [ H : _ |- _ ] => apply cons_eq_app in H ; sD
    | [ H : _ |- _ ] => apply app_eq_cons in H ; sD
    | [ H : _ :: _ = _ :: _ |- _ ] => injection H as ?H ?H 
    end.

Ltac acacD' :=
  repeat match goal with
    | [ H : _ ++ _ = _ ++ _ |- _ ] => apply app_eq_app in H ; sD
    | [ H : _ :: _ = _ ++ _ |- _ ] => apply cons_eq_app in H ; sD
    | [ H : _ ++ _ = _ :: _ |- _ ] => apply app_eq_cons in H ; sD
    | [ H : _ :: _ = _ :: _ |- _ ] => injection H as ?H ?H 
    | [ H : (_, _) = (_, _) |- _ ] => injection H as ?H ?H 
    | [ H : _ :: _ = [] |- _ ] => discriminate H
    | [ H : [] = _ :: _ |- _ ] => discriminate H
         end.

Ltac acacD'T2 :=
  repeat match goal with
    | [ H : _ ++ _ = _ ++ _ |- _ ] => apply app_eq_appT2 in H ; sD
    | [ H : _ :: _ = _ ++ _ |- _ ] => apply cons_eq_appT2 in H ; sD
    | [ H : _ ++ _ = _ :: _ |- _ ] => apply app_eq_consT2 in H ; sD
    | [ H : _ :: _ = _ :: _ |- _ ] => injection H as ?H ?H 
    | [ H : (_, _) = (_, _) |- _ ] => injection H as ?H ?H 
    | [ H : _ :: _ = [] |- _ ] => discriminate H
    | [ H : [] = _ :: _ |- _ ] => discriminate H
         end.

Ltac acacDe' :=
  match goal with
    | [ H : _ ++ _ = _ ++ _ |- _ ] => apply app_eq_app in H ; sD
    | [ H : _ :: _ = _ ++ _ |- _ ] => apply cons_eq_app in H ; sD
    | [ H : _ ++ _ = _ :: _ |- _ ] => apply app_eq_cons in H ; sD
    | [ H : _ :: _ = _ :: _ |- _ ] => injection H as ?H ?H 
    | [ H : (_, _) = (_, _) |- _ ] => injection H as ?H ?H 
    | [ H : _ :: _ = [] |- _ ] => discriminate H
    | [ H : [] = _ :: _ |- _ ] => discriminate H
    | [ H : _ ++ _ = [] |- _ ] => apply app_eq_nil in H
    | [ H : [] = _ ++ _ |- _ ] => apply nil_eq_app in H
    end.

Ltac acacDe'T2 :=
  match goal with
    | [ H : _ ++ _ = _ ++ _ |- _ ] => apply app_eq_appT2 in H ; sD
    | [ H : _ :: _ = _ ++ _ |- _ ] => apply cons_eq_appT2 in H ; sD
    | [ H : _ ++ _ = _ :: _ |- _ ] => apply app_eq_consT2 in H ; sD
    | [ H : _ :: _ = _ :: _ |- _ ] => injection H as ?H ?H 
    | [ H : (_, _) = (_, _) |- _ ] => injection H as ?H ?H 
    | [ H : _ :: _ = [] |- _ ] => discriminate H
    | [ H : [] = _ :: _ |- _ ] => discriminate H
    | [ H : _ ++ _ = [] |- _ ] => apply app_eq_nilT in H
    | [ H : [] = _ ++ _ |- _ ] => apply nil_eq_appT in H
  end.

Ltac acacDe := repeat (sD' || acacDe').
Ltac acacDeT2 := repeat (sD' || acacDe'T2).

Theorem app_eq_unitT :
    forall {A : Type } (x y:list A) (a:A),
      x ++ y = [a] -> (x = [] /\ y = [a]) + (x = [a] /\ y = []).
Proof.
  intros *; intros H; destruct x; auto.
  simpl in H; inversion H as [[H1 H2]]; subst.
  apply app_eq_nil in H2. destruct H2. subst. auto.
Qed.

Theorem unit_eq_appT :
    forall {A : Type } (x y:list A) (a:A),
      [a] = x ++ y -> (x = [] /\ y = [a]) + (x = [a] /\ y = []).
Proof.
  intros *; intros H. 
  apply app_eq_unitT. auto.
Qed.

Ltac list_eq_nc :=
   match goal with
     | [ H : _ ++ _ :: _ = [] |- _ ] => apply list_eq_nil in H
     | [ H : [] = _ ++ _ :: _  |- _ ] => apply nil_eq_list in H
     | [ H : _ ++ _ = [] |- _ ] => apply app_eq_nil in H
     | [ H : [] = _ ++ _ |- _ ] => apply nil_eq_app in H
     | [ H : _ ++ _ = [_] |- _ ] => apply app_eq_unit in H
     | [ H : [_] = _ ++ _ |- _ ] => apply unit_eq_app in H
     | [ H : _ ++ _ :: _ = [_] |- _ ] => apply list_eq_single in H
     | [ H : [_] = _ ++ _ :: _ |- _ ] => apply single_eq_list in H
     | [ H : _ :: _ = [] |- _ ] => discriminate H
     | [ H : _ :: _ = _ :: _ |- _ ] => injection H as
     end.

(* Type version of list_eq_nc *)
Ltac list_eq_ncT :=
   match goal with
     | [ H : _ ++ _ :: _ = [] |- _ ] => apply list_eq_nil in H
     | [ H : [] = _ ++ _ :: _  |- _ ] => apply nil_eq_list in H
     | [ H : _ ++ _ = [] |- _ ] => apply app_eq_nilT in H
     | [ H : [] = _ ++ _ |- _ ] => apply nil_eq_appT in H
     | [ H : _ ++ _ = [_] |- _ ] => apply app_eq_unitT in H
     | [ H : [_] = _ ++ _ |- _ ] => apply unit_eq_appT in H
     | [ H : _ ++ _ :: _ = [_] |- _ ] => apply list_eq_singleT in H
     | [ H : [_] = _ ++ _ :: _ |- _ ] => apply single_eq_listT in H
     | [ H : _ :: _ = [] |- _ ] => discriminate H
     | [ H : _ :: _ = _ :: _ |- _ ] => injection H as
     end.

Ltac sD_list_eq := repeat (cD' || list_eq_nc || sDx).

