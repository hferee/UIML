Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import general_export.

Require Import GLS_export.

Require Import UIGL_Def_measure.
Require Import UIGL_Canopy.
Require Import UIGL_irred_short.
Require Import UIGL_braga.
Require Import UIGL_LexSeq.
Require Import UIGL_nodupseq.


  Section list_conj_disj_properties.

  Lemma TopR : forall X Y0 Y1, GLS_prv (X, Y0 ++ Top :: Y1).
  Proof.
  intros. unfold Top. apply derI with (ps:=[([] ++ ⊥ :: X, Y0 ++ ⊥ :: Y1)]).
  apply ImpR. assert ((X, Y0 ++ ⊥ --> ⊥ :: Y1) = ([] ++ X, Y0 ++ ⊥ --> ⊥ :: Y1)). auto.
  rewrite H. apply ImpRRule_I. apply dlCons. 2: apply dlNil. apply derI with (ps:=[]).
  apply BotL. apply BotLRule_I. apply dlNil.
  Qed.

  Lemma TopL_remove : forall Y X0 X1, GLS_prv (X0 ++ Top :: X1, Y) -> GLS_prv (X0 ++ X1, Y).
  Proof.
  intros. assert (Y= [] ++ Y). auto. rewrite H. rewrite H in X. apply GLS_cut_adm with (A:=Top) ; auto.
  apply TopR.
  Qed.

  Lemma BotR_remove : forall X Y0 Y1, GLS_prv (X, Y0 ++ Bot :: Y1) -> GLS_prv (X, Y0 ++ Y1).
  Proof.
  intros. assert (X= [] ++ X). auto. rewrite H. rewrite H in X0. apply GLS_cut_adm with (A:=Bot) ; auto.
  apply derI with (ps:=[]). 2: apply dlNil. apply BotL. apply BotLRule_I.
  Qed.

  Lemma AndL : forall s A B, GLS_prv (A :: B :: fst s, snd s) -> GLS_prv (And A B :: fst s, snd s).
  Proof.
  intros. unfold And. unfold Neg.
  apply derI with (ps:=[([] ++ fst s, [] ++ (A --> B --> Bot) :: snd s); ([] ++ Bot :: fst s, [] ++ snd s)]).
  apply ImpL. assert (((A --> B --> Bot) --> Bot :: fst s, snd s) = ([] ++ (A --> B --> Bot) --> Bot :: fst s, snd s)). auto.
  rewrite H. apply ImpLRule_I. apply dlCons. 2: apply dlCons. 3: apply dlNil.
  apply derI with (ps:=[([] ++ A :: fst s, [] ++ B --> Bot :: snd s)]). apply ImpR. apply ImpRRule_I.
  apply dlCons. 2: apply dlNil. apply derI with (ps:=[([A] ++ B :: fst s, [] ++ Bot :: snd s)]).
  assert (([] ++ A :: fst s, [] ++ B --> Bot :: snd s) = ([A] ++ fst s, [] ++ B --> Bot :: snd s)). auto. rewrite H.
  apply ImpR. apply ImpRRule_I. apply dlCons. 2: apply dlNil.
  assert (J0: derrec_height X = derrec_height X). auto.
  assert (J1: wkn_R Bot ([A] ++ B :: fst s, [] ++ snd s) ([A] ++ B :: fst s, [] ++ Bot :: snd s)). apply wkn_RI.
  pose (GLS_wkn_R X J0 J1). destruct s0. auto. apply derI with (ps:=[]). apply BotL. apply BotLRule_I.
  apply dlNil.
  Qed.

  Lemma AndR : forall s A B,  GLS_prv (fst s, A :: snd s) -> GLS_prv (fst s, B :: snd s) -> GLS_prv (fst s, And A B :: snd s).
  Proof.
  intros. unfold And. unfold Neg.
  apply derI with (ps:=[([] ++ A --> B --> ⊥ :: fst s, [] ++ ⊥ :: snd s)]).
  apply ImpR. assert ((fst s, (A --> B --> ⊥) --> ⊥ :: snd s) = ([] ++ fst s, [] ++ (A --> B --> ⊥) --> ⊥ :: snd s)). auto.
  rewrite H. apply ImpRRule_I. apply dlCons. 2: apply dlNil.
  apply derI with (ps:=[([] ++ fst s, [] ++ A :: ⊥ :: snd s);([] ++ B --> ⊥ :: fst s, [] ++ ⊥ :: snd s)]). apply ImpL.
  apply ImpLRule_I. apply dlCons. 2: apply dlCons. 3: apply dlNil.
  assert (J0: derrec_height X = derrec_height X). auto.
  assert (J1: wkn_R Bot ([] ++ fst s, [A] ++ snd s) ([] ++ fst s, [A] ++ ⊥ :: snd s)). apply wkn_RI.
  pose (GLS_wkn_R X J0 J1). destruct s0. auto.
  apply derI with (ps:=[([] ++ fst s, [] ++ B :: ⊥ :: snd s);([] ++ ⊥ :: fst s, [] ++ ⊥ :: snd s)]). apply ImpL.
  apply ImpLRule_I. apply dlCons. 2: apply dlCons. 3: apply dlNil.
  assert (J0: derrec_height X0 = derrec_height X0). auto.
  assert (J1: wkn_R Bot ([] ++ fst s, [B] ++ snd s) ([] ++ fst s, [B] ++ ⊥ :: snd s)). apply wkn_RI.
  pose (GLS_wkn_R X0 J0 J1). destruct s0. auto. apply derI with (ps:=[]). apply BotL. apply BotLRule_I.
  apply dlNil.
  Qed.

  Lemma list_conj_wkn_L : forall l s A, InT A l -> GLS_prv (A :: fst s, snd s) -> GLS_prv (list_conj l :: fst s, snd s).
  Proof.
  induction l.
  - intros. inversion H.
  - intros. inversion H ; subst.
    * simpl. apply AndL.
      assert (J0: derrec_height X = derrec_height X). auto.
      assert (J1: wkn_L (list_conj l) (A :: fst s, snd s) (A :: list_conj l :: fst s, snd s)).
      assert (A :: fst s = [A] ++ fst s). auto. rewrite H0.
      assert (A :: list_conj l :: fst s = [A] ++ list_conj l :: fst s). auto. rewrite H1. apply wkn_LI.
      pose (GLS_wkn_L X J0 J1). destruct s0. auto.
    * simpl. apply IHl in X ; auto.
      assert (J0: derrec_height X = derrec_height X). auto.
      assert (J1: wkn_L a (list_conj l  :: fst s, snd s) (a :: list_conj l :: fst s, snd s)).
      assert (a :: list_conj l :: fst s = [] ++ a :: list_conj l :: fst s). auto. rewrite H0.
      assert ((list_conj l  :: fst s,snd s) = ([] ++ list_conj l :: fst s,snd s)). auto. rewrite H2. apply wkn_LI.
      pose (GLS_wkn_L X J0 J1). destruct s0. apply AndL ; auto.
  Qed.

  Lemma list_conj_R : forall l s, (forall A, InT A l -> GLS_prv (fst s, A :: snd s)) -> GLS_prv (fst s, list_conj l :: snd s).
  Proof.
  induction l.
  - intros. simpl. unfold Top.
    apply derI with (ps:=[([] ++ ⊥ :: fst s, [] ++ ⊥ :: snd s)]).
    apply ImpR. assert ((fst s, ⊥ --> ⊥ :: snd s) = ([] ++ fst s, [] ++ ⊥ --> ⊥ :: snd s)). auto.
    rewrite H. apply ImpRRule_I. apply dlCons. 2: apply dlNil. apply derI with (ps:=[]). apply BotL.
    apply BotLRule_I. apply dlNil.
  - intros. simpl. apply AndR.
    * apply X. apply InT_eq.
    * simpl. apply IHl. intros. apply X. apply InT_cons ; auto.
  Qed.

  Lemma OrL : forall s A B,  GLS_prv (A :: fst s, snd s) -> GLS_prv (B :: fst s, snd s) -> GLS_prv (Or A B :: fst s, snd s).
  Proof.
  intros. unfold Or. unfold Neg.
  apply derI with (ps:=[([] ++ fst s, [] ++ (A --> ⊥) :: snd s); ([] ++ B :: fst s, [] ++ snd s)]).
  apply ImpL. assert (((A --> ⊥) --> B :: fst s, snd s) = ([] ++ (A --> ⊥) --> B :: fst s, snd s)). auto.
  rewrite H. apply ImpLRule_I. apply dlCons. 2: apply dlCons. 3: apply dlNil.
  apply derI with (ps:=[([] ++ A :: fst s, [] ++ Bot :: snd s)]). apply ImpR. apply ImpRRule_I.
  apply dlCons. 2: apply dlNil.
  assert (J0: derrec_height X = derrec_height X). auto.
  assert (J1: wkn_R Bot (A :: fst s, [] ++ snd s) (A :: fst s, [] ++ Bot :: snd s)). apply wkn_RI.
  pose (GLS_wkn_R X J0 J1). destruct s0. auto. auto.
  Qed.

  Lemma OrR : forall s A B, GLS_prv (fst s, A :: B :: snd s) -> GLS_prv (fst s, Or A B :: snd s).
  Proof.
  intros. unfold Or. unfold Neg.
  apply derI with (ps:=[([] ++ (A --> Bot) :: fst s, [] ++ B :: snd s)]).
  apply ImpR. assert ((fst s, (A --> Bot) --> B :: snd s) = (fst s, [] ++ (A --> Bot) --> B :: snd s)). auto.
  rewrite H. apply ImpRRule_I. apply dlCons. 2: apply dlNil.
  apply derI with (ps:=[([] ++ fst s, [] ++ A :: B :: snd s);([] ++ ⊥ :: fst s, [] ++ B :: snd s)]).
  apply ImpL. apply ImpLRule_I.
  apply dlCons. 2: apply dlCons. 3: apply dlNil. simpl ; auto.
  apply derI with (ps:=[]). apply BotL. apply BotLRule_I. apply dlNil.
  Qed.

  Lemma list_disj_L : forall l s, (forall A, InT A l -> GLS_prv (A :: fst s, snd s)) -> GLS_prv (list_disj l :: fst s, snd s).
  Proof.
  induction l.
  - intros. simpl. apply derI with (ps:=[]). apply BotL. assert ((⊥ :: fst s, snd s) = ([] ++ ⊥ :: fst s, snd s)). auto.
    rewrite H. apply BotLRule_I. apply dlNil.
  - intros. simpl. apply OrL.
    * apply X. apply InT_eq.
    * simpl. apply IHl. intros. apply X. apply InT_cons ; auto.
  Qed.

  Lemma list_disj_wkn_R : forall l s A, InT A l -> GLS_prv (fst s, A :: snd s) -> GLS_prv (fst s, list_disj l :: snd s).
  Proof.
  induction l.
  - intros. inversion H.
  - intros. inversion H ; subst.
    * simpl. apply OrR.
      assert (J0: derrec_height X = derrec_height X). auto.
      assert (J1: wkn_R (list_disj l) (fst s, A :: snd s) (fst s, A :: list_disj l :: snd s)).
      assert (A :: snd s = [A] ++ snd s). auto. rewrite H0.
      assert (A :: list_disj l :: snd s = [A] ++ list_disj l :: snd s). auto. rewrite H1. apply wkn_RI.
      pose (GLS_wkn_R X J0 J1). destruct s0. auto.
    * simpl. apply IHl in X ; auto.
      assert (J0: derrec_height X = derrec_height X). auto.
      assert (J1: wkn_R a (fst s, list_disj l  :: snd s) (fst s, a :: list_disj l :: snd s)).
      assert (a :: list_disj l :: snd s = [] ++ a :: list_disj l :: snd s). auto. rewrite H0.
      assert ((fst s, list_disj l  :: snd s) = (fst s, [] ++ list_disj l :: snd s)). auto. rewrite H2. apply wkn_RI.
      pose (GLS_wkn_R X J0 J1). destruct s0. apply OrR ; auto.
  Qed.

  Lemma AndR_inv : forall s A B,  GLS_prv (fst s, And A B :: snd s) -> (GLS_prv (fst s, A :: snd s) * GLS_prv (fst s, B :: snd s)).
  Proof.
  intros. unfold And in X. unfold Neg in X. apply ImpR_inv with (prem:=((A --> B --> ⊥) :: fst s, ⊥ :: snd s)) in X.
  apply ImpL_inv with (prem1:=(fst s, A :: ⊥ :: snd s)) (prem2:=(B --> ⊥ :: fst s, ⊥ :: snd s)) in X. destruct X.
  apply ImpL_inv with (prem1:=(fst s, B :: ⊥ :: snd s)) (prem2:=(⊥ :: fst s, ⊥ :: snd s)) in g0. destruct g0.
  pose (BotR_remove (fst s) [A] (snd s) g). pose (BotR_remove (fst s) [B] (snd s) g0). auto.
  1-2: epose (ImpLRule_I _ _ [] _ [] _) ; simpl in i ; apply i.
  epose (ImpRRule_I _ _ [] _ [] _) ; simpl in i ; apply i.
  Qed.

  Lemma AndL_inv : forall s A B,  GLS_prv (And A B :: fst s, snd s) -> GLS_prv (A :: B :: fst s, snd s).
  Proof.
  intros. unfold And in X. unfold Neg in X.
  apply ImpL_inv with (prem1:=(fst s, A --> B --> ⊥ :: snd s)) (prem2:=(⊥ :: fst s, snd s)) in X. destruct X.
  apply ImpR_inv with (prem:=(A :: fst s, B --> ⊥ :: snd s)) in g.
  apply ImpR_inv with (prem:=(A :: B :: fst s, ⊥ :: snd s)) in g.
  pose (BotR_remove (A :: B :: fst s) [] (snd s) g). simpl in g1. auto.
  epose (ImpRRule_I _ _ [A] _ [] _) ; simpl in i ; apply i.
  epose (ImpRRule_I _ _ [] _ [] _) ; simpl in i ; apply i.
  epose (ImpLRule_I _ _ [] _ [] _) ; simpl in i ; apply i.
  Qed.

  Lemma OrR_inv : forall s A B,  GLS_prv (fst s, Or A B :: snd s) -> GLS_prv (fst s, A :: B :: snd s).
  Proof.
  intros. unfold Or in X. unfold Neg in X.
  apply ImpR_inv with (prem:=(A --> ⊥ :: fst s, B  :: snd s)) in X.
  apply ImpL_inv with (prem1:=(fst s, A :: B :: snd s)) (prem2:=(⊥ :: fst s, B :: snd s)) in X. destruct X. auto.
  epose (ImpLRule_I _ _ [] _ [] _) ; simpl in i ; apply i.
  epose (ImpRRule_I _ _ [] _ [] _) ; simpl in i ; apply i.
  Qed.

  Lemma OrL_inv : forall s A B,  GLS_prv (Or A B :: fst s, snd s) -> (GLS_prv (A :: fst s, snd s) * GLS_prv (B :: fst s, snd s)).
  Proof.
  intros. unfold Or in X. unfold Neg in X.
  apply ImpL_inv with (prem1:=(fst s, A --> ⊥ :: snd s)) (prem2:=(B :: fst s, snd s)) in X. destruct X. split ; auto.
  apply ImpR_inv with (prem:=(A :: fst s, ⊥ :: snd s)) in g.
  pose (BotR_remove (A :: fst s) [] (snd s) g). simpl in g1 ; auto.
  epose (ImpRRule_I _ _ [] _ [] _) ; simpl in i ; apply i.
  epose (ImpLRule_I _ _ [] _ [] _) ; simpl in i ; apply i.
  Qed.



  End list_conj_disj_properties.