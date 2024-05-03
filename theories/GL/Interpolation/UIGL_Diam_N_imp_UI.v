  Require Import List.
  Export ListNotations.
  Require Import PeanoNat.
  Require Import Lia.

  Require Import general_export.

  Require Import GLS_export.

  Require Import UIGL_Def_measure.
  Require Import UIGL_Canopy.
  Require Import UIGL_LexSeq.
  Require Import UIGL_nodupseq.
  Require Import UIGL_irred_short.
  Require Import UIGL_braga.
  Require Import UIGL_UI_prelims.
  Require Import UIGL_UI_inter.
  Require Import UIGL_N_imp_UI.


  Theorem Diam_rec_UI_imp : forall s p X Y, (is_init s -> False) -> (critical_Seq s) -> 
              GLS_prv (X,
        Diam (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))))) -->
        Diam (UI p (XBoxed_list (top_boxes (fst s)), []%list)) :: Y).
  Proof.
  intros.
  remember (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))))) as conj1.
  remember (UI p (XBoxed_list (top_boxes (fst s)), []%list)) as conj2.
  unfold Diam. unfold Neg.
  apply derI with (ps:=[((Box (conj1 --> ⊥) --> ⊥) :: X, Box (conj2 --> ⊥) --> ⊥ :: Y)]).
  apply ImpR. epose (ImpRRule_I _ _ [] X [] Y). simpl in i. apply i. apply dlCons. 2: apply dlNil.
  apply derI with (ps:=[(Box (conj2 --> ⊥) :: (Box (conj1 --> ⊥) --> ⊥) :: X, ⊥ :: Y)]).
  apply ImpR. epose (ImpRRule_I _ _ [] (Box (conj1 --> ⊥) --> ⊥ :: X) [] Y). simpl in i. apply i. apply dlCons. 2: apply dlNil.
  apply derI with (ps:=[([Box (conj2 --> ⊥)] ++ X, Box (conj1 --> ⊥) :: ⊥ :: Y);(Box (conj2 --> ⊥) :: ⊥ :: X, ⊥ :: Y)]).
  apply ImpL. epose (ImpLRule_I _ _ [Box (conj2 --> ⊥)] X [] (Bot :: Y)). simpl in i. apply i. apply dlCons. 2: apply dlCons. 3: apply dlNil.
  2: apply derI with (ps:=[]) ; [apply BotL ; epose (BotLRule_I [Box (conj2 --> ⊥)] X _) ; simpl in b ; apply b | apply dlNil].
  apply derI with (ps:=[(XBoxed_list (Box (conj2 --> ⊥) :: top_boxes X) ++ [Box (conj1 --> ⊥)], [conj1 --> ⊥])]).
  apply GLR. epose (@GLRRule_I _ _ _ []). simpl in g. apply g. 3: apply dlCons. 4: apply dlNil.
  intro. intros. inversion H1. exists (conj2 --> ⊥) ; rewrite <- H2 ; auto. apply in_top_boxes in H2. destruct H2.
  destruct s0 ; auto. destruct s0. destruct p0. exists x ; rewrite <- e ; auto.
  simpl. apply univ_gen_ext_cons. apply top_boxes_nobox_gen_ext. simpl.
  apply derI with (ps:=[([] ++ conj1 :: conj2 --> ⊥ :: Box (conj2 --> ⊥) :: XBoxed_list (top_boxes X) ++ [Box (conj1 --> ⊥)], [] ++ ⊥ :: [])]).
  apply ImpR. apply ImpRRule_I. apply dlCons. 2: apply dlNil. simpl.
  apply derI with (ps:=[(conj1 :: Box (conj2 --> ⊥) :: XBoxed_list (top_boxes X) ++ [Box (conj1 --> ⊥)], [conj2 ; ⊥]);
  (conj1 :: ⊥ :: Box (conj2 --> ⊥) :: XBoxed_list (top_boxes X) ++ [Box (conj1 --> ⊥)], [⊥])]).
  apply ImpL. epose (ImpLRule_I _ _ [conj1] _ [] _). simpl in i. apply i. apply dlCons. 2: apply dlCons. 3: apply dlNil.
  2: apply derI with (ps:=[]) ; [apply BotL ; epose (BotLRule_I [conj1] _ _) ; simpl in b ; apply b | apply dlNil].
  pose (@GLS_prv_list_wkn_L [conj1] [] [conj2]). simpl in g.
  pose (@GLS_prv_list_wkn_R (conj1 :: Box (conj2 --> ⊥) :: XBoxed_list (top_boxes X) ++ [Box (conj1 --> ⊥)]) [conj2] []). simpl in g0.
  epose (g0 _ [Bot]). rewrite app_nil_r in g1. apply g1. Unshelve. clear g0.
  epose (g _ (Box (conj2 --> ⊥) :: XBoxed_list (top_boxes X) ++ [Box (conj1 --> ⊥)])).
  rewrite app_nil_r in g0. apply g0. Unshelve. clear g.
  apply ImpR_inv with (concl:=([], [conj1 --> conj2])). subst.
  apply rec_UI_imp ; auto.
  epose (ImpRRule_I _ _ [] [] [] []). simpl in i. apply i.
  Qed.