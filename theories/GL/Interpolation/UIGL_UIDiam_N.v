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
  Require Import UIGL_UI_prelims.
  Require Import UIGL_UI_inter.
  Require Import UIGL_Diam_N_imp_UI.
  Require Import UIGL_Diam_UI_imp_N.


    Section UIPDiam.

  Theorem Diam_rec_UI : forall s p X Y, (is_init s -> False) -> (critical_Seq s) ->
              (GLS_prv (X, Diam (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))))) :: Y) ->
               GLS_prv (X, Diam (UI p (XBoxed_list (top_boxes (fst s)), []%list)) :: Y) ) *

              (GLS_prv (X, Diam (UI p (XBoxed_list (top_boxes (fst s)), []%list)) :: Y) ->
               GLS_prv (X, Diam (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))))) :: Y)).
  Proof.
  intros. split ; intros.

  pose (Diam_rec_UI_imp _ p X Y H H0).
  apply ImpR_inv with (prem:=([] ++ Diam (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))))) :: X,
  [] ++ Diam (UI p (XBoxed_list (top_boxes (fst s)), []%list)) :: Y)) in g.
  pose (GLS_cut_adm (Diam (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))))))
  [] X [] (Diam (UI p (XBoxed_list (top_boxes (fst s)), []%list)) :: Y)). simpl in g0. apply g0. clear g0.
  clear g.
  assert (wkn_R (Diam (UI p (XBoxed_list (top_boxes (fst s)), []%list))) (X, [Diam (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)))))] ++ Y)
  (X, [Diam (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)))))] ++ Diam (UI p (XBoxed_list (top_boxes (fst s)), []%list)) :: Y)).
  apply wkn_RI.
  pose (@GLS_prv_wkn_R (X, [Diam (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)))))] ++ Y)
  X0 _ _ H1). auto.
  simpl in g ; auto.
  assert ((X, Diam (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))))) --> Diam (UI p (XBoxed_list (top_boxes (fst s)), []%list)) :: Y) =
  ([] ++ X, [] ++ Diam (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))))) --> Diam (UI p (XBoxed_list (top_boxes (fst s)), []%list)) :: Y)).
  auto. rewrite H1. apply ImpRRule_I.

  pose (UI_Diam_rec_imp _ p X Y H H0).
  apply ImpR_inv with (prem:=([] ++ Diam (UI p (XBoxed_list (top_boxes (fst s)), []%list)) :: X,
  [] ++ Diam (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))))) :: Y)) in g.
  pose (GLS_cut_adm (Diam (UI p (XBoxed_list (top_boxes (fst s)), []%list)))
  [] X [] (Diam (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))))) :: Y)). simpl in g0. apply g0. clear g0.
  clear g.
  assert (wkn_R (Diam (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)))))) (X, [Diam (UI p (XBoxed_list (top_boxes (fst s)), []%list))] ++ Y)
  (X, [Diam (UI p (XBoxed_list (top_boxes (fst s)), []%list))] ++ Diam (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))))) :: Y)).
  apply wkn_RI.
  pose (@GLS_prv_wkn_R (X, [Diam (UI p (XBoxed_list (top_boxes (fst s)), []%list))] ++ Y)
  X0 _ _ H1). auto.
  simpl in g ; auto.
  assert ((X, Diam (UI p (XBoxed_list (top_boxes (fst s)), []%list)) --> Diam (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))))) :: Y) =
  ([] ++ X, [] ++ Diam (UI p (XBoxed_list (top_boxes (fst s)), []%list)) --> Diam (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))))) :: Y)).
  auto. rewrite H1. apply ImpRRule_I.
  Qed.

    End UIPDiam.