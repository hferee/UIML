  Require Import List.
  Export ListNotations.
  Require Import PeanoNat.
  Require Import Lia.

  Require Import general_export.

  Require Import GLS_export.

  Require Import UIGL_Def_measure.
  Require Import UIGL_Canopy.
  Require Import UIGL_irred_short.
  Require Import UIGL_PermutationT.
  Require Import UIGL_braga.
  Require Import UIGL_LexSeq.
  Require Import UIGL_nodupseq.
  Require Import UIGL_PermutationTS.
  Require Import UIGL_And_Or_rules.
  Require Import UIGL_UI_prelims.
  Require Import UIGL_UI_inter.
  Require Import UIGL_Diam_UI_imp_N_prelim.

  (* Diam UI implies Diam N.  *)

  Theorem UI_Diam_rec_imp : forall s p X Y, (is_init s -> False) -> (critical_Seq s) ->
              GLS_prv (X,
        Diam (UI p (XBoxed_list (top_boxes (fst s)), []%list)) -->
        Diam (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))))) :: Y).
  Proof.
  pose (d:=LexSeq_ind (fun (s:Seq) => forall p X Y, (is_init s -> False) -> (critical_Seq s) ->
              GLS_prv (X, Diam (UI p (XBoxed_list (top_boxes (fst s)), []%list)) -->
        Diam (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))))) :: Y))).
  apply d. clear d. intros s IH.
  intros.
  destruct (empty_seq_dec (XBoxed_list (top_boxes (fst s)), []%list)) as [EE | DE].
  (* (XBoxed_list (top_boxes (fst s)), []%list) is the empty sequent. *)
  { inversion EE ; subst ; simpl in *. rewrite H2 in *. assert (GUI p ([],[]) Bot). apply GUI_empty_seq ; auto. apply UI_GUI in H1.
    rewrite H1 in *. eapply derI with [(Diam ⊥ :: X , _ :: Y)]. apply ImpR. apply (ImpRRule_I _ _ [] _ []).
    apply dlCons. 2: apply dlNil. apply DiamL_lim with (top_boxes X).
    apply is_Boxed_list_top_boxes. apply nobox_gen_ext_top_boxes.
    apply derI with []. apply BotL ; apply (BotLRule_I []). apply dlNil. }
  (* (XBoxed_list (top_boxes (fst s)), []%list) is not the empty sequent. *)
  { destruct (critical_Seq_dec (XBoxed_list (top_boxes (fst s)), []%list)).
  (* The sequent (XBoxed_list (top_boxes (fst s)), []%list) is critical. *)
  - assert ((Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))) = [nodupseq (XBoxed_list (top_boxes (fst s)), []%list)]).
    apply critical_nodupseq in c. apply critical_Seq_InT_Canopy in c. apply Id_InT_Canopy in c ; auto.
    assert (J50: (Canopy (XBoxed_list (top_boxes (fst s)), []%list)) = [(XBoxed_list (top_boxes (fst s)), []%list)]).
    apply critical_Seq_InT_Canopy in c. apply Id_InT_Canopy in c ; auto.
    rewrite H1 ; simpl.
    destruct (dec_init_rules (XBoxed_list (top_boxes (fst s)), []%list)).
    (* The sequent (XBoxed_list (top_boxes (fst s)), []%list) is initial. *)
    * assert (is_init (XBoxed_list (top_boxes (fst s)), []%list)). auto.
      assert (is_init (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))). pose (is_init_nodupseq (XBoxed_list (top_boxes (fst s)), []%list)) ; destruct p0 ; auto.
      assert (J0: GUI p (XBoxed_list (top_boxes (fst s)), []%list) (UI p (XBoxed_list (top_boxes (fst s)), []%list))). apply UI_GUI ; auto.
      pose (@GUI_inv_critic_init p (XBoxed_list (top_boxes (fst s)), []%list) (UI p (XBoxed_list (top_boxes (fst s)), []%list)) J0 c X0). rewrite <- e.
      unfold N.
      destruct (N_pwc p s (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))).
      simpl. pose (GN_inv_init _ g). rewrite e0. unfold Diam. unfold Neg.
      apply derI with (ps:=[([] ++ Box (x --> ⊥) --> ⊥ :: X, [] ++ (Box (And x x --> ⊥) --> ⊥)  :: Y)]).
      assert ((X,  (Box (x --> ⊥) --> ⊥) --> (Box (And x x --> ⊥) --> ⊥) :: Y) = ([] ++ X, [] ++ (Box (x --> ⊥) --> ⊥) --> (Box (And x x --> ⊥) --> ⊥) :: Y)).
      auto. rewrite H2. apply ImpR. apply ImpRRule_I. apply dlCons. 2: apply dlNil.
      apply derI with (ps:=[([] ++ Box (And x x --> ⊥)  :: Box (x --> ⊥) --> ⊥ :: X, [] ++ ⊥ :: Y)]).
      apply ImpR. apply ImpRRule_I. apply dlCons. 2: apply dlNil.
      apply derI with (ps:=[([Box (And x x --> ⊥)] ++ X, [] ++ Box (x --> ⊥) :: ⊥ :: Y);([Box (And x x --> ⊥)] ++ ⊥ :: X, [] ++ ⊥ :: Y)]).
      apply ImpL. apply ImpLRule_I. apply dlCons. 2: apply dlCons. 3: apply dlNil.
      2: apply derI with (ps:=[]) ; [apply BotL ; apply BotLRule_I | apply dlNil].
      apply derI with (ps:=[(XBoxed_list (Box (And x x --> ⊥) :: top_boxes X) ++ [Box (x --> ⊥)], [x --> ⊥])]).
      apply GLR. apply GLRRule_I. 3: apply dlCons. 4: apply dlNil.
      intro. intros. inversion H2. exists (And x x --> ⊥) ; rewrite <- H3 ; auto. apply in_top_boxes in H3. destruct H3.
      destruct s1 ; auto. destruct s1. destruct p0. exists x0 ; rewrite <- e1 ; auto.
      simpl. apply univ_gen_ext_cons. apply top_boxes_nobox_gen_ext. simpl.
      apply derI with (ps:=[([] ++ x :: And x x --> ⊥ :: Box (And x x --> ⊥) :: XBoxed_list (top_boxes X) ++ [Box (x --> ⊥)], [] ++ ⊥ :: [])]).
      apply ImpR. apply ImpRRule_I. apply dlCons. 2: apply dlNil. simpl.
      apply derI with (ps:=[([x] ++ Box (And x x --> ⊥) :: XBoxed_list (top_boxes X) ++ [Box (x --> ⊥)], [] ++ And x x :: [⊥]);
      ([x] ++ ⊥ :: Box (And x x --> ⊥) :: XBoxed_list (top_boxes X) ++ [Box (x --> ⊥)], [] ++ [⊥])]).
      apply ImpL. assert ((x :: And x x --> ⊥ :: Box (And x x --> ⊥) :: XBoxed_list (top_boxes X) ++ [Box (x --> ⊥)], [⊥]) =
      ([x] ++ And x x --> ⊥ :: Box (And x x --> ⊥) :: XBoxed_list (top_boxes X) ++ [Box (x --> ⊥)], [] ++ [⊥])).
      repeat rewrite <- app_assoc ; auto. rewrite H2. apply ImpLRule_I. apply dlCons. 2: apply dlCons. 3: apply dlNil.
      2: apply derI with (ps:=[]) ; [apply BotL ; apply BotLRule_I | apply dlNil].
      pose (AndR ([x] ++ Box (And x x --> ⊥) :: XBoxed_list (top_boxes X) ++ [Box (x --> ⊥)], [⊥]) x x). simpl in g0.
      simpl. apply g0. clear g0.
      all: assert ((x :: Box (And x x --> ⊥) :: XBoxed_list (top_boxes X) ++ [Box (x --> ⊥)], [x; ⊥]) = 
      ([] ++ x :: Box (And x x --> ⊥) :: XBoxed_list (top_boxes X) ++ [Box (x --> ⊥)], [] ++ [x; ⊥])) ;
      auto ; rewrite H2 ; apply Id_all_form.
  (* The sequent (XBoxed_list (top_boxes (fst s)), []%list) is not initial. *)
    * (* Massaging UI. *)
      assert (J: is_init (XBoxed_list (top_boxes (fst s)), []%list) -> False). auto.
      assert (J40: is_init (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)) -> False). intro ; apply J ; apply is_init_nodupseq ; auto.
      assert (J0: GUI p (XBoxed_list (top_boxes (fst s)), []%list) (UI p (XBoxed_list (top_boxes (fst s)), []%list))). apply UI_GUI ; auto.
      assert (J1: Gimap (GUI p) (GLR_prems (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))) (map (UI p) (GLR_prems (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))))). apply Gimap_map. intros.
      apply UI_GUI ; auto.
      assert (J2: Gimap (GN p (GUI p) (XBoxed_list (top_boxes (fst s)), []%list))
      (Canopy (nodupseq (XBoxed_list (top_boxes (fst (XBoxed_list (top_boxes (fst s)), @nil MPropF))), []%list)))
      (map (N p (XBoxed_list (top_boxes (fst s)), []%list)) (Canopy (nodupseq (XBoxed_list (top_boxes (fst (XBoxed_list (top_boxes (fst s)), @nil MPropF))), []%list))))).
      simpl. apply Gimap_map. intros. apply (N_spec p (XBoxed_list (top_boxes (fst s)), []%list) x).

      pose (@GUI_inv_critic_not_init p (XBoxed_list (top_boxes (fst s)), []%list) _ _ _ J0 c DE J J1 J2). rewrite <- e. clear e. simpl.
      (*
      assert (H2 : (GLR_prems (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))) = nil). { simpl.
      unfold GLR_prems. simpl. destruct (finite_GLR_premises_of_S (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))). simpl.
      destruct x ; auto. assert (InT l (l::x)) by apply InT_eq. apply p0 in H2.
      inversion H2 ; subst. destruct Δ0 ; inversion H6.
      }
      rewrite H2. simpl. *)

      (* Naming formulas for brevity. *)
      remember (And (N p s (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))) Top) as conj.
      remember (Or ⊥ (Or (list_disj (map Neg (restr_list_prop p (XBoxed_list (top_boxes (fst s)))))) (Or ⊥ (Diam (list_conj (map (N p (XBoxed_list (top_boxes (fst s)), []%list)) (Canopy (nodupseq (XBoxed_list (top_boxes (XBoxed_list (top_boxes (fst s)))), []%list))))))))) as disj.

       (* Proof-theoretic work. *)
       apply derI with (ps:=[([] ++ Diam disj :: X, [] ++ Diam conj :: Y)]). apply ImpR.
       apply ImpRRule_I.
       apply dlCons. 2: apply dlNil. unfold Diam.
       apply derI with (ps:=[([] ++ Box (Neg conj) :: Neg (Box (Neg disj)) :: X, [] ++ Bot :: Y)]).
       apply ImpR. apply ImpRRule_I. apply dlCons. 2: apply dlNil.
       apply derI with (ps:=[([Box (Neg conj)] ++ X, [] ++  Box (Neg disj) :: ⊥ :: Y);
       ([Box (Neg conj)] ++ Bot :: X, [] ++ ⊥ :: Y)]).
       apply ImpL. apply ImpLRule_I. apply dlCons. 2: apply dlCons. 3: apply dlNil.
       2: apply derI with (ps:=[]) ; [apply BotL ; apply BotLRule_I | apply dlNil].
       apply derI with (ps:=[(XBoxed_list (Box (Neg conj) :: top_boxes X) ++ [Box (Neg disj)], [Neg disj])]).
       apply GLR. apply GLRRule_I.
       intro A. intros H3. inversion H3 as [H4 | H4]. exists (Neg conj) ; rewrite <- H4 ; auto. apply in_top_boxes in H4. destruct H4.
       destruct s0 ; auto. destruct s0. destruct p0. exists x ; rewrite <- e ; auto.
       simpl. apply univ_gen_ext_cons. apply top_boxes_nobox_gen_ext. simpl. apply dlCons. 2: apply dlNil.
       apply derI with (ps:=[([] ++ disj :: Neg conj  :: Box (Neg conj) :: XBoxed_list (top_boxes X) ++ [Box (Neg disj)], [] ++ Bot :: [])]).
       apply ImpR. assert ((Neg conj :: Box (Neg conj) :: XBoxed_list (top_boxes X) ++ [Box (Neg disj)], [Neg disj]) =
       ([] ++ Neg conj :: Box (Neg conj) :: XBoxed_list (top_boxes X) ++ [Box (Neg disj)], [] ++ [Neg disj])). auto. rewrite H2.
       apply ImpRRule_I. apply dlCons. 2: apply dlNil. simpl.
       apply derI with (ps:=[([disj] ++ Box (Neg conj) :: XBoxed_list (top_boxes X) ++ [Box (Neg disj)], [] ++ conj :: [⊥]);
       ([disj] ++ Bot:: Box (Neg conj) :: XBoxed_list (top_boxes X) ++ [Box (Neg disj)], [] ++ [⊥])]).
       apply ImpL. assert ((disj :: Neg conj :: Box (Neg conj) :: XBoxed_list (top_boxes X) ++ [Box (Neg disj)], [⊥]) =
       ([disj] ++ Neg conj :: Box (Neg conj) :: XBoxed_list (top_boxes X) ++ [Box (Neg disj)], [] ++ [⊥])).
       repeat rewrite <- app_asoc ; auto. rewrite H2. apply ImpLRule_I. apply dlCons. 2: apply dlCons. 3: apply dlNil.
       2: apply derI with (ps:=[]) ; [apply BotL ; apply BotLRule_I | apply dlNil]. simpl. rewrite Heqconj.
       pose (AndR (disj :: Box (Neg (And (N p s (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))) Top)) :: XBoxed_list (top_boxes X) ++ [Box (Neg disj)], [⊥]) (N p s (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))) Top).
       simpl in g. apply g. clear g.
       2: pose (TopR (disj :: Box (Neg (And (N p s (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))) Top)) :: XBoxed_list (top_boxes X) ++ [Box (Neg disj)]) [] [Bot]) ; simpl in g0 ; auto.
       pose (@GLS_prv_wkn_R (disj :: Box (Neg (And (N p s (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))) Top)) :: XBoxed_list (top_boxes X) ++ [Box (Neg disj)], [N p s (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))])).
       apply g with (A:=Bot). clear g. subst.
      2: epose (wkn_RI Bot _ [N p s (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))] []) ; simpl in w ; apply w.

       (* Naming LHS. *)
       remember (Box (Neg (And (N p s (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))) Top)) :: XBoxed_list (top_boxes X) ++ [Box (Neg (Or ⊥ (Or (list_disj (map Neg (restr_list_prop p (XBoxed_list (top_boxes (fst s))))))
       (Or ⊥ (Diam (list_conj (map (N p (XBoxed_list (top_boxes (fst s)), []%list)) (Canopy (nodupseq (XBoxed_list (top_boxes (XBoxed_list (top_boxes (fst s)))), []%list))))))))))]) as LHS.

      destruct (Compare_dec.lt_dec (length (usable_boxes (nodupseq (XBoxed_list (top_boxes (fst s)), [])))) (length (usable_boxes s))).
      (* The sequent (XBoxed_list (top_boxes (fst s)), []%list) has less usable boxes than s. *)
      + remember (N p (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))) as N_func.
         (* Massage N on the right. *)
         unfold N. unfold N in HeqLHS.
         destruct (N_pwc p s (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))).
         simpl. simpl in HeqLHS.
         assert ((forall (x : Seq) (l m : MPropF), (fun (s1 : Seq) (A : MPropF) => UI p s1 = A) x l -> (fun (s1 : Seq) (A : MPropF) => UI p s1 = A) x m -> l = m)).
         intros. subst. auto.
         assert (J11: Gimap (GUI p) (GLR_prems (XBoxed_list (top_boxes (fst s)), []%list)) (map (UI p) (GLR_prems (XBoxed_list (top_boxes (fst s)), []%list)))).
         apply Gimap_map. intros. apply UI_GUI ; auto.
         assert (J12: GUI p (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)) (UI p (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)))). apply UI_GUI ; auto.
         apply UI_GUI in J12.
         pose (GN_inv_noinit_lessub p g J40 l (UI_spec p _)). rewrite <- e. rewrite <- e in HeqLHS. clear e.
         assert (J00: GUI p (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)) (UI p (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)))). apply UI_GUI ; auto.
         assert (J01: critical_Seq (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))). apply critical_nodupseq in c ; auto.
         assert (J43: (nodupseq (XBoxed_list (top_boxes (fst s)), @nil MPropF)) <> ([],[])). simpl ; intro. inversion H3.
         apply nodup_nil in H5. rewrite H5 in DE ; auto.
         assert (J44: is_init (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)) -> False). intro. apply J. apply is_init_nodupseq ; auto.
         assert (J45: Gimap (GUI p) (GLR_prems (nodupseq (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)))) (map (UI p) (GLR_prems (nodupseq (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)))))).
         apply Gimap_map. intros. apply UI_GUI ; auto.
         assert (J46: Gimap (GN p (GUI p) (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)))
         (Canopy (nodupseq (XBoxed_list (top_boxes (fst (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)))), []%list)))
         (map (N p (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))) (Canopy (nodupseq (XBoxed_list (top_boxes (fst (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)))), []%list))))).
         simpl. apply Gimap_map. intros. apply (N_spec p (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)) x0).
         pose (@GUI_inv_critic_not_init p (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)) _ _ _ J00 J01 J43 J44 J45 J46). rewrite <- e. clear e. simpl.
         (* Deal with the first disjuncts. *)
         epose (OrL (_,_)). apply g0 ; simpl ; clear g0.
         apply derI with (ps:=[]) ; [ apply BotL ; apply (BotLRule_I []) | apply dlNil].
         epose (OrL (_,_)). apply g0 ; simpl ; clear g0.
         epose (OrR (_,_)). apply g0 ; simpl ; clear g0.
         epose (@GLS_prv_wkn_R (list_disj (map Neg (restr_list_prop p (XBoxed_list (top_boxes (fst s))))) :: LHS,[Or (list_disj (map Neg (restr_list_prop p (nodup eq_dec_form (XBoxed_list (top_boxes (fst s))))))) (Or ⊥
         (Diam (list_conj (map (N p (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)))
         (Canopy (nodupseq (XBoxed_list (top_boxes (nodup eq_dec_form (XBoxed_list (top_boxes (fst s))))), []%list)))))))])).
         apply g0 with (A:=Bot) ; simpl ; clear g0. 2: eapply (wkn_RI Bot _ []).
         eapply (list_disj_L _ (_,_)) ; simpl. intros. apply InT_map_iff in H3. destruct H3. destruct p0. rewrite <- e.
         epose (OrR (_,_)). apply g0 ; simpl ; clear g0.
         eapply (list_disj_wkn_R _ (_,_) (Neg x0)) ; simpl. apply InT_map_iff. exists x0 ; split ; auto.
         apply restr_list_prop_nodup in i ; auto.
         epose (Id_all_form _ [] _ [] _). simpl in d. apply d.
         epose (OrL (_,_)). apply g0 ; simpl ; clear g0.
         apply derI with (ps:=[]) ; [ apply BotL ; apply (BotLRule_I []) | apply dlNil].
         epose (OrR (_,_)). apply g0 ; simpl ; clear g0.
         epose (@GLS_prv_wkn_R (Diam (list_conj (map (fun s0 : Seq => proj1_sig
         (N_pwc p (XBoxed_list (top_boxes (fst s)), []%list) s0))
         (Canopy (nodupseq (XBoxed_list (top_boxes (XBoxed_list (top_boxes (fst s)))), []%list))))) :: LHS,[Or (list_disj (map Neg (restr_list_prop p (nodup eq_dec_form (XBoxed_list (top_boxes (fst s))))))) (Or ⊥
         (Diam (list_conj (map (N p (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)))
         (Canopy (nodupseq (XBoxed_list (top_boxes (nodup eq_dec_form (XBoxed_list (top_boxes (fst s))))), []%list)))))))])).
         apply g0 with (A:=Bot) ; simpl ; clear g0. 2: eapply (wkn_RI Bot _ []).
         epose (OrR (_,_)). apply g0 ; simpl ; clear g0.
         epose (@GLS_prv_wkn_R (Diam (list_conj (map (fun s0 : Seq => proj1_sig
         (N_pwc p (XBoxed_list (top_boxes (fst s)), []%list) s0))
         (Canopy (nodupseq (XBoxed_list (top_boxes (XBoxed_list (top_boxes (fst s)))), []%list))))) :: LHS,[(Or ⊥
         (Diam (list_conj (map (N p (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)))
         (Canopy (nodupseq (XBoxed_list (top_boxes (nodup eq_dec_form (XBoxed_list (top_boxes (fst s))))), []%list)))))))])).
         apply g0 with (A:=list_disj (map Neg (restr_list_prop p (nodup eq_dec_form (XBoxed_list (top_boxes (fst s))))))) ; simpl ; clear g0.
          2: eapply (wkn_RI (list_disj (map Neg (restr_list_prop p (nodup eq_dec_form (XBoxed_list (top_boxes (fst s))))))) _ []).
         epose (OrR (_,_)). apply g0 ; simpl ; clear g0.
         epose (@GLS_prv_wkn_R (Diam (list_conj (map (fun s0 : Seq => proj1_sig
         (N_pwc p (XBoxed_list (top_boxes (fst s)), []%list) s0))
         (Canopy (nodupseq (XBoxed_list (top_boxes (XBoxed_list (top_boxes (fst s)))), []%list))))) :: LHS,[Diam (list_conj (map (N p (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)))
         (Canopy (nodupseq (XBoxed_list (top_boxes (nodup eq_dec_form (XBoxed_list (top_boxes (fst s))))), []%list)))))])).
         apply g0 with (A:=Bot) ; simpl ; clear g0. 2: eapply (wkn_RI Bot _ []).

        (* Naming formulas for brevity. *)
        remember ((list_conj (map (fun s0 : Seq => proj1_sig (N_pwc p(XBoxed_list (top_boxes (fst s)), []%list) s0))
        (Canopy (nodupseq (XBoxed_list (top_boxes (XBoxed_list (top_boxes (fst s)))), []%list)))))) as conj1.
        remember (list_conj
         (map (N p (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)))
            (Canopy (nodupseq (XBoxed_list (top_boxes (nodup eq_dec_form (XBoxed_list (top_boxes (fst s))))), []%list))))) as conj2.

         (* Proof-theoretic work. *)
         unfold Diam.
         apply derI with (ps:=[([] ++ Box (Neg conj2) :: Neg (Box (Neg conj1)) :: LHS, [] ++ Bot :: [])]).
         apply ImpR. apply ImpRRule_I. apply dlCons. 2: apply dlNil.
         apply derI with (ps:=[([Box (Neg conj2)] ++ LHS, [] ++  Box (Neg conj1) :: ⊥ :: []);
         ([Box (Neg conj2)] ++ Bot :: LHS, [] ++ ⊥ :: [])]).
         apply ImpL. apply ImpLRule_I. apply dlCons. 2: apply dlCons. 3: apply dlNil.
         2: apply derI with (ps:=[]) ; [apply BotL ; apply BotLRule_I | apply dlNil].
         apply derI with (ps:=[(XBoxed_list (Box (Neg conj2) :: top_boxes LHS) ++ [Box (Neg conj1)], [Neg conj1])]).
         apply GLR. apply GLRRule_I.
         intro. intros. inversion H3. exists (Neg conj2) ; rewrite <- H4 ; auto. apply in_top_boxes in H4. destruct H4.
         destruct s0 ; auto. destruct s0. destruct p0. exists x0 ; rewrite <- e ; auto.
         simpl. apply univ_gen_ext_cons. apply top_boxes_nobox_gen_ext. simpl. apply dlCons. 2: apply dlNil.
         remember (Box (Neg conj2) :: XBoxed_list (top_boxes LHS) ++ [Box (Neg conj1)]) as LHS0.
         apply derI with (ps:=[([] ++ conj1 :: Neg conj2 :: LHS0, [] ++ Bot :: [])]).
         apply ImpR. eapply (ImpRRule_I _ _ [] _ []). apply dlCons. 2: apply dlNil. simpl.
         apply derI with (ps:=[(conj1 :: LHS0, [conj2;⊥]);(conj1 :: Bot :: LHS0, [⊥])]).
         apply ImpL. eapply (ImpLRule_I _ _ [_] _ []). apply dlCons. 2: apply dlCons. 3: apply dlNil.
         2: apply derI with (ps:=[]) ; [apply BotL ; eapply (BotLRule_I [_]) | apply dlNil].

         (* Deal with the Ns. *)
         rewrite Heqconj1. rewrite Heqconj2.
         eapply (list_conj_R _ (_,_)) ; simpl. intros. apply InT_map_iff in H3. destruct H3. destruct p0. rewrite <- e.
         rewrite <- nodup_top_boxes in i. unfold nodupseq in i ; simpl in i. rewrite nodup_XBoxed_list in i.
         eapply (list_conj_wkn_L _ (_,_) (N p (XBoxed_list (top_boxes (fst s)), []%list) x0)). apply InT_map_iff. exists x0.
         destruct ((N_pwc p (XBoxed_list (top_boxes (fst s)), []%list) x0)) ; simpl.
         split ; auto. subst. pose (@N_spec p (XBoxed_list (top_boxes (fst s)), []%list) x0).
         eapply (GN_fun0 p _ _ _ _ _ _ g0 g1). simpl.

        (* Massage the Ns. *)
        destruct (dec_init_rules x0).
        (* The sequents x1 and x0 is initial. *)
         assert (is_init x0) ; auto.
         pose (N_spec p (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)) x0).
         pose (GN_inv_init _ g0). rewrite <- e0 ; auto.
         epose (TopR _ [] [Bot]). simpl in g1 ; apply g1.
        (* The sequent x is not initial. *)
         assert (is_init x0 -> False) ; auto.
         assert (J20: GUI p x0 (UI p x0)). apply UI_GUI ; auto.
         pose (Canopy_critical _ _ i).
         destruct (Compare_dec.lt_dec (length (usable_boxes x0)) (length (usable_boxes (XBoxed_list (top_boxes (fst s)), []%list)))).
         (* The sequent x has less usable boxes than s. *)
         pose (N_spec p (XBoxed_list (top_boxes (fst s)), []%list) x0).
         epose (@GN_inv_noinit_lessub _ _ _ _ _ g0 H3 l0 (UI_spec p _)). rewrite <- e0 ; auto.
         assert (J60: length (usable_boxes x0) < length (usable_boxes (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)))).
         rewrite <- ub_nodupseq ; auto.
         pose (N_spec p (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)) x0).
         epose (@GN_inv_noinit_lessub _ _ _ _ _ g1 H3). rewrite <- e1 ; auto.
         epose (Id_all_form _ [] _ [] _). simpl in d. apply d. apply UI_GUI ; auto.
         (* The sequent x does not have less usable boxes than s. *)
         pose (N_spec p (XBoxed_list (top_boxes (fst s)), []%list) x0).
         assert (J61: Gimap (GUI p) (GLR_prems (nodupseq x0)) (map (UI p) (GLR_prems (nodupseq x0)))).
         apply Gimap_map ; auto. intros ; apply UI_GUI ; auto.
         epose (@GN_inv_noinit_nolessub _ _ _ _ _ g0 H3 n J61). rewrite <- e0 ; auto.
         assert (J62: (length (usable_boxes x0) < length (usable_boxes (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)))) -> False).
         rewrite <- ub_nodupseq ; auto.
         pose (N_spec p (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)) x0).
         epose (@GN_inv_noinit_nolessub _ _ _ _ _ g1 H3 J62 J61). rewrite <- e1 ; auto.
         epose (Id_all_form _ [] _ [] _). simpl in d. apply d.

      (* The sequent (XBoxed_list (top_boxes (fst s)), []%list) does not have less usable boxes than s. *)
      + remember (N p (XBoxed_list (top_boxes (fst s)), []%list)) as N_func.
         (* Massage N on the right. *)
         unfold N. unfold N in HeqLHS. destruct (N_pwc p s (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))).
         simpl. simpl in HeqLHS.
         assert ((forall (x : Seq) (l m : MPropF), (fun (s1 : Seq) (A : MPropF) => UI p s1 = A) x l -> (fun (s1 : Seq) (A : MPropF) => UI p s1 = A) x m -> l = m)).
         intros. subst. auto.
         assert (J11: Gimap (GUI p) (GLR_prems (nodupseq (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)))) (map (UI p) (GLR_prems (nodupseq (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)))))).
         apply Gimap_map. intros. apply UI_GUI ; auto.
         pose (GN_inv_noinit_nolessub _ g J40 n J11). rewrite <- e. rewrite <- e in HeqLHS. clear e. simpl.

        (* (XBoxed_list (top_boxes (XBoxed_list (top_boxes (fst s)))), []%list) is also critical. *)
        assert (critical_Seq (nodupseq (XBoxed_list (top_boxes (XBoxed_list (top_boxes (fst s)))), []%list))).
        intros A HA ; simpl ; simpl in HA. rewrite app_nil_r in HA. apply nodup_In in HA.
        pose (In_XBoxed_list _ _ HA). destruct o. left.
        apply in_top_boxes in H3. destruct H3. destruct s0. destruct s0. destruct p0. exists x0 ; auto.
        destruct H3. destruct H3. subst. apply c. simpl. rewrite app_nil_r. apply XBoxed_list_In.
        apply nolessub_In. intro. apply n. rewrite <- ub_nodupseq. auto. auto.
        pose (i := critical_Seq_InT_Canopy _ H3). apply Id_InT_Canopy in i. rewrite i ; simpl.

        (* Treating the disjunction on the right. *)
        epose (OrR (_,_)). simpl in g0. apply g0 ; clear g0.
        epose (@GLS_prv_wkn_R (Or ⊥ (Or (list_disj (map Neg (restr_list_prop p (XBoxed_list (top_boxes (fst s))))))
        (Or ⊥ (Diam (And (N_func (nodupseq (XBoxed_list (top_boxes (XBoxed_list (top_boxes (fst s)))), []%list))) Top)))) :: LHS, [Or (list_disj (map Neg (restr_list_prop p (nodup eq_dec_form (XBoxed_list (top_boxes (fst s))))))) ⊥])).
        apply g0 with (A:=⊥). clear g0.
        2: eapply (wkn_RI Bot _ []).
        epose (OrR (_,_)). simpl in g0. apply g0 ; clear g0.
        pose (@GLS_prv_wkn_R (Or ⊥ (Or (list_disj (map Neg (restr_list_prop p (XBoxed_list (top_boxes (fst s))))))
        (Or ⊥ (Diam (And (N_func (nodupseq (XBoxed_list (top_boxes (XBoxed_list (top_boxes (fst s)))), []%list))) Top)))) :: LHS, [list_disj (map Neg (restr_list_prop p (nodup eq_dec_form (XBoxed_list (top_boxes (fst s))))))])).
        apply g0 with (A:=⊥). clear g0.
        2: eapply (wkn_RI Bot _ [list_disj (map Neg (restr_list_prop p (nodup eq_dec_form (XBoxed_list (top_boxes (fst s))))))] []).

        (* Treating the disjunction on the left. *)
        epose (OrL (_,_)). simpl in g0. apply g0 ; clear g0.
        apply derI with (ps:=[]). apply BotL. eapply (BotLRule_I []). apply dlNil.
        epose (OrL (_,_)). simpl in g0. apply g0 ; clear g0.
        eapply (list_disj_L _ (_,_)) ; simpl. intros. apply InT_map_iff in H4. destruct H4. destruct p0. rewrite <- e.
        eapply (list_disj_wkn_R _ (_,_) (Neg x0)) ; simpl. apply InT_map_iff. exists x0 ; split ; auto.
        apply restr_list_prop_nodup in i0 ; auto.
        epose (Id_all_form _ [] _ [] _). simpl in d. apply d.
        epose (OrL (_,_)). apply g0 ; simpl ; clear g0.
        apply derI with (ps:=[]) ; [ apply BotL ; apply (BotLRule_I []) | apply dlNil].

        (* Critical case. *)
        subst ; simpl. rewrite i. simpl.
        remember (And (N p (XBoxed_list (top_boxes (fst s)), []%list) (nodupseq (XBoxed_list (top_boxes (XBoxed_list (top_boxes (fst s)))), []%list))) Top) as conjN.
        remember [list_disj (map Neg (restr_list_prop p (nodup eq_dec_form (XBoxed_list (top_boxes (fst s))))))] as RHS.
        remember (Box (Neg (And (Or ⊥ (Or (list_disj (map Neg (restr_list_prop p (nodup eq_dec_form (XBoxed_list (top_boxes (fst s))))))) ⊥)) Top)) :: XBoxed_list (top_boxes X) ++
        [Box (Neg (Or ⊥ (Or (list_disj (map Neg (restr_list_prop p (XBoxed_list (top_boxes (fst s)))))) (Or ⊥ (Diam conjN)))))]) as LHS.
        unfold Diam.
        apply derI with (ps:=[([] ++ LHS, [] ++ (Box (Neg conjN)) :: RHS);([] ++ Bot :: LHS, [] ++ RHS)]).
        apply ImpL. apply ImpLRule_I. apply dlCons. 2: apply dlCons. 3: apply dlNil.
        2: apply derI with (ps:=[]) ; [apply BotL ; apply BotLRule_I | apply dlNil].
        apply derI with (ps:=[(XBoxed_list (top_boxes LHS) ++ [Box (Neg conjN)], [Neg conjN])]).
        apply GLR. apply GLRRule_I.
        intros A HA. rewrite HeqLHS in HA. inversion HA. symmetry in H4. eexists ; rewrite H4 ; auto. apply in_top_boxes in H4. destruct H4.
        destruct s0 ; auto. destruct s0. destruct p0. exists x0 ; rewrite <- e ; auto.
        simpl. apply top_boxes_nobox_gen_ext. apply dlCons. 2: apply dlNil.
        apply derI with (ps:=[([] ++ conjN  :: XBoxed_list (top_boxes LHS) ++ [Box (Neg conjN)], [] ++ Bot :: [])]).
        apply ImpR. assert ((XBoxed_list (top_boxes LHS) ++ [Box (Neg conjN)], [Neg conjN]) =
        ([] ++ XBoxed_list (top_boxes LHS) ++ [Box (Neg conjN)], [] ++ [Neg conjN])). auto. rewrite H4.
        apply ImpRRule_I. apply dlCons. 2: apply dlNil. simpl. subst.
        epose (AndL (_, _)). simpl in g0. apply g0. simpl. clear g0. repeat rewrite top_boxes_distr_app. simpl.
        repeat rewrite XBox_app_distrib. simpl. repeat rewrite <- app_assoc. simpl.
        eapply derI with (ps:=[_ ; _]). apply ImpL. epose (ImpLRule_I _ Bot [_ ; _] _ [] [Bot]).
        simpl in i0. apply i0. apply dlCons. 2: apply dlCons. 3: apply dlNil.
        2: apply derI with (ps:=[]) ; [apply BotL ; epose (BotLRule_I [_ ; _] _ _) ; simpl in b ; apply b | apply dlNil]. simpl.
        epose (AndR (_,_)). simpl in g0. apply g0. clear g0. 2: epose (TopR _ [] [Bot]) ; apply g1 ; auto.
        epose (OrR (_,_)). simpl in g0. apply g0. clear g0.

         (* Massaging N on the left. *)
         unfold N. destruct (N_pwc p (XBoxed_list (top_boxes (fst s)), []%list)
         (nodupseq (XBoxed_list (top_boxes (XBoxed_list (top_boxes (fst s)))), []%list))). simpl.
         assert (J12: Gimap (GUI p) (GLR_prems (nodupseq (nodupseq (XBoxed_list (top_boxes (XBoxed_list (top_boxes (fst s)))), []%list))))
         (map (UI p) (GLR_prems (nodupseq (nodupseq (XBoxed_list (top_boxes (XBoxed_list (top_boxes (fst s)))), []%list)))))).
         apply Gimap_map. intros. apply UI_GUI ; auto.

         assert (J13: length (usable_boxes (nodupseq (XBoxed_list (top_boxes (XBoxed_list (top_boxes (fst s)))), []%list))) < length (usable_boxes (XBoxed_list (top_boxes (fst s)), []%list)) -> False).
         subst. intro. apply n. rewrite <- ub_nodupseq. apply ub_stable ; auto. rewrite <- ub_nodupseq in H4 ; auto.

         assert (J14: is_init (nodupseq (XBoxed_list (top_boxes (XBoxed_list (top_boxes (fst s)))), []%list)) -> False).
         intros. apply J. unfold is_init. right. destruct X0. destruct s0. inversion i0. exfalso. destruct Δ0 ; inversion H6.
         inversion i0. destruct Δ0 ; inversion H6. inversion b. subst.
         assert (InT Bot (XBoxed_list (top_boxes (XBoxed_list (top_boxes (fst s)))))).
         apply In_InT. rewrite <- nodup_In. rewrite <- H4. apply in_or_app ; right ; apply in_eq.
         assert (In Bot (XBoxed_list (top_boxes (fst s)))).
         apply InT_In in H5. apply In_XBoxed_list in H5. destruct H5. exfalso. apply in_top_boxes in H5.
         destruct H5. destruct s0. destruct s0. destruct p0 ; subst. inversion e. destruct H5.
         destruct H5. subst. apply nolessub_In in H5 ; auto. apply XBoxed_list_In ; auto.
         rewrite <- ub_nodupseq in n ; auto. apply In_InT in H6. apply InT_split in H6.
         destruct H6. destruct s0. rewrite e. apply BotLRule_I.

         pose (GN_inv_noinit_nolessub _ g0 J14 J13 J12). rewrite <- e. simpl.

         (* Final proof-theoretic work. *)
         epose (OrL (_,_)). simpl in g1. apply g1 ; clear g1.
         apply derI with (ps:=[]). apply BotL. epose (BotLRule_I []). simpl in b ; auto. apply dlNil.
         epose (OrL (_,_)). simpl in g1. apply g1 ; clear g1.
         epose (@GLS_prv_wkn_R (list_disj (map Neg (restr_list_prop p (nodup eq_dec_form (XBoxed_list (top_boxes (XBoxed_list (top_boxes (fst s)))))))) :: Top
         :: Box (Neg (And (Or ⊥ (Or (list_disj (map Neg (restr_list_prop p (nodup eq_dec_form (XBoxed_list (top_boxes (fst s))))))) ⊥)) Top)) :: XBoxed_list (top_boxes (XBoxed_list (top_boxes X))) ++
         [Neg (Or ⊥ (Or (list_disj (map Neg (restr_list_prop p (XBoxed_list (top_boxes (fst s)))))) (Or ⊥ (Diam (And (Or ⊥ (Or (list_disj (map Neg (restr_list_prop p (nodup eq_dec_form (XBoxed_list (top_boxes (XBoxed_list (top_boxes (fst s))))))))) ⊥)) Top)))));
         Box (Neg (Or ⊥ (Or (list_disj (map Neg (restr_list_prop p (XBoxed_list (top_boxes (fst s)))))) (Or ⊥ (Diam (And (Or ⊥ (Or (list_disj (map Neg (restr_list_prop p (nodup eq_dec_form (XBoxed_list (top_boxes (XBoxed_list (top_boxes (fst s))))))))) ⊥)) Top))))));
         Box (Neg (And (Or ⊥ (Or (list_disj (map Neg (restr_list_prop p (nodup eq_dec_form (XBoxed_list (top_boxes (XBoxed_list (top_boxes (fst s))))))))) ⊥)) Top))], [Or (list_disj (map Neg (restr_list_prop p (nodup eq_dec_form (XBoxed_list (top_boxes (fst s))))))) ⊥; ⊥])).
         apply g1 with (A:=Bot). clear g1. clear e.
         epose (OrR (_,[Bot])). simpl in g1. apply g1. clear g1.
         epose (list_disj_L _ (_,_)). simpl in g1. apply g1. clear g1. intros.
         epose (list_disj_wkn_R _ (_,_) A). apply g1. clear g1. apply InT_map_iff. apply InT_map_iff in H4. destruct H4.
         destruct p0. subst. exists x1 ; split ; auto. apply restr_list_prop_nodup.
         pose (restr_list_prop_nodup (XBoxed_list (top_boxes (XBoxed_list (top_boxes (fst s))))) x1 p). destruct p0. apply i1 in i0.
         unfold restr_list_prop. unfold restr_list_prop in i0. apply In_InT. apply InT_In in i0.
         apply in_remove in i0. destruct i0. apply in_in_remove ; auto. apply In_list_prop_LF in H4.
         destruct H4. destruct s0. subst. apply In_list_In_list_prop_LF ; auto. apply In_XBoxed_list in i0.
         destruct i0. exfalso. apply in_top_boxes in H4. destruct H4. destruct s0. destruct s0. destruct p0. inversion e.
         destruct H4. destruct H4. subst. apply nolessub_In in H4 ; auto. apply XBoxed_list_In ; auto.
         rewrite <- ub_nodupseq in n ; auto.
         simpl. clear g1. epose (Id_all_form A [] _ []). simpl in d. apply d.
         epose (wkn_RI Bot _ []). simpl in w. apply w.
         apply derI with (ps:=[]). apply BotL. epose (BotLRule_I []). simpl in b. auto. apply dlNil.
  (* The sequent (XBoxed_list (top_boxes (fst s)), []%list) is not critical. *)
  - (* First, we massage UI. *)
    assert ((GLR_prems (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))) = nil).
    unfold GLR_prems. destruct (finite_GLR_premises_of_S (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))). simpl.
    destruct x ; auto. assert (InT l (l::x)). apply InT_eq. apply p0 in H1.
    inversion H1 ; subst. destruct Δ0 ; inversion H5.
    assert (J0: GUI p (XBoxed_list (top_boxes (fst s)), []%list) (UI p (XBoxed_list (top_boxes (fst s)), []%list))). apply UI_GUI ; auto.
    assert (J1: Gimap (GUI p) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))) (map (UI p) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))))). apply Gimap_map. intros.
    apply UI_GUI ; auto.
    pose (@GUI_inv_not_critic p (XBoxed_list (top_boxes (fst s)), []%list) (UI p (XBoxed_list (top_boxes (fst s)), []%list)) _ J0 f J1). rewrite <- e. clear e.

    (* Proof theoretic work on the implication and diamonds. *)
    remember (list_conj (map (UI p) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))))) as conj1.
    remember (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))))) as conj2.
    apply derI with (ps:=[([] ++ Diam conj1 :: X, [] ++ Diam conj2 :: Y)]). apply ImpR. apply ImpRRule_I.
    apply dlCons. 2: apply dlNil. unfold Diam.
    apply derI with (ps:=[([] ++ Box (Neg conj2) :: Neg (Box (Neg conj1)) :: X, [] ++ Bot :: Y)]).
    apply ImpR. apply ImpRRule_I. apply dlCons. 2: apply dlNil.
    apply derI with (ps:=[([Box (Neg conj2)] ++ X, [] ++  Box (Neg conj1) :: ⊥ :: Y);
    ([Box (Neg conj2)] ++ Bot :: X, [] ++ ⊥ :: Y)]).
    apply ImpL. apply ImpLRule_I. apply dlCons. 2: apply dlCons. 3: apply dlNil.
    2: apply derI with (ps:=[]) ; [apply BotL ; apply BotLRule_I | apply dlNil].
    apply derI with (ps:=[(XBoxed_list (Box (Neg conj2) :: top_boxes X) ++ [Box (Neg conj1)], [Neg conj1])]).
    apply GLR. apply GLRRule_I.
    intro. intros. inversion H2. exists (Neg conj2) ; rewrite <- H3 ; auto. apply in_top_boxes in H3. destruct H3.
    destruct s0 ; auto. destruct s0. destruct p0. exists x ; rewrite <- e ; auto.
    simpl. apply univ_gen_ext_cons. apply top_boxes_nobox_gen_ext. simpl. apply dlCons. 2: apply dlNil.
    apply derI with (ps:=[([] ++ conj1 :: Neg conj2 :: Box (Neg conj2) :: XBoxed_list (top_boxes X) ++ [Box (Neg conj1)], [] ++ Bot :: [])]).
    apply ImpR. eapply (ImpRRule_I _ _ [] _ []). apply dlCons. 2: apply dlNil. simpl.
    apply derI with (ps:=[([conj1] ++ Box (Neg conj2) :: XBoxed_list (top_boxes X) ++ [Box (Neg conj1)], [] ++ conj2 :: [⊥]);
    ([conj1] ++ Bot :: Box (Neg conj2) :: XBoxed_list (top_boxes X) ++ [Box (Neg conj1)], [] ++ [⊥])]).
    apply ImpL. eapply (ImpLRule_I _ _ [_] _ [] [_]). apply dlCons. 2: apply dlCons. 3: apply dlNil.
    2: apply derI with (ps:=[]) ; [apply BotL ; apply BotLRule_I | apply dlNil]. simpl.

    (* Getting rid of bottom on the right. *)
    pose (@GLS_prv_wkn_R (conj1 :: Box (Neg conj2) :: XBoxed_list (top_boxes X) ++ [Box (Neg conj1)], [conj2])).
    apply g with (A:=Bot). subst. clear g.
    2: assert ([conj2; ⊥] = [conj2] ++ ⊥ :: []) ; auto. 2: rewrite H2.
    2: assert ([conj2] = [conj2] ++ []) ; auto. 2: rewrite H3 ; apply wkn_RI.

    (* Naming context on the left. *)
    remember (Box (Neg (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))))))
    :: XBoxed_list (top_boxes X) ++ [Box (Neg (list_conj (map (UI p) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))))))]) as LHS.

    (* We treat the list of conjunction on the right. *)
    epose (list_conj_R _ (_,[])). simpl in g. apply g. clear g. intros. apply InT_map_iff in H2. destruct H2. destruct p0. rewrite <- e.

    (* We treat the list of conjunction on the left. *)
    epose (list_conj_wkn_L _ (LHS,_)). simpl in g. apply g with (A:=UI p x). clear g. subst. apply InT_map_iff. exists x ; auto. clear g.

    destruct (dec_init_rules x).
    (* The sequent x is initial. *)
     assert (is_init x) ; auto.
     pose (N_spec p s x).
     pose (GN_inv_init _ g). rewrite <- e0 ; auto.
     epose (TopR _ [] []). simpl in g0 ; apply g0.
    (* The sequent x is not initial. *)
     assert (is_init x -> False) ; auto.
     assert (J2: GUI p x (UI p x)). apply UI_GUI ; auto.
     pose (Canopy_critical _ _ i).
     assert (J3: Gimap (GUI p) (GLR_prems (nodupseq x)) (map (UI p) (GLR_prems (nodupseq x)))).
     apply Gimap_map. intros. apply UI_GUI ; auto.
     assert (J4: Gimap (GN p (GUI p) x) (Canopy (nodupseq (XBoxed_list (top_boxes (fst x)), @nil MPropF)))
     (map (N p x) (Canopy (nodupseq (XBoxed_list (top_boxes (fst x)), @nil MPropF))))).
     simpl. apply Gimap_map. intros. apply (N_spec p x x0).
     destruct (empty_seq_dec x) as [EEx | DEx].
     { subst. assert (GUI p ([],[]) Bot). apply GUI_empty_seq ; auto. apply UI_GUI in H3.
       rewrite H3 in *. apply derI with []. apply BotL ; apply (BotLRule_I []). apply dlNil. }

      { epose (GUI_inv_critic_not_init _ J2 c DEx H2 J3 J4). rewrite <- e0.
      destruct (Compare_dec.lt_dec (length (usable_boxes x)) (length (usable_boxes s))).
      (* The sequent x has less usable boxes than s. *)
      assert ((forall (x : Seq) (l m : MPropF), (fun (s1 : Seq) (A : MPropF) => UI p s1 = A) x l -> (fun (s1 : Seq) (A : MPropF) => UI p s1 = A) x m -> l = m)).
      intros. subst. auto.
      pose (N_spec p s x).
      epose (@GN_inv_noinit_lessub _ _ _ _ _ g H2 l (UI_spec p _)). rewrite <- e1 ; auto. rewrite <- e0.
      epose (Id_all_form _ [] _ [] []). simpl in d ; apply d.
      (* The sequent x does not have less usable boxes than s. *)
      assert ((forall (x : Seq) (l m : MPropF), (fun (s1 : Seq) (A : MPropF) => UI p s1 = A) x l -> (fun (s1 : Seq) (A : MPropF) => UI p s1 = A) x m -> l = m)).
      intros. subst. auto.
      pose (N_spec p s x).
      assert (J5: Gimap (GUI p) (GLR_prems (nodupseq x)) (map (UI p) (GLR_prems (nodupseq x)))).
      apply Gimap_map ; auto. intros ; apply UI_GUI ; auto.
      epose (@GN_inv_noinit_nolessub _ _ _ _ _ g H2 n J5). rewrite <- e1 ; auto.

       (* Proof-theoretic work. *)
       epose (OrL (LHS,_)). simpl in g0. apply g0. clear g0.
       epose (OrR (_,[])). simpl in g0. apply g0. epose (Id_all_form _ [] _ [] _). simpl in d ; apply d.
       apply g0. clear g0. epose (OrR (_,[])). simpl in g0. apply g0.
       pose (@GLS_prv_wkn_R (list_disj (map Neg (restr_list_prop p (fst x))) :: LHS, [Or (list_disj (map Neg (restr_list_prop p (fst x)))) (list_disj (map Box (map (UI p) (GLR_prems (nodupseq x)))))])).
       apply g1 with (A:=list_disj (restr_list_prop p (snd x))). clear g1. apply g0. epose (Id_all_form _ [] _ [] _). simpl in d ; apply d.
       epose (wkn_RI _ _ []). simpl in w. apply w.
       apply g0. clear g0. epose (OrR (_,[])). simpl in g0. apply g0.
       pose (@GLS_prv_wkn_R (list_disj (map Box (map (UI p) (GLR_prems (nodupseq x)))) :: LHS, [Or (list_disj (map Neg (restr_list_prop p (fst x)))) (list_disj (map Box (map (UI p) (GLR_prems (nodupseq x)))))])).
       apply g1 with (A:=list_disj (restr_list_prop p (snd x))). clear g1. apply g0.
       pose (@GLS_prv_wkn_R (list_disj (map Box (map (UI p) (GLR_prems (nodupseq x)))) :: LHS, [(list_disj (map Box (map (UI p) (GLR_prems (nodupseq x)))))])).
       apply g1 with (A:=list_disj (map Neg (restr_list_prop p (fst x)))). clear g1. clear g0.
       epose (Id_all_form _ [] _ [] _). simpl in d ; apply d.
       epose (wkn_RI _ _ []). simpl in w. apply w. epose (wkn_RI _ _ []). simpl in w. apply w.
       clear g0. epose (OrR (_,[])). simpl in g0. apply g0.
       pose (@GLS_prv_wkn_R (Diam (list_conj (map (N p x) (Canopy (nodupseq (XBoxed_list (top_boxes (fst x)), []%list))))) :: LHS, [Or (list_disj (map Neg (restr_list_prop p (fst x)))) (list_disj (map Box (map (UI p) (GLR_prems (nodupseq x)))))])).
       apply g1 with (A:=list_disj (restr_list_prop p (snd x))). clear g1. apply g0.
       pose (@GLS_prv_wkn_R (Diam (list_conj (map (N p x) (Canopy (nodupseq (XBoxed_list (top_boxes (fst x)), []%list))))) :: LHS, [(list_disj (map Box (map (UI p) (GLR_prems (nodupseq x)))))])).
       apply g1 with (A:=list_disj (map Neg (restr_list_prop p (fst x)))). clear g1. clear g0.
       2-3: epose (wkn_RI _ _ []) ; simpl in w ; apply w.
      remember [list_disj (map Box (map (UI p) (GLR_prems (nodupseq x))))] as RHS. unfold Diam.
      apply derI with (ps:=[([] ++ LHS, [] ++  Box (Neg (list_conj (map (N p x) (Canopy (nodupseq (XBoxed_list (top_boxes (fst x)), []%list)))))) :: RHS);
      ([] ++ Bot :: LHS, [] ++ RHS)]).
      apply ImpL. apply ImpLRule_I. apply dlCons. 2: apply dlCons. 3: apply dlNil.
      2: apply derI with (ps:=[]) ; [apply BotL ; apply BotLRule_I | apply dlNil].
      apply derI with (ps:=[(XBoxed_list (top_boxes LHS) ++ [Box (Neg (list_conj (map (N p x) (Canopy (nodupseq (XBoxed_list (top_boxes (fst x)), []%list))))))], [(Neg (list_conj (map (N p x) (Canopy (nodupseq (XBoxed_list (top_boxes (fst x)), []%list))))))])]).
      apply GLR. apply GLRRule_I.
      intro. intros. subst. simpl in H4. repeat rewrite top_boxes_distr_app in H4. simpl in H4.
      inversion H4. symmetry in H5 ;  eexists ; apply H5. apply in_app_or in H5. destruct H5.
      apply in_top_boxes in H5. destruct H5. destruct s0 ; auto. destruct s0. destruct p0. exists x0 ; rewrite <- e ; auto.
      simpl in H5. destruct H5. symmetry in H5 ; eexists ; apply H5. inversion H5.
      simpl. apply top_boxes_nobox_gen_ext. apply dlCons. 2: apply dlNil. subst. simpl.
      pose (@GLS_prv_list_wkn_L [Neg (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)))))] []
      [Neg (list_conj (map (N p x) (Canopy (nodupseq (XBoxed_list (top_boxes (fst x)), []%list)))))]).
      simpl in g0.

      assert (J20: GLS_prv ([Neg (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)))))],
      [Neg (list_conj (map (N p x) (Canopy (nodupseq (XBoxed_list (top_boxes (fst x)), []%list)))))])).
      remember (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))))) as conj1. clear e0.
      remember (list_conj (map (N p x) (Canopy (nodupseq (XBoxed_list (top_boxes (fst x)), []%list))))) as conj2.
      apply derI with (ps:=[([conj2;Neg conj1], [Bot])]). apply ImpR. epose (ImpRRule_I _ _ [] _ [] []). simpl in i0. apply i0.
      apply dlCons. 2: apply dlNil.
      apply derI with (ps:=[([conj2] , [conj1; ⊥]);([conj2;Bot], [⊥])]). apply ImpL. epose (ImpLRule_I _ _[conj2] [] [] [Bot]). simpl in i0.
      apply i0. apply dlCons. 2: apply dlCons. 3: apply dlNil.
      2: apply derI with (ps:=[]) ; [apply BotL ; eapply (BotLRule_I [conj2] [] _) | apply dlNil]. simpl. subst.
      pose (@GLS_prv_wkn_R ([list_conj (map (N p x) (Canopy (nodupseq (XBoxed_list (top_boxes (fst x)), []%list))))], [list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))))])).
      apply g1 with (A:=Bot). clear g1.
      2: epose (wkn_RI  Bot _ [list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))))] []) ; simpl in w ; apply w.
      epose (list_conj_R _ (_,_)). apply g1 ; clear g1 ; simpl.
      intros A HA. apply InT_map_iff in HA. destruct HA. destruct p0 ; subst.

      assert (PermutationTS (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)) (nodupseq (XBoxed_list (top_boxes (fst x)), []%list))).
      unfold PermutationTS. split ; simpl. 2: apply permT_nil. apply Permutation_PermutationT.
      apply NoDup_Permutation. 1-2: apply NoDup_nodup.
      assert (length (usable_boxes x) < length (usable_boxes (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))) -> False).
      intro. rewrite <- ub_nodupseq in H4. pose (leq_ub_unif s). lia.
      assert (forall A, In A (top_boxes (fst s)) <-> In A (top_boxes (fst x))).
      intros ; split ; intros. apply top_boxes_diam_jump in H5 ; auto.
      pose (top_boxes_Canopy_noless_ub _ _ i H4). simpl in p0 ; destruct p0. destruct p0.
      destruct p0. apply i4. rewrite <- nodup_top_boxes. apply nodup_In. auto.
      pose (leq_ub_unif s). inversion l ; auto ; subst. exfalso. rewrite <- ub_nodupseq in H4.
      pose (leq_ub_Canopy _ _ i). rewrite <- ub_nodupseq in l0. lia.
      apply top_boxes_diam_jump ; auto. pose (leq_ub_unif s). inversion l ; auto ; subst. exfalso. rewrite <- ub_nodupseq in H4.
      pose (leq_ub_Canopy _ _ i). rewrite <- ub_nodupseq in l0. lia.
      pose (top_boxes_Canopy_noless_ub _ _ i H4). simpl in p0 ; destruct p0. destruct p0.
      destruct p0. apply i3 in H5. rewrite <- nodup_top_boxes in H5. apply nodup_In in H5. auto.
      intros. split ; intro ; apply nodup_In ; apply nodup_In in H6.
      apply In_XBoxed_list in H6. destruct H6. apply list_preserv_XBoxed_list ; apply H5 ; auto.
      destruct H6. destruct H6 ; subst. apply XBoxed_list_In. apply H5 ; auto.
      apply In_XBoxed_list in H6. destruct H6. apply list_preserv_XBoxed_list ; apply H5 ; auto.
      destruct H6. destruct H6 ; subst. apply XBoxed_list_In. apply H5 ; auto.
      pose (PermutationTS_Canopy _ _ H4 _ i0). destruct s0. destruct p0.
      epose (list_conj_wkn_L _ (_,_) (N p x x1)). apply g1 ; clear g1 ; simpl.
      apply InT_map_iff. exists x1 ; split ; auto.

      assert (J80: length (usable_boxes s) = length (usable_boxes x)).
      pose (leq_ub_unif s). pose (leq_ub_Canopy _ _ i). rewrite <- ub_nodupseq in l0. lia.

    (* Massage the Ns. *)
    destruct (dec_init_rules x0).
    (* The sequents x1 and x0 is initial. *)
     assert (is_init x0) ; auto.
     pose (N_spec p s x0).
     pose (GN_inv_init _  g1). rewrite <- e ; auto.
     epose (TopR _ [] []). simpl in g2 ; apply g2.
    (* The sequent x is not initial. *)
     assert (is_init x0 -> False) ; auto.
     assert (is_init x1 -> False). intro. apply H5. apply (PermutationTS_is_init _ _ (PermutationTS_sym _ _ p0) X0).
     assert (J20: GUI p x0 (UI p x0)). apply UI_GUI ; auto.
     assert (J30: GUI p x1 (UI p x1)). apply UI_GUI ; auto.
     pose (Canopy_critical _ _ i0).
     pose (Canopy_critical _ _ i1).
     destruct (Compare_dec.lt_dec (length (usable_boxes x0)) (length (usable_boxes s))).
     (* The sequent x has less usable boxes than s. *)
     pose (N_spec p s x0).
     epose (@GN_inv_noinit_lessub _ _ _ _ _ g1 H5 l (UI_spec p _)). rewrite <- e ; auto.
     assert (J40: length (usable_boxes x1) < length (usable_boxes x)). rewrite <- J80 ; auto.
     assert (incl (usable_boxes x1) (usable_boxes x0)). intros A HA.
     apply InT_In ; apply In_InT in HA. apply (PermutationTS_usable_boxes _ _ (PermutationTS_sym _ _ p0)) ; auto.
     pose (NoDup_incl_length (NoDup_usable_boxes x1) H7).
     assert (incl (usable_boxes x0) (usable_boxes x1)). intros A HA.
     apply InT_In ; apply In_InT in HA. apply (PermutationTS_usable_boxes _ _ p0) ; auto.
     pose (NoDup_incl_length (NoDup_usable_boxes x0) H8). lia.
     pose (N_spec p x x1).
     epose (@GN_inv_noinit_lessub _ _ _ _ _ g2 H6 J40 (UI_spec p _)). rewrite <- e0 ; auto.
     apply PermutationTS_UI ; apply PermutationTS_sym ; auto.
     (* The sequent x does not have less usable boxes than s. *)
     pose (N_spec p s x0).
     assert (J41: Gimap (GUI p) (GLR_prems (nodupseq x0)) (map (UI p) (GLR_prems (nodupseq x0)))).
     apply Gimap_map ; auto. intros ; apply UI_GUI ; auto.
     epose (@GN_inv_noinit_nolessub _ _ _ _ _ g1 H5 n0 J41). rewrite <- e ; auto.
     assert (J42: (length (usable_boxes x1) < length (usable_boxes x)) -> False). rewrite <- J80.
     assert (incl (usable_boxes x1) (usable_boxes x0)). intros A HA.
     apply InT_In ; apply In_InT in HA. apply (PermutationTS_usable_boxes _ _ (PermutationTS_sym _ _ p0)) ; auto.
     pose (NoDup_incl_length (NoDup_usable_boxes x1) H7).
     assert (incl (usable_boxes x0) (usable_boxes x1)). intros A HA.
     apply InT_In ; apply In_InT in HA. apply (PermutationTS_usable_boxes _ _ p0) ; auto.
     pose (NoDup_incl_length (NoDup_usable_boxes x0) H8). lia.
     pose (N_spec p x x1).
     assert (J43: Gimap (GUI p) (GLR_prems (nodupseq x1)) (map (UI p) (GLR_prems (nodupseq x1)))).
     apply Gimap_map ; auto. intro ; apply UI_GUI ; auto.
     epose (@GN_inv_noinit_nolessub _ _ _ _ _ g2 H6 J42 J43). rewrite <- e0 ; auto.

       (* Proof-theoretic work. *)
       epose (OrL (_,_)). simpl in g3. apply g3 ; clear g3.
       epose (OrR (_,[])). simpl in g3. apply g3 ; clear g3.
       epose (list_disj_L _ (_,_)). simpl in g3. apply g3 ; clear g3. intros.
       epose (list_disj_wkn_R _ (_,_) A). apply g3 ; clear g3.
       apply PermutationTS_restr_list_prop_snd with (s:=x1) ; auto. apply PermutationTS_sym ; auto.
       simpl. epose (Id_all_form _ [] _ [] _). simpl in d ; apply d.
       epose (OrL (_,_)). simpl in g3. apply g3 ; clear g3.
       epose (OrR (_,[])). simpl in g3. apply g3 ; clear g3.
       pose (@GLS_prv_wkn_R ([list_disj (map Neg (restr_list_prop p (fst x1)))],[Or (list_disj (map Neg (restr_list_prop p (fst x0)))) (list_disj (map Box (map (UI p) (GLR_prems (nodupseq x0)))))])).
       apply g3 with (A:=list_disj (restr_list_prop p (snd x0))). clear g3.
       2: epose (wkn_RI _ _ []) ; simpl in w ; apply w.
       epose (OrR (_,[])). simpl in g3. apply g3 ; clear g3.
       epose (list_disj_L _ (_,_)). simpl in g3. apply g3 ; clear g3. intros.
       epose (list_disj_wkn_R _ (_,_) A). apply g3 ; clear g3.
       apply InT_map_iff. apply InT_map_iff in H7. destruct H7. destruct p1 ; subst.
       exists x2 ; split ; auto.
       apply PermutationTS_restr_list_prop_fst with (s:=x1) ; auto. apply PermutationTS_sym ; auto.
       simpl. epose (Id_all_form _ [] _ [] _). simpl in d ; apply d.
       epose (OrR (_,[])). simpl in g3. apply g3 ; clear g3.
       pose (@GLS_prv_wkn_R ([list_disj (map Box (map (UI p) (GLR_prems (nodupseq x1))))],[Or (list_disj (map Neg (restr_list_prop p (fst x0)))) (list_disj (map Box (map (UI p) (GLR_prems (nodupseq x0)))))])).
       apply g3 with (A:=list_disj (restr_list_prop p (snd x0))). clear g3.
       2: epose (wkn_RI _ _ []) ; simpl in w ; apply w.
       epose (OrR (_,[])). simpl in g3. apply g3 ; clear g3.
       pose (@GLS_prv_wkn_R ([list_disj (map Box (map (UI p) (GLR_prems (nodupseq x1))))],[(list_disj (map Box (map (UI p) (GLR_prems (nodupseq x0)))))])).
       apply g3 with (A:=list_disj (map Neg (restr_list_prop p (fst x0)))). clear g3.
       2: epose (wkn_RI _ _ []) ; simpl in w ; apply w.
       epose (list_disj_L _ (_,_)). simpl in g3. apply g3 ; clear g3. intros.
       apply InT_map_iff in H7. destruct H7. destruct p1 ; subst.
       apply InT_map_iff in i2. destruct i2. destruct p1 ; subst.
       pose (PermutationTS_GLR_prems _ _ (PermutationTS_nodupseq _ _ (PermutationTS_sym _ _ p0)) _ i2).
       destruct s0. destruct p1.
       epose (list_disj_wkn_R _ (_,_) (Box (UI p x2))). apply g3 ; clear g3.
       apply InT_map_iff. exists (UI p x2) ; split ; auto.
       apply InT_map_iff. exists x2 ; split ; auto. simpl.
       apply derI with (ps:=[([UI p x3 ; Box (UI p x3) ; Box (UI p x2)], [UI p x2])]).
       apply GLR. epose (@GLRRule_I _ [Box (UI p x3)] _ [] []). simpl in g3. apply g3 ; clear g3.
       intros A HA. inversion HA ; subst. eexists ; auto. inversion H7. apply univ_gen_ext_refl.
       apply dlCons. 2: apply dlNil.
       pose (PermutationTS_UI _ _ p p1).
       pose (@GLS_prv_list_wkn_L [UI p x3] [] [UI p x2] g3 [Box (UI p x3); Box (UI p x2)]). simpl in g4.
       auto.

      epose (GLS_prv_list_wkn_L [_] [] _ _). rewrite app_nil_r in g1 ; simpl in g1. apply g1.
      Unshelve. apply GUI_fun. rewrite app_nil_r ; auto. } }
  Qed.
