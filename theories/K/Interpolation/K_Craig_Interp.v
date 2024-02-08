(* It took me a day and a half of work to write the file below
    (14-15/11/2022). *)

Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import KS_export.
Require Import general_export.

Set Implicit Arguments.

(* Material to define Craig interpolants. *)

Fixpoint propvar_subform (φ : MPropF) : list MPropF :=
match φ with
  | Var p => (Var p) :: nil 
  | Bot => nil
  | Imp ψ χ => (propvar_subform ψ) ++ ( propvar_subform χ)
  | Box ψ => ( propvar_subform ψ)
end.

Fixpoint propvar_subform_list (l : list MPropF) : list MPropF :=
match l with
  | nil => nil
  | φ :: t => (propvar_subform φ) ++ (propvar_subform_list t)
end.

(* Lemmas about propvar_subform_list. *)

Lemma propvar_subform_list_app: forall l0 l1,
      propvar_subform_list (l0 ++ l1) = (propvar_subform_list l0) ++ (propvar_subform_list l1).
Proof.
induction l0.
- simpl. auto.
- intros. simpl. rewrite (IHl0). rewrite <- app_assoc ; auto.
Qed.

Lemma propvar_subform_list_unboxed_list : forall l A, In A (propvar_subform_list (unboxed_list l)) -> In A (propvar_subform_list l).
Proof.
induction l.
- auto.
- simpl. intros. apply in_app_or in H. destruct H. apply in_or_app ; left. destruct a ; auto.
  apply in_or_app ; auto.
Qed.

Lemma propvar_subform_list_nobox_gen_ext : forall l0 l1, nobox_gen_ext l0 l1 ->
          (forall A, In A (propvar_subform_list l0) -> In A (propvar_subform_list l1)).
Proof.
intros l0 l1 H. induction H ; auto.
- simpl ; intros. apply in_or_app. apply in_app_or in H0 ; destruct H0 ; auto.
- simpl ; intros. apply in_or_app ; auto.
Qed.

Lemma InT_var_provar : forall P Γ, InT # P Γ -> InT # P (propvar_subform_list Γ).
Proof.
induction Γ ; auto. intro. simpl. inversion H ; subst ; simpl. apply InT_eq.
apply InT_or_app ; right. auto.
Qed.

(* Craig interpolation theorem. *)

Theorem Craig_Interpolation : forall Γ0 Γ1 Δ0 Δ1,
    KS_prv (Γ0 ++ Γ1, Δ0 ++ Δ1) ->
    (existsT2 (I : MPropF), (forall p, In (Var p) (propvar_subform I) -> In (Var p) (propvar_subform_list (Γ0 ++ Δ0)) *
                                                                                                            In (Var p) (propvar_subform_list (Γ1 ++ Δ1))) *
                                   (KS_prv (Γ0, I :: Δ0)) *
                                   (KS_prv (I :: Γ1, Δ1))).
Proof.
(* Setting the statement right. *)
intros. remember (Γ0 ++ Γ1, Δ0 ++ Δ1) as s. revert Heqs.
generalize dependent Γ0. generalize dependent Γ1. generalize dependent Δ0. generalize dependent Δ1.
remember (derrec_height X) as n. revert Heqn. generalize dependent X. generalize dependent s.
generalize dependent n.

(* Using strong induction. *)
pose (strong_inductionT (fun (x:nat) => forall (s : list MPropF * list MPropF) (X : KS_prv s),
x = derrec_height X ->
forall Δ1 Δ0 Γ1 Γ0 : list MPropF,
s = (Γ0 ++ Γ1, Δ0 ++ Δ1) ->
existsT2 I : MPropF,
  (forall p, In # p (propvar_subform I) -> In (Var p) (propvar_subform_list (Γ0 ++ Δ0)) *
                                                                                                            In (Var p) (propvar_subform_list (Γ1 ++ Δ1))) * KS_prv (Γ0, I :: Δ0) *
  KS_prv (I :: Γ1, Δ1))).
apply s. clear s.

(* Start of the intuitive proof. *)
unfold KS_prv. intros n IHn s D. subst. remember D as D'. destruct D ; intros.
(* D0 is a leaf *)
- inversion f.
(* D0 ends with an application of rule *)
- inversion k.
  (* IdP *)
  * inversion H1. subst. inversion H5 ; subst. assert (J: InT (# P) (Γ0 ++ Γ1)). rewrite <- H0.
    apply InT_or_app ; right ; apply InT_eq. apply InT_app_or in J. destruct J.
    + assert (J: InT (# P) (Δ0 ++ Δ1)). rewrite <- H2.
       apply InT_or_app ; right ; apply InT_eq. apply InT_app_or in J. destruct J.
       -- exists (Bot). repeat split. intros. 1,2: inversion H.
           apply derI with (ps:=[]). 2: apply dersrec_nil. apply IdP.
           apply InT_split in i. destruct i. destruct s. subst.
           assert (J: InT # P (Bot :: Δ0)). apply InT_cons. auto.
           apply InT_split in J. destruct J. destruct s. rewrite e. apply IdPRule_I.
           apply derI with (ps:=[]). 2: apply dersrec_nil. apply BotL. apply (BotLRule_I []).
       -- exists (# P). repeat split. intros. 1,2: simpl in H ; destruct H ; auto ; try rewrite <- H. 2, 4: inversion H.
           1-2: repeat rewrite propvar_subform_list_app ; apply in_or_app. left ; apply InT_In ; apply InT_var_provar ; auto.
           right ; apply InT_In ; apply InT_var_provar ; auto.
           apply derI with (ps:=[]). 2: apply dersrec_nil. apply IdP.
           apply InT_split in i. destruct i. destruct s. subst.
           assert (J: # P :: Δ0 = [] ++ # P :: Δ0). auto. rewrite J. clear J. apply IdPRule_I.
           apply derI with (ps:=[]). 2: apply dersrec_nil. apply IdP.
           apply InT_split in i0. destruct i0. destruct s. subst.
           assert (J: # P :: Γ1 = [] ++ # P :: Γ1). auto. rewrite J. clear J. apply IdPRule_I.
    + assert (J: InT (# P) (Δ0 ++ Δ1)). rewrite <- H2.
       apply InT_or_app ; right ; apply InT_eq. apply InT_app_or in J. destruct J.
       -- exists (# P --> Bot). repeat split.
           1,2: simpl in H ; destruct H ; auto ; try rewrite <- H. 2, 4: inversion H.
           1-2: repeat rewrite propvar_subform_list_app ; apply in_or_app. right ; apply InT_In ; apply InT_var_provar ; auto.
           left ; apply InT_In ; apply InT_var_provar ; auto.
           apply derI with (ps:=[([] ++ # P :: Γ0, [] ++ Bot :: Δ0)]). apply ImpR.
           assert (J: (Γ0, # P --> Bot :: Δ0) = ([] ++ Γ0, [] ++ # P --> Bot :: Δ0)). auto. rewrite J. clear J. apply ImpRRule_I.
           apply dlCons. 2: apply dlNil. apply derI with (ps:=[]). 2: apply dersrec_nil. apply IdP.
           assert (J: InT # P ([] ++ Bot :: Δ0)). apply InT_cons. auto. apply InT_split in J. destruct J. destruct s.
           rewrite e. apply IdPRule_I.
           apply derI with (ps:=[([] ++ Γ1, [] ++ # P :: Δ1);([] ++ Bot :: Γ1, [] ++ Δ1)]). apply ImpL.
           assert (J: (# P --> Bot :: Γ1, Δ1) = ([] ++ # P --> Bot :: Γ1, [] ++ Δ1)). auto. rewrite J. clear J. apply ImpLRule_I.
           apply dlCons. apply derI with (ps:=[]). 2: apply dlNil. apply IdP.
           assert (J: InT # P ([] ++ Γ1)). simpl ; auto. apply InT_split in J. destruct J. destruct s.
           rewrite e. apply IdPRule_I. apply dlCons. 2: apply dlNil. apply derI with (ps:=[]). 2: apply dlNil. apply BotL.
           apply BotLRule_I.
       -- exists (Bot --> Bot). repeat split. intros. 1,2: inversion H.
           apply derI with (ps:=[([] ++ Bot :: Γ0, [] ++ Bot :: Δ0)]). apply ImpR.
           assert ((Γ0, Bot --> Bot :: Δ0) = ([] ++ Γ0, [] ++ Bot --> Bot :: Δ0)). auto. rewrite H. clear H.
           apply ImpRRule_I. apply dlCons. 2: apply dlNil. apply derI with (ps:=[]). apply BotL.
           apply BotLRule_I. apply dlNil.
           apply derI with (ps:=[]). 2: apply dersrec_nil. apply IdP.
           assert (J: InT # P (Bot --> Bot :: Γ1)). apply InT_cons. auto.
           apply InT_split in J. destruct J. destruct s. rewrite e.
           apply InT_split in i0. destruct i0. destruct s. subst. apply IdPRule_I.
  (* BotL *)
  * inversion H1. subst. assert (J: InT Bot (Γ0 ++ Γ1)). inversion H5 ; subst.
    apply InT_or_app ; right ; apply InT_eq. apply InT_app_or in J. destruct J.
    + exists Bot. repeat split. intros. 1,2: inversion H.
       apply derI with (ps:=[]). apply BotL. 2: apply dlNil.
       apply InT_split in i. destruct i. destruct s. subst. apply BotLRule_I.
       apply derI with (ps:=[]). apply BotL. 2: apply dlNil.
       assert (J: (Bot :: Γ1, Δ1) = ([] ++ Bot :: Γ1, Δ1)). auto. rewrite J. apply BotLRule_I.
    + exists (Bot --> Bot). repeat split. intros. 1,2: inversion H.
       apply derI with (ps:=[([] ++ Bot :: Γ0, [] ++ Bot :: Δ0)]). apply ImpR.
       assert ((Γ0, Bot --> Bot :: Δ0) = ([] ++ Γ0, [] ++ Bot --> Bot :: Δ0)). auto. rewrite H. clear H.
       apply ImpRRule_I. apply dlCons. 2: apply dlNil. apply derI with (ps:=[]). apply BotL.
       apply BotLRule_I. apply dlNil.
       apply derI with (ps:=[]). apply BotL. 2: apply dlNil.
       assert (J: InT Bot (Bot --> Bot :: Γ1)). apply InT_cons ; auto.
       apply InT_split in J. destruct J. destruct s. rewrite e. apply BotLRule_I.
  (* ImpR *)
  * inversion H1. subst. inversion H5 ; subst. simpl in IHn.
    assert (J: dersrec_height d = dersrec_height d). auto. apply dersrec_derrec_height in J.
    destruct J.
    assert (J1: derrec_height x = derrec_height x). auto.
    assert (J3: list_exch_L (Γ2 ++ A :: Γ3, Δ2 ++ B :: Δ3) (A :: Γ0 ++ Γ1, Δ2 ++ B :: Δ3)).
    rewrite <- H0. assert (Γ2 ++ A :: Γ3 = [] ++ [] ++ Γ2 ++ [A] ++ Γ3). auto. rewrite H.
    assert (A :: Γ2 ++ Γ3 = [] ++ [A] ++ Γ2 ++ [] ++ Γ3). auto. rewrite H3. apply list_exch_LI.
    pose (KS_hpadm_list_exch_L _ x _ J3). destruct s.
    assert (J5: derrec_height x0 = derrec_height x0). auto.
    assert (J4: list_exch_L (A :: Γ0 ++ Γ1, Δ2 ++ B :: Δ3) (Γ0 ++ A :: Γ1, Δ2 ++ B :: Δ3)).
    assert (Γ0 ++ A :: Γ1 = [] ++ [] ++ Γ0 ++ [A] ++ Γ1). auto. rewrite H.
    assert (A :: Γ0 ++ Γ1 = [] ++ [A] ++ Γ0 ++ [] ++ Γ1). auto. rewrite H3. apply list_exch_LI.
    pose (KS_hpadm_list_exch_L _ x0 _ J4). destruct s.
    assert (J0: derrec_height x1 < S (dersrec_height d)). rewrite <- e. apply Arith_prebase.le_lt_n_Sm.
    apply (Nat.le_trans _ _ _ l0 l).
    assert (J6: derrec_height x1 = derrec_height x1). auto.
    pose (IHn _ J0 _ _ J6).
    apply app2_find_hole in H2. destruct H2. repeat destruct s0 ; destruct p ; subst.
    +  assert (J2: (Γ0 ++ A :: Γ1, Δ2 ++ B :: Δ3) = (Γ0 ++ (A :: Γ1), Δ2 ++ (B :: Δ3))). auto.
        apply s in J2. destruct J2. destruct p. destruct p. exists x3. repeat split ; auto.
        intros. apply p in H. repeat rewrite propvar_subform_list_app in H. simpl in H.
        repeat rewrite propvar_subform_list_app. repeat rewrite <- app_assoc in H. simpl. destruct H.
        apply in_app_or in i. destruct i. apply in_or_app ; auto. apply in_or_app ; auto.
        apply p in H. repeat rewrite propvar_subform_list_app in H. simpl in H.
        repeat rewrite propvar_subform_list_app. repeat rewrite <- app_assoc in H. simpl. destruct H.
        apply in_app_or in i0. destruct i0. apply in_or_app ; right ; apply in_or_app ; left ; apply in_or_app ; auto.
        apply in_app_or in H. destruct H. apply in_or_app ; auto.
        apply in_app_or in H. destruct H. apply in_or_app ; right ; apply in_or_app ; left ; apply in_or_app ; auto.
        apply in_or_app ; right ; apply in_or_app ; auto. 
        apply derI with (ps:=[(x3 :: A :: Γ1, B :: Δ3)]). apply ImpR.
        assert ((x3 :: Γ1, A --> B :: Δ3) = ([x3] ++ Γ1, [] ++ A --> B :: Δ3)). auto. rewrite H.
        assert ((x3 :: A :: Γ1, B :: Δ3) = ([x3] ++ A :: Γ1, [] ++ B :: Δ3)). auto. rewrite H2. apply ImpRRule_I.
        apply dlCons ; auto. apply dlNil.
    +  destruct x2 ; subst.
        -- simpl in e1. subst. rewrite <- app_nil_end.
            assert (J2: (Γ0 ++ A :: Γ1, Δ2 ++ B :: Δ3) = (Γ0 ++ (A :: Γ1), Δ2 ++ (B :: Δ3))). auto.
            apply s in J2. destruct J2. destruct p. destruct p. exists x2. repeat split ; auto.
            intros. apply p in H. repeat rewrite propvar_subform_list_app in H. simpl in H. repeat rewrite <- app_assoc in H.
            repeat rewrite propvar_subform_list_app. simpl. destruct H. auto.
            apply p in H. repeat rewrite propvar_subform_list_app in H. simpl in H. repeat rewrite <- app_assoc in H.
            repeat rewrite propvar_subform_list_app. simpl. destruct H.
            apply in_app_or in i0. destruct i0. apply in_or_app ; right ; apply in_or_app ; left ; apply in_or_app ; auto.
            apply in_app_or in H ; destruct H. apply in_or_app ; auto. apply in_app_or in H ; destruct H.
            apply in_or_app ; right ; apply in_or_app ; left ; apply in_or_app ; auto.
            apply in_or_app ; right ; apply in_or_app ; right ; auto.
            apply derI with (ps:=[(x2 :: A :: Γ1, B :: Δ3)]). apply ImpR.
            assert ((x2 :: Γ1, A --> B :: Δ3) = ([x2] ++ Γ1, [] ++ A --> B :: Δ3)). auto. rewrite H.
            assert ((x2 :: A :: Γ1, B :: Δ3) = ([x2] ++ A :: Γ1, [] ++ B :: Δ3)). auto. rewrite H2. apply ImpRRule_I.
            apply dlCons ; auto. apply dlNil.
        -- inversion e1. subst.
            assert (J2: (Γ0 ++ A :: Γ1, Δ2 ++ B :: x2 ++ Δ1) = ((Γ0 ++ [A]) ++ Γ1, (Δ2 ++ B :: x2) ++ Δ1)).
            repeat rewrite <- app_assoc ; auto.
            apply s in J2. destruct J2. destruct p. destruct p. exists x3. repeat split ; auto.
            intros. apply p in H. simpl in H. repeat rewrite <- app_assoc in H ; simpl in H.
            repeat rewrite propvar_subform_list_app in H. simpl in H. repeat rewrite propvar_subform_list_app in H. simpl in H.
            destruct H.
            repeat rewrite propvar_subform_list_app. simpl. repeat rewrite propvar_subform_list_app. simpl.
            apply in_app_or in i. destruct i. apply in_or_app ; auto. apply in_app_or in H ; destruct H.
            apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; left ; apply in_or_app ; auto.
            apply in_app_or in H ; destruct H. apply in_or_app ; right ; apply in_or_app ; auto.
            apply in_app_or in H ; destruct H. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; left ; apply in_or_app ; auto.
            apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
            intros. apply p in H. simpl in H. repeat rewrite <- app_assoc in H ; simpl in H.
            repeat rewrite propvar_subform_list_app in H. simpl in H. repeat rewrite propvar_subform_list_app in H. simpl in H.
            destruct H. repeat rewrite propvar_subform_list_app.
            apply in_app_or in i0. destruct i0. 1-2: apply in_or_app ; auto.
            apply derI with (ps:=[(Γ0 ++ A :: [], (x3 :: Δ2) ++ B :: x2)]). apply ImpR.
            assert ((Γ0, x3 :: Δ2 ++ A --> B :: x2) = (Γ0 ++ [], (x3 :: Δ2) ++ A --> B :: x2)). rewrite <- app_nil_end. auto.
            rewrite H. apply ImpRRule_I. apply dlCons ; auto. apply dlNil.
    +  assert (J2: (Γ0 ++ A :: Γ1, (Δ0 ++ x2) ++ B :: Δ3) = (Γ0 ++ (A :: Γ1), Δ0 ++ (x2)++ B :: Δ3)). repeat rewrite <- app_assoc. auto.
        apply s in J2. destruct J2. destruct p. destruct p. exists x3. repeat split ; auto.
        intros. 1,2: apply p in H ; simpl in H ; repeat rewrite <- app_assoc in H ; simpl in H ;
        repeat rewrite propvar_subform_list_app in H ; simpl in H ; repeat rewrite propvar_subform_list_app in H ; simpl in H ;
        destruct H ;  repeat rewrite propvar_subform_list_app ; simpl ; repeat rewrite propvar_subform_list_app ; simpl.
        apply in_app_or in i. destruct i. 1,2: apply in_or_app ; auto.
        apply in_app_or in i0. destruct i0. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; left ; apply in_or_app ; auto.
        apply in_app_or in H ; destruct H. apply in_or_app ; auto. apply in_app_or in H ; destruct H. 
        apply in_or_app ; right ; apply in_or_app ; auto. apply in_app_or in H ; destruct H.
        apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; left ; apply in_or_app ; auto.
        apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; auto.
        apply derI with (ps:=[(x3 :: A :: Γ1, x2 ++ B :: Δ3)]). apply ImpR.
        assert ((x3 :: Γ1, x2 ++ A --> B :: Δ3) = ([x3] ++ Γ1, x2 ++ A --> B :: Δ3)). auto. rewrite H.
        assert ((x3 :: A :: Γ1, x2 ++ B :: Δ3) = ([x3] ++ A :: Γ1, x2 ++ B :: Δ3)). auto. rewrite H2. apply ImpRRule_I.
        apply dlCons ; auto. apply dlNil.
  (* ImpL *)
  * inversion H1. subst. inversion H5 ; subst. simpl in IHn.
    assert (J: dersrec_height d = dersrec_height d). auto. apply dersrec_derrec2_height in J.
    destruct J. destruct s.
    assert (J1: derrec_height x = derrec_height x). auto.
    assert (J3: list_exch_R (Γ2 ++ Γ3, Δ2 ++ A :: Δ3) (Γ2 ++ Γ3, A :: Δ0 ++ Δ1)).
    rewrite <- H2. assert (Δ2 ++ A :: Δ3 = [] ++ [] ++ Δ2 ++ [A] ++ Δ3). auto. rewrite H.
    assert (A :: Δ2 ++ Δ3 = [] ++ [A] ++ Δ2 ++ [] ++ Δ3). auto. rewrite H3. apply list_exch_RI.
    pose (KS_hpadm_list_exch_R _ x _ J3). destruct s.
    assert (J5: derrec_height x1 = derrec_height x1). auto.
    assert (J4: list_exch_R (Γ2 ++ Γ3, A :: Δ0 ++ Δ1) (Γ2 ++ Γ3, Δ0 ++ A :: Δ1)).
    assert (Δ0 ++ A :: Δ1 = [] ++ [] ++ Δ0 ++ [A] ++ Δ1). auto. rewrite H.
    assert (A :: Δ0 ++ Δ1 = [] ++ [A] ++ Δ0 ++ [] ++ Δ1). auto. rewrite H3. apply list_exch_RI.
    pose (KS_hpadm_list_exch_R _ x1 _ J4). destruct s.
    assert (existsT2 (x3 : derrec KS_rules (fun _ : Seq => False) (Γ2 ++ B :: Γ3, Δ0 ++ Δ1)), derrec_height x3 <= dersrec_height d).
    rewrite <- H2. exists x0 ; auto. rewrite e. apply Nat.le_max_r. destruct X.
    apply app2_find_hole in H0. destruct H0. repeat destruct s ; destruct p ; subst.
    +  assert (J11: derrec_height x2 < S (dersrec_height d)). rewrite e. apply Arith_prebase.le_lt_n_Sm.
        apply Nat.max_le_iff. left. apply (Nat.le_trans _ _ _ l0 l).
        assert (J12: derrec_height x2 = derrec_height x2). auto.
        pose (IHn _ J11 _ _ J12).
        assert (J2: (Γ2 ++ Γ3, Δ0 ++ A :: Δ1) = (Γ2 ++ Γ3, Δ0 ++ A :: Δ1)). auto.
        apply s in J2. destruct J2. destruct p. destruct p.
        assert (J13: derrec_height x3 < S (dersrec_height d)). lia.
        assert (J14: derrec_height x3 = derrec_height x3). auto.
        pose (IHn _ J13 _ _ J14).
        assert (J2: (Γ2 ++ B :: Γ3, Δ0 ++ Δ1) = (Γ2 ++ B :: Γ3, Δ0 ++ Δ1)). auto.
        apply s0 in J2. destruct J2. destruct p0. destruct p0.
        exists ((x5 --> (x6 --> Bot)) --> Bot). repeat split.
        intros. 1,2: simpl in H ; repeat rewrite <- app_nil_end in H ; repeat rewrite propvar_subform_list_app ; simpl ;
        repeat rewrite <- app_assoc ; apply in_app_or in H ; destruct H.
        apply p in H ; repeat rewrite propvar_subform_list_app in H ; simpl in H ; destruct H ; auto.
        apply p0 in H ; repeat rewrite propvar_subform_list_app in H ; simpl in H ; repeat rewrite <- app_assoc in H ; destruct H ; auto.
        apply p in H ; repeat rewrite propvar_subform_list_app in H ; simpl in H ; destruct H ; auto.
        apply in_app_or in i0 ; destruct i0. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
        apply in_app_or in H ; destruct H. apply in_or_app ; auto.
        apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; auto.
        apply p0 in H ; repeat rewrite propvar_subform_list_app in H ; simpl in H ; repeat rewrite <- app_assoc in H ; destruct H ; auto.
        apply in_app_or in i0 ; destruct i0. apply in_or_app ; right ; apply in_or_app ; auto.
        apply in_app_or in H ; destruct H. 1,2: apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
        apply derI with (ps:=[([] ++ (x5 --> x6 --> Bot) :: Γ2, [] ++ Bot :: Δ0)]). apply ImpR.
        assert ((Γ2, (x5 --> x6 --> Bot) --> Bot :: Δ0) = ([] ++ Γ2, [] ++ (x5 --> x6 --> Bot) --> Bot :: Δ0)). auto. rewrite H. apply ImpRRule_I.
        apply dlCons. 2: apply dlNil.
        apply derI with (ps:=[([] ++ Γ2, [] ++ x5 :: Bot :: Δ0);([] ++ x6 --> Bot :: Γ2, [] ++ Bot :: Δ0)]). apply ImpL. apply ImpLRule_I.
        apply dlCons. simpl.
        assert (J15: derrec_height d1 = derrec_height d1). auto.
        assert (J16: wkn_R Bot (Γ2, [x5] ++ Δ0) (Γ2, [x5] ++ Bot :: Δ0)). apply wkn_RI. simpl in J16.
        pose (KS_wkn_R _ _ d1 J15 _ _ J16). destruct s1 ; auto. apply dlCons. 2: apply dlNil.
        apply derI with (ps:=[([] ++ Γ2, [] ++ x6 :: Bot :: Δ0);([] ++ Bot :: Γ2, [] ++ Bot :: Δ0)]). apply ImpL. apply ImpLRule_I.
        apply dlCons. simpl.
        assert (J15: derrec_height d3 = derrec_height d3). auto.
        assert (J16: wkn_R Bot (Γ2, [x6] ++ Δ0) (Γ2, [x6] ++ Bot :: Δ0)). apply wkn_RI. simpl in J16.
        pose (KS_wkn_R _ _ d3 J15 _ _ J16). destruct s1 ; auto.
        apply dlCons. 2: apply dlNil. apply derI with (ps:=[]). apply BotL. apply BotLRule_I. apply dlNil.
        apply derI with (ps:=[([] ++ A --> B :: Γ3, [] ++ (x5 --> x6 --> Bot) :: Δ1);([] ++ Bot :: A --> B :: Γ3, [] ++ Δ1)]).
        assert (((x5 --> x6 --> Bot) --> Bot :: A --> B :: Γ3, Δ1) = ([] ++ (x5 --> x6 --> Bot) --> Bot :: A --> B :: Γ3, [] ++ Δ1)). auto.
        rewrite H. apply ImpL. apply ImpLRule_I. apply dlCons.
        apply derI with (ps:=[([] ++ x5 :: A --> B :: Γ3, [] ++ x6 --> Bot :: Δ1)]). apply ImpR. apply ImpRRule_I. apply dlCons.
        apply derI with (ps:=[([x5] ++ Γ3, [] ++ A :: x6 --> Bot :: Δ1);([x5] ++ B :: Γ3, [] ++ x6 --> Bot :: Δ1)]).
        assert (([] ++ x5 :: A --> B :: Γ3, [] ++ x6 --> Bot :: Δ1) = ([x5] ++ A --> B :: Γ3, [] ++ x6 --> Bot :: Δ1)). auto.
        rewrite H. apply ImpL. apply ImpLRule_I. apply dlCons. 3: apply dlNil.
        assert (J15: derrec_height d0 = derrec_height d0). auto. simpl.
        assert (J16: wkn_R (x6 --> Bot) (x5 :: Γ3, [A]++ Δ1) (x5 :: Γ3, [A] ++ x6 --> Bot :: Δ1)). apply wkn_RI. simpl in J16.
        pose (KS_wkn_R _ _ d0 J15 _ _ J16). destruct s1 ; auto. apply dlCons. 2: apply dlNil.
        apply derI with (ps:=[([x5] ++ x6 :: B :: Γ3, [] ++ Bot :: Δ1)]). apply ImpR. apply ImpRRule_I. apply dlCons.
        assert (J15: derrec_height d2 = derrec_height d2). auto. simpl.
        assert (J16: wkn_R Bot (x6 :: B :: Γ3, [] ++ Δ1) (x6 :: B :: Γ3, [] ++ Bot :: Δ1)). apply wkn_RI. simpl in J16.
        pose (KS_wkn_R _ _ d2 J15 _ _ J16). destruct s1.
        assert (J17: derrec_height x7 = derrec_height x7). auto. simpl.
        assert (J18: wkn_L x5 ([] ++ x6 :: B :: Γ3, Bot :: Δ1) ([] ++ x5 :: x6 :: B :: Γ3, Bot :: Δ1)). apply wkn_LI. simpl in J18.
        pose (KS_wkn_L _ _ x7 J17 _ _ J18). destruct s1. auto. apply dlNil. apply dlCons. 2: apply dlNil.
        apply derI with (ps:=[]). apply BotL. apply BotLRule_I. apply dlNil.
    +  destruct x4.
      --  simpl. repeat rewrite <- app_nil_end. simpl in e1. subst.
          assert (J11: derrec_height x2 < S (dersrec_height d)). rewrite e. apply Arith_prebase.le_lt_n_Sm.
          apply Nat.max_le_iff. left. apply (Nat.le_trans _ _ _ l0 l).
          assert (J12: derrec_height x2 = derrec_height x2). auto.
          pose (IHn _ J11 _ _ J12).
          assert (J2: (Γ2 ++ Γ3, Δ0 ++ A :: Δ1) = (Γ2 ++ Γ3, Δ0 ++ A :: Δ1)). auto.
          apply s in J2. destruct J2. destruct p. destruct p.
          assert (J13: derrec_height x3 < S (dersrec_height d)). lia.
          assert (J14: derrec_height x3 = derrec_height x3). auto.
          pose (IHn _ J13 _ _ J14).
          assert (J2: (Γ2 ++ B :: Γ3, Δ0 ++ Δ1) = (Γ2 ++ B :: Γ3, Δ0 ++ Δ1)). auto.
          apply s0 in J2. destruct J2. destruct p0. destruct p0.
          exists ((x4 --> (x5 --> Bot)) --> Bot). repeat split.
          intros. 1,2: simpl in H ; repeat rewrite <- app_nil_end in H ; repeat rewrite propvar_subform_list_app ; simpl ;
          repeat rewrite <- app_assoc ; apply in_app_or in H ; destruct H.
          apply p in H ; repeat rewrite propvar_subform_list_app in H ; simpl in H ; destruct H ; auto.
          apply p0 in H ; repeat rewrite propvar_subform_list_app in H ; simpl in H ; repeat rewrite <- app_assoc in H ; destruct H ; auto.
          apply p in H ; repeat rewrite propvar_subform_list_app in H ; simpl in H ; destruct H ; auto.
          apply in_app_or in i0 ; destruct i0. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
          apply in_app_or in H ; destruct H. apply in_or_app ; auto.
          apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; auto.
          apply p0 in H ; repeat rewrite propvar_subform_list_app in H ; simpl in H ; repeat rewrite <- app_assoc in H ; destruct H ; auto.
          apply in_app_or in i0 ; destruct i0. apply in_or_app ; right ; apply in_or_app ; auto.
          apply in_app_or in H ; destruct H. 1,2: apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
          apply derI with (ps:=[([] ++ (x4 --> x5 --> Bot) :: Γ2, [] ++ Bot :: Δ0)]). apply ImpR.
          assert ((Γ2, (x4 --> x5 --> Bot) --> Bot :: Δ0) = ([] ++ Γ2, [] ++ (x4 --> x5 --> Bot) --> Bot :: Δ0)). auto. rewrite H. apply ImpRRule_I.
          apply dlCons. 2: apply dlNil.
          apply derI with (ps:=[([] ++ Γ2, [] ++ x4 :: Bot :: Δ0);([] ++ x5 --> Bot :: Γ2, [] ++ Bot :: Δ0)]). apply ImpL. apply ImpLRule_I.
          apply dlCons. simpl.
          assert (J15: derrec_height d1 = derrec_height d1). auto.
          assert (J16: wkn_R Bot (Γ2, [x4] ++ Δ0) (Γ2, [x4] ++ Bot :: Δ0)). apply wkn_RI. simpl in J16.
          pose (KS_wkn_R _ _ d1 J15 _ _ J16). destruct s1 ; auto. apply dlCons. 2: apply dlNil.
          apply derI with (ps:=[([] ++ Γ2, [] ++ x5 :: Bot :: Δ0);([] ++ Bot :: Γ2, [] ++ Bot :: Δ0)]). apply ImpL. apply ImpLRule_I.
          apply dlCons. simpl.
          assert (J15: derrec_height d3 = derrec_height d3). auto.
          assert (J16: wkn_R Bot (Γ2, [x5] ++ Δ0) (Γ2, [x5] ++ Bot :: Δ0)). apply wkn_RI. simpl in J16.
          pose (KS_wkn_R _ _ d3 J15 _ _ J16). destruct s1 ; auto.
          apply dlCons. 2: apply dlNil. apply derI with (ps:=[]). apply BotL. apply BotLRule_I. apply dlNil.
          apply derI with (ps:=[([] ++ A --> B :: Γ3, [] ++ (x4 --> x5 --> Bot) :: Δ1);([] ++ Bot :: A --> B :: Γ3, [] ++ Δ1)]).
          assert (((x4 --> x5 --> Bot) --> Bot :: A --> B :: Γ3, Δ1) = ([] ++ (x4 --> x5 --> Bot) --> Bot :: A --> B :: Γ3, [] ++ Δ1)). auto.
          rewrite H. apply ImpL. apply ImpLRule_I. apply dlCons.
          apply derI with (ps:=[([] ++ x4 :: A --> B :: Γ3, [] ++ x5 --> Bot :: Δ1)]). apply ImpR. apply ImpRRule_I. apply dlCons.
          apply derI with (ps:=[([x4] ++ Γ3, [] ++ A :: x5 --> Bot :: Δ1);([x4] ++ B :: Γ3, [] ++ x5 --> Bot :: Δ1)]).
          assert (([] ++ x4 :: A --> B :: Γ3, [] ++ x5 --> Bot :: Δ1) = ([x4] ++ A --> B :: Γ3, [] ++ x5 --> Bot :: Δ1)). auto.
          rewrite H. apply ImpL. apply ImpLRule_I. apply dlCons. 3: apply dlNil.
          assert (J15: derrec_height d0 = derrec_height d0). auto. simpl.
          assert (J16: wkn_R (x5 --> Bot) (x4 :: Γ3, [A]++ Δ1) (x4 :: Γ3, [A] ++ x5 --> Bot :: Δ1)). apply wkn_RI. simpl in J16.
          pose (KS_wkn_R _ _ d0 J15 _ _ J16). destruct s1 ; auto. apply dlCons. 2: apply dlNil.
          apply derI with (ps:=[([x4] ++ x5 :: B :: Γ3, [] ++ Bot :: Δ1)]). apply ImpR. apply ImpRRule_I. apply dlCons.
          assert (J15: derrec_height d2 = derrec_height d2). auto. simpl.
          assert (J16: wkn_R Bot (x5 :: B :: Γ3, [] ++ Δ1) (x5 :: B :: Γ3, [] ++ Bot :: Δ1)). apply wkn_RI. simpl in J16.
          pose (KS_wkn_R _ _ d2 J15 _ _ J16). destruct s1.
          assert (J17: derrec_height x6 = derrec_height x6). auto. simpl.
          assert (J18: wkn_L x4 ([] ++ x5 :: B :: Γ3, Bot :: Δ1) ([] ++ x4 :: x5 :: B :: Γ3, Bot :: Δ1)). apply wkn_LI. simpl in J18.
          pose (KS_wkn_L _ _ x6 J17 _ _ J18). destruct s1. auto. apply dlNil. apply dlCons. 2: apply dlNil.
          apply derI with (ps:=[]). apply BotL. apply BotLRule_I. apply dlNil.
      --  repeat rewrite <- app_assoc. simpl. simpl in e1. inversion e1. subst.
          assert (J13: derrec_height x3 < S (dersrec_height d)). lia.
          assert (J14: derrec_height x3 = derrec_height x3). auto.
          pose (IHn _ J13 _ _ J14).
          assert (J2: (Γ2 ++ B :: x4 ++ Γ1, Δ0 ++ Δ1) = ((Γ2 ++ B :: x4) ++ Γ1, Δ0 ++ Δ1)). repeat rewrite <- app_assoc. auto.
          apply s in J2. destruct J2. destruct p. destruct p.
          assert (J7: derrec_height x2 = derrec_height x2). auto.
          assert (J8: list_exch_R (Γ2 ++ x4 ++ Γ1, Δ0 ++ A :: Δ1) (Γ2 ++ x4 ++ Γ1, Δ1 ++ A :: Δ0)).
          assert (Δ0 ++ A :: Δ1 = [] ++ Δ0 ++ [A] ++ Δ1 ++ []). rewrite <- app_nil_end. auto. rewrite H.
          assert (Δ1 ++ A :: Δ0 = [] ++ Δ1 ++ [A] ++ Δ0 ++ []). rewrite <- app_nil_end. auto. rewrite H0. apply list_exch_RI.
          pose (KS_hpadm_list_exch_R _ x2 _ J8). destruct s0.
          assert (J9: derrec_height x6 = derrec_height x6). auto.
          assert (J10: list_exch_L (Γ2 ++ x4 ++ Γ1, Δ1 ++ A :: Δ0) (Γ1 ++ x4 ++ Γ2, Δ1 ++ A :: Δ0)).
          assert (Γ2 ++ x4 ++ Γ1 = [] ++ Γ2 ++ x4 ++ Γ1 ++ []). rewrite <- app_nil_end. auto. rewrite H.
          assert (Γ1 ++ x4 ++ Γ2 = [] ++ Γ1 ++ x4 ++ Γ2 ++ []). rewrite <- app_nil_end. auto. rewrite H0. apply list_exch_LI.
          pose (KS_hpadm_list_exch_L _ x6 _ J10). destruct s0.
          assert (J11: derrec_height x7 < S (dersrec_height d)). rewrite e. apply Arith_prebase.le_lt_n_Sm.
          apply Nat.max_le_iff. left. pose (Nat.le_trans _ _ _ l0 l). pose (Nat.le_trans _ _ _ l2 l4). apply (Nat.le_trans _ _ _ l3 l5).
          assert (J12: derrec_height x7 = derrec_height x7). auto.
          pose (IHn _ J11 _ _ J12).
          assert (J2: (Γ1 ++ x4 ++ Γ2, Δ1 ++ A :: Δ0) = (Γ1 ++ x4 ++ Γ2, Δ1 ++ A :: Δ0)). auto.
          apply s0 in J2. destruct J2. destruct p0. destruct p0.
          exists (x8 --> x5). repeat split.
          intros. 1,2: simpl in H ; repeat rewrite <- app_nil_end in H ; repeat rewrite propvar_subform_list_app ; simpl ;
          repeat rewrite propvar_subform_list_app ; simpl ;repeat rewrite <- app_assoc ; apply in_app_or in H ; destruct H.
          apply p0 in H ; repeat rewrite propvar_subform_list_app in H ; simpl in H ; repeat rewrite <- app_assoc in H ; destruct H ; auto.
          apply in_app_or in i0 ; destruct i0. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
          apply in_app_or in H ; destruct H. apply in_or_app ; auto. apply in_app_or in H ; destruct H.
          apply in_or_app ; right ; apply in_or_app ; auto. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
          apply p in H ; repeat rewrite propvar_subform_list_app in H ; simpl in H ; destruct H ; repeat rewrite <- app_assoc in i.
          apply in_app_or in i ; destruct i. apply in_or_app ; auto. apply in_app_or in H ; destruct H.
          apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.  apply in_app_or in H ; destruct H.
          apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
          apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
          apply p0 in H ; repeat rewrite propvar_subform_list_app in H ; simpl in H ; repeat rewrite <- app_assoc in H ; destruct H ; auto.
          apply p in H ; repeat rewrite propvar_subform_list_app in H ; simpl in H ; destruct H ; auto.
          apply derI with (ps:=[(Γ2 ++ x8 :: A --> B :: x4, [] ++ x5 :: Δ0)]). apply ImpR.
          assert ((Γ2 ++ A --> B :: x4, x8 --> x5 :: Δ0) = (Γ2 ++ A --> B :: x4, [] ++ x8 --> x5 :: Δ0)). auto. rewrite H. apply ImpRRule_I.
          apply dlCons. 2: apply dlNil.
          apply derI with (ps:=[((Γ2 ++ [x8]) ++ x4, [] ++ A :: x5 :: Δ0);((Γ2 ++ [x8]) ++ B :: x4, [] ++ x5 :: Δ0)]). apply ImpL.
          assert ((Γ2 ++ x8 :: A --> B :: x4, [] ++ x5 :: Δ0) = ((Γ2 ++ [x8]) ++ A --> B :: x4, [] ++ x5 :: Δ0)). repeat rewrite <- app_assoc. auto.
          rewrite H. apply ImpLRule_I. apply dlCons. repeat rewrite <- app_assoc. simpl.
          assert (J15: derrec_height d2 = derrec_height d2). auto.
          pose (@KS_list_wkn_R (derrec_height d2) (x8 :: x4 ++ Γ2) [A] Δ0). simpl in s1.
          pose (s1 d2 J15 [x5]). simpl in s2. destruct s2.
          assert (J16: derrec_height x9 = derrec_height x9). auto.
          assert (J17: list_exch_L (x8 :: x4 ++ Γ2, A :: x5 :: Δ0) (Γ2 ++ x8 :: x4, A :: x5 :: Δ0)).
          assert (x8 :: x4 ++ Γ2 = [] ++ (x8 :: x4) ++ [] ++ Γ2 ++ []). rewrite <- app_nil_end. auto. rewrite H.
          assert (Γ2 ++ x8 :: x4 = [] ++ Γ2 ++ [] ++ (x8 :: x4) ++ []). rewrite <- app_nil_end. auto. rewrite H0. apply list_exch_LI.
          pose (KS_hpadm_list_exch_L _ x9 _ J17). destruct s2. auto.
          simpl. repeat rewrite <- app_assoc. simpl.
          assert (J17: derrec_height d1 = derrec_height d1). auto. simpl. apply dlCons. 2: apply dlNil.
          assert (J18: wkn_L x8 (Γ2 ++ B :: x4, x5 :: Δ0) (Γ2 ++ x8 :: B :: x4, x5 :: Δ0)). apply wkn_LI.
          pose (KS_wkn_L _ _ d1 J17 _ _ J18). destruct s1. auto.
          apply derI with (ps:=[([] ++ Γ1, [] ++ x8 :: Δ1);([] ++ x5 :: Γ1, [] ++ Δ1)]).
          assert ((x8 --> x5 :: Γ1, Δ1) = ([] ++ x8 --> x5 :: Γ1, [] ++ Δ1)). auto. rewrite H. apply ImpL. apply ImpLRule_I.
          apply dlCons. simpl ; auto. apply dlCons. simpl ; auto. apply dlNil.
    +  assert (J11: derrec_height x2 < S (dersrec_height d)). rewrite e. apply Arith_prebase.le_lt_n_Sm.
        apply Nat.max_le_iff. left. apply (Nat.le_trans _ _ _ l0 l).
        assert (J12: derrec_height x2 = derrec_height x2). auto.
        pose (IHn _ J11 _ _ J12).
        assert (J2: ((Γ0 ++ x4) ++ Γ3, Δ0 ++ A :: Δ1) = (Γ0 ++ x4 ++ Γ3, Δ0 ++ A :: Δ1)). repeat rewrite <- app_assoc. auto.
        apply s in J2. destruct J2. destruct p. destruct p.
        assert (J13: derrec_height x3 < S (dersrec_height d)). lia.
        assert (J14: derrec_height x3 = derrec_height x3). auto.
        pose (IHn _ J13 _ _ J14).
        assert (J2: ((Γ0 ++ x4) ++ B :: Γ3, Δ0 ++ Δ1) = (Γ0 ++ x4 ++ B :: Γ3, Δ0 ++ Δ1)). repeat rewrite <- app_assoc. auto.
        apply s0 in J2. destruct J2. destruct p0. destruct p0.
        exists ((x5 --> (x6 --> Bot)) --> Bot). repeat split.
        intros. 1,2: simpl in H ; repeat rewrite <- app_nil_end in H ; repeat rewrite propvar_subform_list_app ; simpl ;
        repeat rewrite propvar_subform_list_app ; simpl ;repeat rewrite <- app_assoc ; apply in_app_or in H ; destruct H.
        apply p in H ; repeat rewrite propvar_subform_list_app in H ; simpl in H ; destruct H ; auto.
        apply p0 in H ; repeat rewrite propvar_subform_list_app in H ; simpl in H ; repeat rewrite <- app_assoc in H ; destruct H ; auto.
        apply p in H ; repeat rewrite propvar_subform_list_app in H ; simpl in H ; destruct H ; repeat rewrite <- app_assoc in i0.
        apply in_app_or in i0 ; destruct i0. apply in_or_app ; auto. apply in_app_or in H ; destruct H.
        apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.  apply in_app_or in H ; destruct H.
        apply in_or_app ; right ; apply in_or_app ; auto.
        apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
        apply p0 in H ; repeat rewrite propvar_subform_list_app in H ; simpl in H ; repeat rewrite <- app_assoc in H ; destruct H ; auto.
        apply in_app_or in i0 ; destruct i0. apply in_or_app ; auto. apply in_app_or in H ; destruct H.
        apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto. apply in_app_or in H ; destruct H.
        apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
        apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
        apply derI with (ps:=[([] ++ (x5 --> x6 --> Bot) :: Γ0, [] ++ Bot :: Δ0)]). apply ImpR.
        assert ((Γ0, (x5 --> x6 --> Bot) --> Bot :: Δ0) = ([] ++ Γ0, [] ++ (x5 --> x6 --> Bot) --> Bot :: Δ0)). auto. rewrite H. apply ImpRRule_I.
        apply dlCons. 2: apply dlNil.
        apply derI with (ps:=[([] ++ Γ0, [] ++ x5 :: Bot :: Δ0);([] ++ x6 --> Bot :: Γ0, [] ++ Bot :: Δ0)]). apply ImpL. apply ImpLRule_I.
        apply dlCons. simpl.
        assert (J15: derrec_height d1 = derrec_height d1). auto.
        assert (J16: wkn_R Bot (Γ0, [x5] ++ Δ0) (Γ0, [x5] ++ Bot :: Δ0)). apply wkn_RI. simpl in J16.
        pose (KS_wkn_R _ _ d1 J15 _ _ J16). destruct s1 ; auto. apply dlCons. 2: apply dlNil.
        apply derI with (ps:=[([] ++ Γ0, [] ++ x6 :: Bot :: Δ0);([] ++ Bot :: Γ0, [] ++ Bot :: Δ0)]). apply ImpL. apply ImpLRule_I.
        apply dlCons. simpl.
        assert (J15: derrec_height d3 = derrec_height d3). auto.
        assert (J16: wkn_R Bot (Γ0, [x6] ++ Δ0) (Γ0, [x6] ++ Bot :: Δ0)). apply wkn_RI. simpl in J16.
        pose (KS_wkn_R _ _ d3 J15 _ _ J16). destruct s1 ; auto.
        apply dlCons. 2: apply dlNil. apply derI with (ps:=[]). apply BotL. apply BotLRule_I. apply dlNil.
        apply derI with (ps:=[([] ++ x4 ++ A --> B :: Γ3, [] ++ (x5 --> x6 --> Bot) :: Δ1);([] ++ Bot :: x4 ++ A --> B :: Γ3, [] ++ Δ1)]).
        assert (((x5 --> x6 --> Bot) --> Bot :: x4 ++ A --> B :: Γ3, Δ1) = ([] ++ (x5 --> x6 --> Bot) --> Bot :: x4 ++ A --> B :: Γ3, [] ++ Δ1)). auto.
        rewrite H. apply ImpL. apply ImpLRule_I. apply dlCons.
        apply derI with (ps:=[([] ++ x5 :: x4 ++ A --> B :: Γ3, [] ++ x6 --> Bot :: Δ1)]). apply ImpR. apply ImpRRule_I. apply dlCons.
        apply derI with (ps:=[((x5 :: x4) ++ Γ3, [] ++ A :: x6 --> Bot :: Δ1);((x5 :: x4) ++ B :: Γ3, [] ++ x6 --> Bot :: Δ1)]).
        assert (([] ++ x5 :: x4 ++ A --> B :: Γ3, [] ++ x6 --> Bot :: Δ1) = ((x5 :: x4) ++ A --> B :: Γ3, [] ++ x6 --> Bot :: Δ1)). auto.
        rewrite H. apply ImpL. apply ImpLRule_I. apply dlCons. 3: apply dlNil.
        assert (J15: derrec_height d0 = derrec_height d0). auto. simpl.
        assert (J16: wkn_R (x6 --> Bot) (x5 :: x4 ++ Γ3, [A]++ Δ1) (x5 :: x4 ++ Γ3, [A] ++ x6 --> Bot :: Δ1)). apply wkn_RI. simpl in J16.
        pose (KS_wkn_R _ _ d0 J15 _ _ J16). destruct s1 ; auto. apply dlCons. 2: apply dlNil.
        apply derI with (ps:=[((x5 :: x4) ++ x6 :: B :: Γ3, [] ++ Bot :: Δ1)]). apply ImpR. apply ImpRRule_I. apply dlCons.
          assert (J19: derrec_height d2 = derrec_height d2). auto.
          assert (J20: list_exch_L (x6 :: x4 ++ B :: Γ3, Δ1) (x4 ++ x6 :: B :: Γ3, Δ1)).
          assert (x6 :: x4 ++ B :: Γ3 = [] ++ [x6] ++ [] ++ x4 ++ (B :: Γ3)). auto. rewrite H.
          assert (x4 ++ x6 :: B :: Γ3 = [] ++ x4 ++ [] ++ [x6] ++ (B :: Γ3)). auto. rewrite H0. apply list_exch_LI.
          pose (KS_hpadm_list_exch_L _ d2 _ J20). destruct s1. auto.
        assert (J15: derrec_height x7 = derrec_height x7). auto. simpl.
        assert (J16: wkn_R Bot (x4 ++ x6 :: B :: Γ3, [] ++ Δ1) (x4 ++ x6 :: B :: Γ3, [] ++ Bot :: Δ1)). apply wkn_RI. simpl in J16.
        pose (KS_wkn_R _ _ x7 J15 _ _ J16). destruct s1.
        assert (J17: derrec_height x8 = derrec_height x8). auto. simpl.
        assert (J18: wkn_L x5 ([] ++ x4 ++ x6 :: B :: Γ3, Bot :: Δ1) ([] ++ x5 :: x4 ++ x6 :: B :: Γ3, Bot :: Δ1)). apply wkn_LI. simpl in J18.
        pose (KS_wkn_L _ _ x8 J17 _ _ J18). destruct s1. auto. apply dlNil. apply dlCons. 2: apply dlNil.
        apply derI with (ps:=[]). apply BotL. apply BotLRule_I. apply dlNil.
  (* KR *)
  * inversion X. subst. inversion H5. subst. pose (univ_gen_ext_splitR _ _ X0). destruct s.
    destruct s. destruct p. subst. destruct p.
    assert (J: dersrec_height d = dersrec_height d). auto. apply dersrec_derrec_height in J. destruct J.
    apply app2_find_hole in H1. destruct H1. simpl in IHn. repeat destruct s ; destruct p ; subst.
    + assert (J1: derrec_height x1 < S (dersrec_height d)). lia.
       assert (J2: derrec_height x1 = derrec_height x1). auto.
       assert (J3: (unboxed_list (x ++ x0), [A]) = ((unboxed_list x) ++ (unboxed_list x0), [] ++ [A])).
       rewrite unbox_app_distrib. repeat rewrite <- app_assoc. auto.
       pose (IHn _ J1 _ _ J2 _ _ _ _ J3). destruct s. destruct p. destruct p.
       exists (Box x3). simpl. simpl in p. repeat split.
       intros. 1,2: simpl in H ; repeat rewrite <- app_nil_end in H ; repeat rewrite propvar_subform_list_app ; simpl ;
       repeat rewrite propvar_subform_list_app ; simpl ;repeat rewrite <- app_assoc ;
       apply p in H ; repeat rewrite propvar_subform_list_app in H ; simpl in H ; repeat rewrite <- app_nil_end in H ; destruct H.
       apply propvar_subform_list_unboxed_list in i. apply in_or_app ; left. apply (propvar_subform_list_nobox_gen_ext u) ; auto.
       repeat rewrite <- app_assoc in i0. apply in_app_or in i0. destruct i0.
       apply in_or_app ; left. apply propvar_subform_list_unboxed_list in H. apply (propvar_subform_list_nobox_gen_ext u0) ; auto.
       apply in_or_app ; right ; apply in_or_app ; auto.
       apply derI with (ps:=[(unboxed_list x, [x3])]). apply KR.
       assert ((Γ0, Box x3 :: Δ2) = (Γ0, [] ++ Box x3 :: Δ2)). auto. rewrite H. apply KRRule_I ; auto.
       intro. intros. apply H3. apply in_or_app ; auto. apply dlCons. 2: apply dlNil. auto.
       apply derI with (ps:=[(unboxed_list (Box x3 :: x0), [A])]). apply KR.
       assert ((Box x3 :: Γ1, Box A :: Δ3) = (Box x3 :: Γ1, [] ++ Box A :: Δ3)). auto. rewrite H. apply KRRule_I ; auto.
       intro. intros. inversion H0. exists x3 ; subst ; auto. apply H3. apply in_or_app ; auto.
       apply univ_gen_ext_cons ; auto. apply dlCons. 2: apply dlNil. simpl. auto.
    + destruct x2.
       --  repeat rewrite <- app_nil_end. simpl in e1. subst. assert (J1: derrec_height x1 < S (dersrec_height d)). lia.
           assert (J2: derrec_height x1 = derrec_height x1). auto.
           assert (J3: (unboxed_list (x ++ x0), [A]) = ((unboxed_list x) ++ (unboxed_list x0), [] ++ [A])).
           rewrite unbox_app_distrib. repeat rewrite <- app_assoc. auto.
           pose (IHn _ J1 _ _ J2 _ _ _ _ J3). destruct s. destruct p. destruct p.
           exists (Box x2). simpl. repeat rewrite <- app_nil_end in p. repeat split.
           intros. 1,2: simpl in H ; repeat rewrite <- app_nil_end in H ; repeat rewrite propvar_subform_list_app ; simpl ;
           repeat rewrite propvar_subform_list_app ; simpl ;repeat rewrite <- app_assoc ;
           apply p in H ; repeat rewrite propvar_subform_list_app in H ; simpl in H ; repeat rewrite <- app_nil_end in H ;
           destruct H ; repeat rewrite <- app_assoc in i0.
           apply propvar_subform_list_unboxed_list in i. apply in_or_app ; left. apply (propvar_subform_list_nobox_gen_ext u) ; auto.
           repeat rewrite <- app_assoc in i0. apply in_app_or in i0. destruct i0.
           apply in_or_app ; left. apply propvar_subform_list_unboxed_list in H. apply (propvar_subform_list_nobox_gen_ext u0) ; auto.
           apply in_or_app ; right ; apply in_or_app ; auto.
           apply derI with (ps:=[(unboxed_list x, [x2])]). apply KR.
           assert ((Γ0, Box x2 :: Δ2) = (Γ0, [] ++ Box x2 :: Δ2)). auto. rewrite H. apply KRRule_I ; auto.
           intro. intros. apply H3. apply in_or_app ; auto. apply dlCons. 2: apply dlNil. auto.
           apply derI with (ps:=[(unboxed_list (Box x2 :: x0), [A])]). apply KR.
           assert ((Box x2 :: Γ1, Box A :: Δ3) = (Box x2 :: Γ1, [] ++ Box A :: Δ3)). auto. rewrite H. apply KRRule_I ; auto.
           intro. intros. inversion H0. exists x2 ; subst ; auto. apply H3. apply in_or_app ; auto.
           apply univ_gen_ext_cons ; auto. apply dlCons. 2: apply dlNil. simpl. auto.
       --   simpl in e1. inversion e1 ; subst.
              assert (J19: derrec_height x1 = derrec_height x1). auto.
              assert (J20: list_exch_L (unboxed_list (x ++ x0), [A]) (unboxed_list x0 ++ unboxed_list x, [A])).
              assert (unboxed_list (x ++ x0) = [] ++ (unboxed_list x) ++ [] ++ (unboxed_list x0) ++ []).
              rewrite unbox_app_distrib. simpl. rewrite <- app_nil_end. auto. rewrite H.
              assert (unboxed_list x0 ++ unboxed_list x = [] ++ (unboxed_list x0) ++ [] ++ (unboxed_list x) ++ []).
              simpl. rewrite <- app_nil_end. auto. rewrite H0. apply list_exch_LI.
               pose (KS_hpadm_list_exch_L _ x1 _ J20). destruct s.
               assert (J1: derrec_height x3 < S (dersrec_height d)). rewrite <- e. apply Arith_prebase.le_lt_n_Sm. auto.
               assert (J2: derrec_height x3 = derrec_height x3). auto.
               assert (J3: (unboxed_list x0 ++ unboxed_list x, [A]) = (unboxed_list x0 ++ unboxed_list x, [] ++ [A])).
               repeat rewrite <- app_assoc. auto.
               pose (IHn _ J1 _ _ J2 _ _ _ _ J3). destruct s. destruct p. destruct p.
               exists ((Box x4) --> Bot). simpl. repeat rewrite <- app_nil_end in p. repeat rewrite <- app_nil_end. repeat split.
               intros. 1,2: simpl in H ; repeat rewrite <- app_nil_end in H ; repeat rewrite propvar_subform_list_app ; simpl ;
               repeat rewrite propvar_subform_list_app ; simpl ;repeat rewrite <- app_assoc ;
               apply p in H ; repeat rewrite propvar_subform_list_app in H ; simpl in H ; repeat rewrite <- app_nil_end in H ;
               destruct H ; repeat rewrite <- app_assoc in i0. apply in_app_or in i0. destruct i0.
             apply in_or_app ; left. apply propvar_subform_list_unboxed_list in H. apply (propvar_subform_list_nobox_gen_ext u) ; auto.
             apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
             apply propvar_subform_list_unboxed_list in i. apply in_or_app ; left.
             apply (propvar_subform_list_nobox_gen_ext u0) ; auto.
             apply derI with (ps:=[([] ++ Box x4 :: Γ0, [] ++ Bot :: Δ2 ++ Box A :: x2)]). apply ImpR.
             assert ((Γ0, Box x4 --> Bot :: Δ2 ++ Box A :: x2) = ([] ++ Γ0, [] ++ Box x4 --> Bot :: Δ2 ++ Box A :: x2)). auto. rewrite H. apply ImpRRule_I.
             apply dlCons. 2: apply dlNil. simpl.
             pose (dlCons d0 (dlNil _ _)). apply derI with (concl:=(Box x4 :: Γ0, (Bot :: Δ2) ++ Box A :: x2)) in d2 ; auto.
             apply KR. assert (x4 :: unboxed_list x = unboxed_list (Box x4 :: x)).
             simpl. auto. rewrite H. apply KRRule_I ; auto. intro. intros. inversion H0. exists x4 ; subst ; auto.
             apply H3. apply in_or_app ; auto. apply univ_gen_ext_cons ; auto.
             apply derI with (ps:=[([] ++ Γ1, [] ++ Box x4 :: Δ1);([] ++ Bot :: Γ1, [] ++ Δ1)]). apply ImpL.
             assert ((Box x4 --> Bot :: Γ1, Δ1) = ([] ++ Box x4 --> Bot :: Γ1, [] ++ Δ1)). auto. rewrite H. apply ImpLRule_I.
             apply dlCons. apply derI with (ps:=[(unboxed_list x0, [x4])]). apply KR. apply KRRule_I ; auto.
             intro. intros. apply H3. apply in_or_app ; auto. apply dlCons.
             assert (J4: derrec_height d1 = derrec_height d1). auto. 2: apply dlNil. auto.
             apply dlCons. 2: apply dlNil. apply derI with (ps:=[]). apply BotL. 2: apply dlNil. apply BotLRule_I.
    + assert (J1: derrec_height x1 < S (dersrec_height d)). lia.
       assert (J2: derrec_height x1 = derrec_height x1). auto.
       assert (J3: (unboxed_list (x ++ x0), [A]) = ((unboxed_list x) ++ (unboxed_list x0), [] ++ [A])).
       rewrite unbox_app_distrib. repeat rewrite <- app_assoc. auto.
       pose (IHn _ J1 _ _ J2 _ _ _ _ J3). destruct s. destruct p. destruct p.
       exists (Box x3). simpl. repeat rewrite <- app_nil_end in p. repeat split.
       intros. 1,2: simpl in H ; repeat rewrite <- app_nil_end in H ; repeat rewrite propvar_subform_list_app ; simpl ;
       repeat rewrite propvar_subform_list_app ; simpl ;repeat rewrite <- app_assoc ;
       apply p in H ; repeat rewrite propvar_subform_list_app in H ; simpl in H ; repeat rewrite <- app_nil_end in H ;
       destruct H ; repeat rewrite <- app_assoc in i0.
       apply propvar_subform_list_unboxed_list in i. apply in_or_app ; left.
       apply (propvar_subform_list_nobox_gen_ext u) ; auto.
       apply in_app_or in i0. destruct i0.
       apply in_or_app ; left. apply propvar_subform_list_unboxed_list in H. apply (propvar_subform_list_nobox_gen_ext u0) ; auto.
       apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
       apply derI with (ps:=[(unboxed_list x, [x3])]). apply KR.
       assert ((Γ0, Box x3 :: Δ0) = (Γ0, [] ++ Box x3 :: Δ0)). auto. rewrite H. apply KRRule_I ; auto.
       intro. intros. apply H3. apply in_or_app ; auto. apply dlCons. 2: apply dlNil. auto.
       apply derI with (ps:=[(unboxed_list (Box x3 :: x0), [A])]). apply KR. apply KRRule_I ; auto.
       intro. intros. inversion H. exists x3 ; subst ; auto. apply H3. apply in_or_app ; auto.
       apply univ_gen_ext_cons ; auto. apply dlCons. 2: apply dlNil. simpl. auto.
Qed.







