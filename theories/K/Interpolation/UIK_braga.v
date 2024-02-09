(**************************************************************)
(*   Copyright Ian Shillito [*]                 *)
(*                                                            *)
(*                             [*] Affiliation ANU  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2.1 FREE SOFTWARE LICENSE AGREEMENT        *)
(**************************************************************)

(** Certification of uniform interpolant function (define below)

*)

  Require Import List Extraction.
  Require Import Lia.
  Require Import String.

  Require Import KS_export.

  Require Import UIK_Def_measure.
  Require Import UIK_Canopy.
  Require Export UIK_basics.

  Import ListNotations.

  #[local] Infix "∈" := (@In _) (at level 70, no associativity).

  Section imap.

  Variables (X Y : Type)
            (F : X -> Y -> Prop)                                          (* We will instantiate F with GUI (to have mutal recursion). *)
            (Ffun : forall x l m, F x l -> F x m -> l = m)       (*Require that F is a function. *)
            (D : X -> Prop)                                                 (* Domain of F *)
            (f : forall x, D x -> sig (F x)).                             (* F is defined on the domain. *)

  (* Proceed similarly as Dominique did with flatmap. *)

  Inductive Gimap : list X -> list Y -> Prop :=
    | Gim_nil            : Gimap [] []
    | Gim_cons {x y l m} : F x y
                         -> Gimap l m
                         -> Gimap (x::l) (y::m).

  Hint Constructors Gimap : core.

  Fact Gimap_inv_left l m :
        Gimap l m
      -> match l with
        | []   => [] = m
        | x::l => exists y m', F x y /\ Gimap l m' /\ m = y :: m'
        end.
  Proof. destruct 1; eauto. Qed.

  Fact Gimap_inv_sg_left x m : Gimap [x] [m] -> F x m.
  Proof.
    intros. apply Gimap_inv_left in H. destruct H. destruct H. destruct H.
    destruct H0. inversion H1. subst. auto.
  Qed.

  Fact Gimap_app_inv_left l1 l2 m :
        Gimap (l1++l2) m
      -> exists m1 m2, Gimap l1 m1 /\ Gimap l2 m2 /\ m = m1++m2.
  Proof. 
    induction l1 as [ | x l1 IH1 ] in m |- *; simpl.
    + exists [], m; auto.
    + intros (y & m' & H1 & (m1 & m2 & H2 & H3 & ->)%IH1 & ->)%Gimap_inv_left.
      exists (y::m1), m2. repeat split ; auto.
  Qed.

  Fixpoint imap l : (forall x, x ∈ l -> D x) -> sig (Gimap l).
  Proof.
    refine (match l with
    | []   => fun _  => exist _ [] Gim_nil
    | x::l => fun dl => let (y,hy) := f x _       in
                    let (m,hm) := imap l _ in
                    exist _ (y::m) (Gim_cons hy hm)
    end); auto.
    apply dl ; apply in_eq. intros. apply dl ; apply in_cons ; auto.
  Defined.

  Variables (g : X -> Y) (Hg : forall x, F x (g x)).

  Fact Gimap_map l : Gimap l (map g l).
  Proof. induction l; simpl; now constructor. Qed.

  Fact Gimap_fun l0 : forall l1 l2, Gimap l0 l1 -> Gimap l0 l2 -> l1 = l2.
  Proof. induction l0. intros. apply Gimap_inv_left in H. subst.
             apply Gimap_inv_left in H0. auto. intros.
             apply Gimap_inv_left in H. apply Gimap_inv_left in H0.
             destruct H. destruct H. destruct H. destruct H1. destruct H0.
             destruct H0. destruct H0. destruct H3. subst. pose (Ffun _ _ _ H H0).
             rewrite e. pose (IHl0 _ _ H1 H3). rewrite e0. auto. Qed.

  End imap.

Arguments Gimap {X} {Y} _.
Arguments imap {X} {Y} _ {D} _ {l}.

  Section Gimap_cont.

  Variables (X Y : Type)
            (F : X -> Y -> Prop)                                          (* We will instantiate F with GUI (to have mutal recursion). *)
            (D : X -> Prop)                                                 (* Domain of F *)
            (f : forall x, D x -> sig (F x)).                             (* F is defined on the domain. *)

  Fact Gimap_fun_rest l0 : forall l1 l2, (forall x, InT x l0 -> forall y0 y1, F x y0 -> F x y1 -> y0 = y1) -> Gimap F l0 l1 -> Gimap F l0 l2 -> l1 = l2.
  Proof. induction l0. intros l1 l2 Dom H H0. apply Gimap_inv_left in H. subst.
             apply Gimap_inv_left in H0. auto. intros l1 l2 Dom H H0.
             apply Gimap_inv_left in H. apply Gimap_inv_left in H0.
             destruct H. destruct H. destruct H. destruct H1. destruct H0.
             destruct H0. destruct H0. destruct H3. subst.
             assert (J0: InT a (a :: l0)). apply InT_eq.
             pose (Dom _ J0 _ _ H H0). rewrite e.
             assert (J1: forall x : X, InT x l0 -> forall y0 y1 : Y, F x y0 -> F x y1 -> y0 = y1).
             intros. apply Dom with (x:=x3) ; auto. apply InT_cons ; auto.
             pose (IHl0 _ _ J1 H1 H3). rewrite e0. auto. Qed.

  End Gimap_cont.



  Section UI.

  (* I define the graph of the function UI. *)

  Variables (p : string).     (* The variable we exclude from the interpolant. *)

  Unset Elimination Schemes.

  Inductive GUI : Seq -> MPropF -> Prop :=
    | GUI_empty_seq {s} : (s = ([],[])) ->                                       (* If the sequent is empty, output Bot. *)
                                      GUI s Bot
    | GUI_critic_init {s} : critical_Seq s ->                                             (* If critical and initial, output Top. *)
                                      is_init s ->
                                      GUI s Top
    | GUI_not_critic {s l} : ((critical_Seq s) -> False) ->                        (* If not critical, output conjunction of recursive calls of GUI on Canopy. *)
                                      (Gimap GUI (Canopy s) l) ->
                                      GUI s (list_conj l)
    | GUI_critic_not_init {s l A} : critical_Seq s ->                               (* If critical but not initial, store the propositional variables, recursively call on
                                                                                                               the KR premises of the sequent, and consider the diamond jump. *)
                                           (s <> ([],[])) ->
                                           (is_init s -> False) ->
                                           (Gimap GUI (KR_prems s) l) ->
                                           (GUI (unboxed_list (top_boxes (fst s)), []) A) ->
                                           GUI s (Or (list_disj (restr_list_prop p (snd s)))
                                                     (Or (list_disj (map Neg (restr_list_prop p (fst s))))
                                                     (Or (list_disj (map Box l))
                                                     (Diam A)))).

 Set Elimination Schemes.

  Lemma GUI_fun : forall x l m, GUI x l -> GUI x m -> l = m.
  Proof.
  apply (LtSeq_ind (fun x => forall l m, GUI x l -> GUI x m -> l = m)).
  intros s IH l m H H0. subst. inversion H ; inversion H0 ; subst ; auto ; simpl in *. 1-8: exfalso ; auto.
  6-9: exfalso ; auto. 1,3: apply not_init_empty_set ; auto. apply H4 ; apply critical_empty_set.
  apply H1 ; apply critical_empty_set.
  - assert (J0: (forall x : Seq, InT x (Canopy s) -> forall y0 y1 : MPropF, GUI x y0 -> GUI x y1 -> y0 = y1)).
    intros. apply IH with (s1:=x) ; auto. destruct (Canopy_LtSeq s x H3) ; subst ; auto.
    exfalso. apply H1. apply Canopy_critical with (s:=x) ; subst ; auto.
    pose (Gimap_fun_rest _ _ GUI (Canopy s) l0 l1 J0). rewrite e ; auto.
  - assert (J0: list_disj (map Box l0) = list_disj (map Box l1)).
    assert (J00: (forall x : Seq, InT x (KR_prems s) -> forall y0 y1 : MPropF, GUI x y0 -> GUI x y1 -> y0 = y1)).
    intros. apply IH with (s1:=x) ; auto. apply KR_prems_LtSeq ; auto.
    pose (Gimap_fun_rest _ _ GUI (KR_prems s) l0 l1 J00). rewrite e ; auto.
    assert (J1: A = A0).
    { destruct (eq_dec_listsF (fst s) []) ; subst.
       - rewrite e in * ; simpl in *. inversion H12 ; inversion H5 ; subst ; auto.
         1-14: exfalso ; auto. 1,3: apply not_init_empty_set ; auto.
         1-3: pose critical_empty_set ; auto.
       - apply IH with (s1:=(unboxed_list (top_boxes (fst s)), [])) ; auto.
         unfold LtSeq. unfold measure ; simpl.
         pose (size_LF_nil_unbox_top_box _ n). lia. }
    subst. rewrite J0. auto.
  Qed.

  Lemma GUI_tot : forall s : Seq, {A : MPropF | GUI s A}.
  Proof.
  apply (LtSeq_ind (fun x => existsT A : MPropF, GUI x A)).
  intros s IH. destruct (empty_seq_dec s).
  - subst. exists Bot. apply GUI_empty_seq ; auto.
  - destruct (critical_Seq_dec s).
    -- destruct (dec_KS_init_rules s).
      * assert (is_init s) ; auto. exists Top. apply GUI_critic_init ; auto.
      * assert (is_init s -> False) ; auto.
        assert ((forall x : Seq, In x (KR_prems s) -> {x0 : MPropF | GUI x x0})).
        intros. apply IH with (s1:=x) ; auto. apply KR_prems_LtSeq ; auto. apply InT_In_Seq ; auto.
        epose (@imap _ _ GUI (fun (x : Seq) => In x (KR_prems s)) H0 (KR_prems s)). simpl in s0. destruct s0 ; auto.
        destruct (eq_dec_listsF (fst s) []).
        + exists (Or (list_disj (restr_list_prop p (snd s))) (Or (list_disj (map Neg (restr_list_prop p (fst s))))
           (Or (list_disj (map Box x)) (Diam Bot)))). apply GUI_critic_not_init ; auto. rewrite e ; simpl.
           apply GUI_empty_seq ; auto.
        + assert (J10: existsT A : MPropF, GUI (unboxed_list (top_boxes (fst s)), []%list) A). apply IH.
           unfold LtSeq. unfold measure. simpl. pose (size_LF_nil_unbox_top_box (fst s) n0). lia. destruct J10.
           exists (Or (list_disj (restr_list_prop p (snd s))) (Or (list_disj (map Neg (restr_list_prop p (fst s))))
           (Or (list_disj (map Box x)) (Diam x0)))). apply GUI_critic_not_init ; auto.
    -- assert ((forall x : Seq, In x (Canopy s) -> {x0 : MPropF | GUI x x0})).
      intros. apply IH with (s1:=x) ; auto. destruct (Canopy_LtSeq s x) ; auto.
      apply InT_In_Seq ; auto. subst. exfalso. apply f. apply InT_In_Seq in H ; apply Canopy_critical in H ; auto.
      epose (@imap _ _ GUI (fun (x : Seq) => In x (Canopy s)) H (Canopy s)). simpl in s0. destruct s0 ; auto.
      exists (list_conj x). apply GUI_not_critic ; auto.
  Qed.

  Fact GUI_inv_empty_seq {s A} : GUI s A -> s = ([],[]) -> Bot = A.
  Proof. intros. pose (GUI_empty_seq H0). apply (GUI_fun _ _ _ g H). Qed.

  Fact GUI_inv_critic_init {s A} : GUI s A -> critical_Seq s -> is_init s -> Top = A.
  Proof. intros. pose (GUI_critic_init H0 X). apply (GUI_fun _ _ _ g H). Qed.

  Fact GUI_inv_not_critic {s A l} : GUI s A -> (critical_Seq s -> False) ->
                           (Gimap GUI (Canopy s) l) ->
                           ((list_conj l) = A).
  Proof.
  intros. pose (GUI_not_critic H0 H1). apply (GUI_fun _ _ _ g H).
  Qed.

  Fact GUI_inv_critic_not_init {s A B l0 } : GUI s A -> critical_Seq s ->
                           (s <> ([],[])) ->
                           (is_init s -> False) ->
                           (Gimap GUI (KR_prems s) l0) ->
                           (GUI (unboxed_list (top_boxes (fst s)), []) B) ->
                           ((Or (list_disj (restr_list_prop p (snd s)))
                                                     (Or (list_disj (map Neg (restr_list_prop p (fst s))))
                                                     (Or (list_disj (map Box l0))
                                                     (Diam B)))) = A).
  Proof.
  intros. pose (GUI_critic_not_init H0 H1 H2 H3 H4). apply (GUI_fun _ _ _ g H).
  Qed.

  Let UI_pwc : forall x, sig (GUI x).
  Proof.
  apply GUI_tot.
  Qed.

  Definition UI x := proj1_sig (UI_pwc x).

  Fact UI_spec x : GUI x (UI x).
  Proof. apply (proj2_sig _). Qed.

  Lemma UI_GUI : forall x A, UI x = A <-> GUI x A.
  Proof.
  intros. split ; intro ; subst.
  apply UI_spec. unfold UI. destruct UI_pwc. simpl.
  apply GUI_fun with (x:=x) ; auto.
  Qed.

  End UI.

