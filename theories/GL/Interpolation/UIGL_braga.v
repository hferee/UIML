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

  Require Import GLS_export.

  Require Import UIGL_Def_measure.
  Require Import UIGL_Canopy.
  Require Import UIGL_LexSeq.
  Require Export UIGL_basics.
  Require Import UIGL_nodupseq.

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


  Section GN.

  Variables (p : nat)                                                         (* The variable we exclude from the interpolant. *)
            (F : Seq -> MPropF -> Prop)                            (* We will instantiate F with GUI (to have mutal recursion). *)
            (Ffun : forall x l m, F x l -> F x m -> l = m).       (* Require that F is a function. *)

  (* First I define the graph of the function N, which is involved in UI. N is total. *)

  Unset Elimination Schemes.

  (** I proceed as Dominique: Because of nesting, induction principles are too weak,
      see below for better ones *)

  Inductive GN : Seq -> Seq -> MPropF -> Prop :=
    (* If s is initial, send Top. *)
    | GN_init_seq {s0 s} : is_init s -> GN s0 s Top
    (* If s is not initial, and has less usable boxes than s0, then call UI. *)
    | GN_less_ub {s0 s φ} : (is_init s -> False) ->
                              (length (usable_boxes s) < length (usable_boxes s0)) ->
                              F s φ ->
                              GN s0 s φ
    (* If s is not initial, and does not have less usable boxes than s0, then do an unfolding without recursive call. *)
    | GN_less {s0 s l} : (is_init s -> False) ->
                              ((length (usable_boxes s) < length (usable_boxes s0)) -> False) ->
                              (Gimap F (GLR_prems (nodupseq s)) l) ->
                              GN s0 s (Or (list_disj (restr_list_prop p (snd s)))                   (* Disjunction of propositional variables (different from p) on the right. *)
                                            (Or (list_disj (map Neg (restr_list_prop p (fst s))))   (* Disjunction of propositional variables (different from p) on the left, negated. *)
                                            (list_disj (map Box l)))).

  Set Elimination Schemes.

  Fact GN_inv_init0 {s0 s A} : GN s0 s A -> is_init s -> Top = A.
  Proof. destruct 1 as [ Inits | ? ? ? Inits |  ] ; intros; trivial ; exfalso ; auto. Qed.

  Fact GN_inv_noinit_lessub0 {s0 s A φ} : GN s0 s A -> (is_init s -> False) ->
                           (length (usable_boxes s) < length (usable_boxes s0)) ->
                           F s φ ->
                           φ = A.
  Proof. destruct 1 as [ Inits | ? ? ? Inits |  ] ; intros; trivial ; auto. 1, 3: exfalso ; auto.
             apply (Ffun s) ; auto. Defined.

  Fact GN_inv_noinit_nolessub0 {s0 s A l} : GN s0 s A -> (is_init s -> False) ->
                           ((length (usable_boxes s) < length (usable_boxes s0)) -> False) ->
                           (Gimap F (GLR_prems (nodupseq s)) l) ->
          (Or (list_disj (restr_list_prop p (snd s)))  (Or (list_disj (map Neg (restr_list_prop p (fst s)))) (list_disj (map Box l)))) = A.
  Proof. destruct 1 as [ Inits | ? ? ? Inits |  ] ; intros; trivial ; auto. 1, 2: exfalso ; auto.
              pose (Gimap_fun _ _ F Ffun _ _ _ H1 H4). rewrite e. auto. Defined.

  Hint Constructors Gimap GN : core.
  Hint Resolve GN_inv_init0 GN_inv_noinit_lessub0 GN_inv_noinit_nolessub0 : core.


  Lemma GN_fun : forall s0 s A, GN s0 s A -> (fun s0 s A => forall B, GN s0 s B -> A = B) s0 s A.
  Proof.
  intros. inversion H ; subst ; intros; auto.
  - pose (GN_inv_init0 H0 X) ; auto.
  - pose (GN_inv_noinit_lessub0 H3 H0 H1 H2) ; auto.
  - pose (GN_inv_noinit_nolessub0 H3 H0 H1 H2) ; auto.
  Qed.

  Lemma GN_fun0 : forall s0 s A B, GN s0 s A -> GN s0 s B -> A = B.
  Proof.
  intros. apply GN_fun with (s0:=s0) (s:=s) ; auto.
  Qed.

  End GN.





  Section UI.

  (* Second I define the graph of the function UI. *)

  Variables (p : nat).     (* The variable we exclude from the interpolant. *)

  Unset Elimination Schemes.

  (** Because of nesting, induction principles are too weak, 
      see below for better ones *)

  Inductive GUI : Seq -> MPropF -> Prop :=
    | GUI_empty_seq {s} : s = ([],[]) ->                                             (* If s is the empty set, output Bot. *)
                                      GUI s Bot
    | GUI_critic_init {s} : critical_Seq s ->                                             (* If critical and initial, output Top. *)
                                      is_init s ->
                                      GUI s Top
    | GUI_not_critic {s l} : ((critical_Seq s) -> False) ->                        (* If not critical, output conjunction of recursive calls of GUI on Canopy. *)
                                      (Gimap GUI (Canopy (nodupseq s)) l) ->
                                      GUI s (list_conj l)
    | GUI_critic_not_init {s l0 l1} : critical_Seq s ->                               (* If critical but not initial, store the propositional variables, recursively call on
                                                                                                               the GLR premises of the sequent, and use GN. *)
                                           (s <> ([],[])) ->
                                           (is_init s -> False) ->
                                           (Gimap GUI (GLR_prems (nodupseq s)) l0) ->
                                           (Gimap (GN p GUI s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []))) l1) ->
                                           GUI s (Or (list_disj (restr_list_prop p (snd s)))
                                                     (Or (list_disj (map Neg (restr_list_prop p (fst s))))
                                                     (Or (list_disj (map Box l0))
                                                     (Diam (list_conj l1))))).

 Set Elimination Schemes.

  Lemma GUI_fun : forall x l m, GUI x l -> GUI x m -> l = m.
  Proof.
  apply (LexSeq_ind (fun x => forall l m, GUI x l -> GUI x m -> l = m)).
  intros s IH l m H H0. inversion H ; inversion H0 ; subst ; auto ; simpl in *. 1-8: exfalso ; auto.
  6-9: exfalso ; auto. 1,3: apply not_init_empty_seq ; auto. apply H4 ; apply critical_empty_seq.
  apply H1 ; apply critical_empty_seq.
  - assert (J0: (forall x : Seq, InT x (Canopy (nodupseq s)) -> forall y0 y1 : MPropF, GUI x y0 -> GUI x y1 -> y0 = y1)).
    intros. apply IH with (s1:=x) ; auto. apply LexSeq_nodupseq. destruct (Canopy_LexSeq (nodupseq s) x H3) ; auto.
    exfalso. apply H1. apply critical_nodupseq. apply Canopy_critical with (s:=nodupseq s) ; subst ; auto.
    pose (Gimap_fun_rest _ _ GUI (Canopy (nodupseq s)) l0 l1 J0). rewrite e ; auto.
  - assert (J0: list_disj (map Box l0) = list_disj (map Box l2)).
    assert (J00: (forall x : Seq, InT x (GLR_prems (nodupseq s)) -> forall y0 y1 : MPropF, GUI x y0 -> GUI x y1 -> y0 = y1)).
    intros. apply IH with (s1:=x) ; auto. apply LexSeq_nodupseq. apply GLR_prems_LexSeq ; auto.
    intro. pose (is_init_nodupseq s). apply H3. apply p0. unfold is_init ; auto.
    pose (Gimap_fun_rest _ _ GUI (GLR_prems (nodupseq s)) l0 l2 J00). rewrite e ; auto.
    assert (J1: l1 = l3).
    assert (J10: (forall x : Seq, InT x (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))) -> forall y0 y1 : MPropF, (GN p GUI s) x y0 -> (GN p GUI s) x y1 -> y0 = y1)).
    intros. inversion H7 ; inversion H13 ; subst ; auto. 1-3: exfalso ; auto.
    2-4: exfalso ; auto.
    apply IH with (s1:=x) ; auto. unfold LexSeq. unfold less_thanS. apply DLW_wf_lex.lex_cons ; auto.
    assert (J100: (forall x0 : Seq, InT x0 (GLR_prems (nodupseq x)) -> forall y0 y1 : MPropF, GUI x0 y0 -> GUI x0 y1 -> y0 = y1)).
    intros. apply IH with (s1:=x0) ; auto. unfold LexSeq. apply DLW_wf_lex.lex_cons ; auto. apply GLR_prems_less_ub in H17.
    rewrite <- ub_nodupseq in H17. pose (leq_ub_Canopy _ _ H6). rewrite <- ub_nodupseq in l5.
    pose (leq_ub_unif s) ; lia. intros. pose (is_init_nodupseq x). apply H14. apply p0. unfold is_init ; left ; auto.
    pose (Gimap_fun_rest _ _ GUI (GLR_prems (nodupseq x)) l l4 J100). rewrite e ; auto.
    pose (Gimap_fun_rest _ _ _ _ l1 l3 J10). rewrite e ; auto.
    rewrite J0. rewrite J1. auto.
  Qed.

  Lemma GUI_tot : forall s : Seq, {A : MPropF | GUI s A}.
  Proof.
  apply (LexSeq_ind (fun x => existsT A : MPropF, GUI x A)).
  intros s IH. destruct (empty_seq_dec s).
  - subst. exists Bot. apply GUI_empty_seq ; auto.
  - destruct (critical_Seq_dec s).
    -- destruct (dec_init_rules s).
      * assert (is_init s) ; auto. exists Top. apply GUI_critic_init ; auto.
      * assert (is_init s -> False) ; auto.
        assert ((forall x : Seq, In x (GLR_prems (nodupseq s)) -> {x0 : MPropF | GUI x x0})).
        intros. apply IH with (s1:=x) ; auto. apply LexSeq_nodupseq. apply GLR_prems_LexSeq ; auto.
        intro. pose (is_init_nodupseq s). apply f. apply p0. unfold is_init ; auto. apply InT_In_Seq ; auto.
        epose (@imap _ _ GUI (fun (x : Seq) => In x (GLR_prems (nodupseq s))) H0 (GLR_prems (nodupseq s))). simpl in s0. destruct s0 ; auto.
        assert (J10: (forall z : Seq, In z (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))) -> existsT A : MPropF, (GN p GUI s) z A)).
         { intros. destruct (dec_init_rules z).
         -- exists Top. apply GN_init_seq ; auto.
         -- destruct (lt_decT (length (usable_boxes z)) (length (usable_boxes s))).
             ** destruct (IH z). unfold LexSeq. apply DLW_wf_lex.lex_cons ; auto. exists x0. apply GN_less_ub ; auto.
             ** assert (J100: (forall x0 : Seq, In x0 (GLR_prems (nodupseq z)) -> existsT A : MPropF, GUI x0 A)).
                 intros. apply IH with (s1:=x0) ; auto. unfold LexSeq. apply DLW_wf_lex.lex_cons ; auto. apply InT_In_Seq in H2. apply GLR_prems_less_ub in H2.
                 rewrite <- ub_nodupseq in H2. apply InT_In_Seq in H1. pose (leq_ub_Canopy _ _ H1). rewrite <- ub_nodupseq in l.
                 pose (leq_ub_unif s) ; lia. intros. pose (is_init_nodupseq z). apply f0. apply p0. unfold is_init ; left ; auto.
                 epose (@imap _ _ GUI (fun (x : Seq) => In x (GLR_prems (nodupseq z))) J100 (GLR_prems (nodupseq z))). simpl in s0. destruct s0 ; auto.
                 exists (Or (list_disj (restr_list_prop p (snd z))) (Or (list_disj (map Neg (restr_list_prop p (fst z)))) (list_disj (map Box x0)))).
                 apply GN_less ; auto. }
         epose (@imap Seq MPropF (GN p GUI s) (fun (x : Seq) => In x (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)))) J10
         (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)))). simpl in s0. destruct s0 ; auto.
         exists (Or (list_disj (restr_list_prop p (snd s))) (Or (list_disj (map Neg (restr_list_prop p (fst s))))
         (Or (list_disj (map Box x)) (Diam (list_conj x0))))). apply GUI_critic_not_init ; auto.
    -- assert ((forall x : Seq, In x (Canopy (nodupseq s)) -> {x0 : MPropF | GUI x x0})).
        intros. apply IH with (s1:=x) ; auto. destruct (Canopy_LexSeq (nodupseq s) x) ; auto.
        apply InT_In_Seq ; auto. subst. exfalso. apply f. apply critical_nodupseq. apply InT_In_Seq in H ; apply Canopy_critical in H ; auto.
        apply LexSeq_nodupseq ; auto.
        epose (@imap _ _ GUI (fun (x : Seq) => In x (Canopy (nodupseq s))) H (Canopy (nodupseq s))). simpl in s0. destruct s0 ; auto.
        exists (list_conj x). apply GUI_not_critic ; auto.
Qed.

  Fact GUI_inv_empty_seq {s A} : GUI s A -> s = ([],[]) -> Bot = A.
  Proof. intros. pose (GUI_empty_seq H0). apply (GUI_fun _ _ _ g H). Qed.


  Fact GUI_inv_critic_init {s A} : GUI s A -> critical_Seq s -> is_init s -> Top = A.
  Proof. intros. pose (GUI_critic_init H0 X). apply (GUI_fun _ _ _ g H). Qed.

  Fact GUI_inv_not_critic {s A l} : GUI s A -> (critical_Seq s -> False) ->
                           (Gimap GUI (Canopy (nodupseq s)) l) ->
                           ((list_conj l) = A).
  Proof.
  intros. pose (GUI_not_critic H0 H1). apply (GUI_fun _ _ _ g H).
  Qed.

  Fact GUI_inv_critic_not_init {s A l0 l1} : GUI s A -> critical_Seq s ->
                           (s <> ([],[])) ->
                           (is_init s -> False) ->
                           (Gimap GUI (GLR_prems (nodupseq s)) l0) ->
                           (Gimap (GN p GUI s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []))) l1) ->
                           ((Or (list_disj (restr_list_prop p (snd s)))
                                                     (Or (list_disj (map Neg (restr_list_prop p (fst s))))
                                                     (Or (list_disj (map Box l0))
                                                     (Diam (list_conj l1))))) = A).
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

  Section N.

  Definition N_pwc : forall p s0 s, sig (GN p (GUI p) s0 s).
  Proof.
  intros. destruct (dec_init_rules s).
  - assert (is_init s) ; auto. exists Top. apply GN_init_seq ; auto.
  - assert (is_init s -> False) ; auto.
    destruct (lt_decT (length (usable_boxes s)) (length (usable_boxes s0))).
    + exists (UI p s). apply GN_less_ub ; auto ; apply UI_GUI ; auto.
    + assert (J100: (forall x0 : Seq, In x0 (GLR_prems (nodupseq s)) -> existsT A : MPropF, GUI p x0 A)).
       intros. apply GUI_tot.
       epose (@imap _ _ (GUI p) (fun (x : Seq) => In x (GLR_prems (nodupseq s))) J100 (GLR_prems (nodupseq s))). simpl in s1. destruct s1 ; auto.
       exists (Or (list_disj (restr_list_prop p (snd s))) (Or (list_disj (map Neg (restr_list_prop p (fst s)))) (list_disj (map Box x)))).
       apply GN_less ; auto.
  Qed.

  Variables (p : nat).      (* Propositional variable we consider. *)

  Definition N s0 s := proj1_sig (N_pwc p s0 s).

  Fact N_spec s0 s : GN p (GUI p) s0 s (N s0 s).
  Proof. apply (proj2_sig _). Qed.

  Fact GN_inv_init {s0 s A} : GN p (GUI p) s0 s A -> is_init s -> Top = A.
  Proof. destruct 1 as [ Inits | ? ? ? Inits |  ] ; intros; trivial ; exfalso ; auto. Qed.

  Fact GN_inv_noinit_lessub {s0 s A φ} : GN p (GUI p) s0 s A -> (is_init s -> False) ->
                           (length (usable_boxes s) < length (usable_boxes s0)) ->
                           GUI p s φ ->
                           φ = A.
  Proof. destruct 1 as [ Inits | ? ? ? Inits |  ] ; intros; trivial ; auto. 1, 3: exfalso ; auto.
             apply (GUI_fun p s) ; auto. Defined.

  Fact GN_inv_noinit_nolessub {s0 s A l} : GN p (GUI p) s0 s A -> (is_init s -> False) ->
                           ((length (usable_boxes s) < length (usable_boxes s0)) -> False) ->
                           (Gimap (GUI p) (GLR_prems (nodupseq s)) l) ->
          (Or (list_disj (restr_list_prop p (snd s)))  (Or (list_disj (map Neg (restr_list_prop p (fst s)))) (list_disj (map Box l)))) = A.
  Proof. destruct 1 as [ Inits | ? ? ? Inits |  ] ; intros; trivial ; auto. 1, 2: exfalso ; auto.
              pose (Gimap_fun _ _ (GUI p) (GUI_fun p) _ _ _ H1 H4). rewrite e. auto. Defined.

  Hint Resolve N_spec : core.

  End N.

