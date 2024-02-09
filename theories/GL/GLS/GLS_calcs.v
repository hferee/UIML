Require Import List.
Export ListNotations.
Require Import PeanoNat.

Require Export general_export.

Require Export Syntax_export.

(* In this file we define two calculi based on multisets for the propositonal modal logic
   GL. The first one, called GLS, is the main calculus for GL. The second one, named PSGLS,
   is essentially the calculus GLS with further restrictions on the application of the
   rules. In other words, the calculus PSGLS is a proof-search oriented version of GLS. *)

(* To define our rules, we will need some notions on the language. *)

Fixpoint XBoxed_list (Γ : list MPropF) : list MPropF:=
  match Γ with
  | [ ] => [ ]
  | h :: t => (unBox_formula h :: h :: XBoxed_list t)
  end
.

(* Now that we have defined these, we can prove some properties about them. *)

Lemma XBox_app_distrib :
  forall (l1 l2: list MPropF), XBoxed_list (l1 ++ l2) = (XBoxed_list l1) ++ (XBoxed_list l2).
Proof.
induction l1.
- intro l2. rewrite app_nil_l with (l:=l2). simpl. reflexivity.
- intro l2. simpl. rewrite IHl1. reflexivity.
Qed.

Lemma list_preserv_XBoxed_list : forall (l : list MPropF), incl l (XBoxed_list l).
Proof.
induction l.
- simpl. unfold incl. intros. inversion H.
- simpl. unfold incl. intros. inversion H.
  * subst. apply in_cons. apply in_eq.
  * apply in_cons. apply in_cons. apply IHl. assumption.
Qed.

(* We use a macro for sequents *)

Definition Seq := (prod (list MPropF) (list MPropF)).


(* ---------------------------------------------------------------------------------------------------------------------------------- *)

(* Finally, we can define the rules which constitute our calculi. We gather
   them in cacluli in a definition appearing later. *)

Inductive IdPRule : rlsT Seq :=
  | IdPRule_I : forall P (Γ0 Γ1 Δ0 Δ1 : list MPropF), 
          IdPRule [] (pair (Γ0 ++ # P :: Γ1) (Δ0 ++ # P :: Δ1))
.

Inductive IdBRule : rlsT Seq :=
  | IdBRule_I : forall A Γ0 Γ1 Δ0 Δ1,
          IdBRule [] (pair (Γ0 ++ Box A :: Γ1) (Δ0 ++ Box A :: Δ1))
.

Inductive BotLRule : rlsT Seq :=
  | BotLRule_I : forall Γ0 Γ1 Δ,
          BotLRule [] (pair (Γ0 ++ (Bot) :: Γ1) Δ)
.

Inductive ImpRRule : rlsT Seq :=
  | ImpRRule_I : forall A B Γ0 Γ1 Δ0 Δ1,
          ImpRRule [(pair (Γ0 ++ A :: Γ1) (Δ0 ++ B :: Δ1))]
                    (pair (Γ0 ++ Γ1) (Δ0 ++ (A --> B) :: Δ1))
.

Inductive ImpLRule : rlsT Seq :=
  | ImpLRule_I : forall A B Γ0 Γ1 Δ0 Δ1,
          ImpLRule ((pair (Γ0 ++ Γ1) (Δ0 ++ A :: Δ1)) ::
                     [(pair (Γ0 ++ B :: Γ1) (Δ0 ++ Δ1))])
                    (pair (Γ0 ++ (A --> B) :: Γ1) (Δ0 ++ Δ1))
.

Inductive GLRRule : rlsT Seq :=
  | GLRRule_I : forall A BΓ Γ0 Δ0 Δ1,
          (is_Boxed_list BΓ) -> (* have MS of boxed formulae prem L*)
          (nobox_gen_ext BΓ Γ0) -> (* extend BΓ in Γ0, the L of the ccl *)
         GLRRule [(pair ((XBoxed_list BΓ) ++ [Box A]) [A])] (pair Γ0 (Δ0 ++ Box A :: Δ1))
.

(* At last we can define our calculus GLS and its proof-search version PSGLS. *)

Inductive GLS_rules : rlsT Seq :=
  | IdP : forall ps c, IdPRule ps c -> GLS_rules ps c
  | BotL : forall ps c, BotLRule ps c -> GLS_rules ps c
  | ImpR : forall ps c, ImpRRule ps c -> GLS_rules ps c
  | ImpL : forall ps c, ImpLRule ps c -> GLS_rules ps c
  | GLR : forall ps c, GLRRule ps c -> GLS_rules ps c
.

(* We can show that all identities are provable in GLS. *)

Lemma Id_all_form : forall (A : MPropF) l0 l1 l2 l3,
          derrec GLS_rules (fun _ => False) (l0 ++ A :: l1, l2 ++ A :: l3).
Proof.
assert (DersNilF: dersrec GLS_rules  (fun _ : rel (list MPropF) => False) []).
apply dersrec_nil.

induction A.
- intros. assert (IdPRule [] (l0 ++ # s :: l1, l2 ++ # s :: l3)). apply IdPRule_I. apply IdP in H.
  pose (derI (rules:=GLS_rules) (prems:=fun _ : rel (list MPropF) => False) (ps:=[])
  (l0 ++ # s :: l1, l2 ++ # s :: l3) H DersNilF). assumption.
- intros. assert (BotLRule [] (l0 ++ ⊥ :: l1, l2 ++ ⊥ :: l3)). apply BotLRule_I. apply BotL in H.
  pose (derI (rules:=GLS_rules) (prems:=fun _ : rel (list MPropF) => False) (ps:=[])
  (l0 ++ ⊥ :: l1, l2 ++ ⊥ :: l3) H DersNilF). assumption.
- intros. assert (ImpRRule [(l0 ++ A1 :: A1 --> A2 :: l1, l2 ++ A2 :: l3)] (l0 ++ A1 --> A2 :: l1, l2 ++ A1 --> A2 :: l3)).
  apply ImpRRule_I. apply ImpR in H.
  assert (ImpLRule [((l0 ++ [A1]) ++ l1, l2 ++ A1 :: A2 :: l3); ((l0 ++ [A1]) ++ A2 :: l1, l2 ++ A2 :: l3)] ((l0 ++ [A1]) ++ A1 --> A2 :: l1, l2 ++ A2 :: l3)).
  apply ImpLRule_I. repeat rewrite <- app_assoc in H0. simpl in H0. apply ImpL in H0.
  pose (IHA1 l0 l1 l2 (A2 :: l3)). pose (IHA2 (l0 ++ [A1]) l1 l2 l3). repeat rewrite <- app_assoc in d0. simpl in d0.
  pose (dlCons d0 DersNilF). pose (dlCons d d1).
  pose (derI (rules:=GLS_rules) (prems:=fun _ : rel (list MPropF) => False) (ps:=[(l0 ++ A1 :: l1, l2 ++ A1 :: A2 :: l3); (l0 ++ A1 :: A2 :: l1, l2 ++ A2 :: l3)])
  (l0 ++ A1 :: A1 --> A2 :: l1, l2 ++ A2 :: l3) H0 d2). pose (dlCons d3 DersNilF).
  pose (derI (rules:=GLS_rules) (prems:=fun _ : rel (list MPropF) => False) (ps:=[(l0 ++ A1 :: A1 --> A2 :: l1, l2 ++ A2 :: l3)])
  (l0 ++ A1 --> A2 :: l1, l2 ++ A1 --> A2 :: l3) H d4). assumption.
- intros. assert (GLRRule [(XBoxed_list (top_boxes (l0 ++ Box A :: l1)) ++ [Box A], [A])] (l0 ++ Box A :: l1, l2 ++ Box A :: l3)).
  apply GLRRule_I. apply is_Boxed_list_top_boxes. rewrite top_boxes_distr_app. simpl. apply univ_gen_ext_combine.
  apply nobox_gen_ext_top_boxes. apply univ_gen_ext_cons. apply nobox_gen_ext_top_boxes.
  rewrite top_boxes_distr_app in X. simpl in X. rewrite XBox_app_distrib in X. simpl in X.
  repeat rewrite <- app_assoc in X. simpl in X.
  pose (IHA (XBoxed_list (top_boxes l0)) (Box A :: XBoxed_list (top_boxes l1) ++ [Box A]) [] []).
  simpl in d. pose (dlCons d DersNilF). apply GLR in X.
  pose (derI (rules:=GLS_rules) (prems:=fun _ : rel (list MPropF) => False) (ps:=[(XBoxed_list (top_boxes l0) ++ A :: Box A :: XBoxed_list (top_boxes l1) ++ [Box A], [A])])
  (l0 ++ Box A :: l1, l2 ++ Box A :: l3) X d0). assumption.
Qed.


Definition GLS_prv s := derrec GLS_rules (fun _ => False) s.
Definition GLS_drv s := derrec GLS_rules (fun _ => True) s.



