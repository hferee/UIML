Require Import List.
Export ListNotations.
Require Import PeanoNat.

Require Export general_export.
Require Export Syntax_export.

(* We use a macro for sequents *)

Definition Seq := (prod (list MPropF) (list MPropF)).


(* ---------------------------------------------------------------------------------------------------------------------------------- *)

(* Finally, we can define the rules which constitute our calculus. We gather
   it in caclulus in a definition appearing later. *)

Inductive IdPRule : rlsT Seq :=
  | IdPRule_I : forall P (Γ0 Γ1 Δ0 Δ1 : list MPropF),
          IdPRule [] (Γ0 ++ # P :: Γ1 , Δ0 ++ # P :: Δ1)
.


Inductive BotLRule : rlsT Seq :=
  | BotLRule_I : forall Γ0 Γ1 Δ,
          BotLRule [] (Γ0 ++ Bot :: Γ1 , Δ)
.

Inductive ImpRRule : rlsT Seq :=
  | ImpRRule_I : forall A B Γ0 Γ1 Δ0 Δ1,
          ImpRRule [(Γ0 ++ A :: Γ1 , Δ0 ++ B :: Δ1)]
                    (Γ0 ++ Γ1 , Δ0 ++ (A --> B) :: Δ1).

Inductive ImpLRule : rlsT Seq :=
  | ImpLRule_I : forall A B Γ0 Γ1 Δ0 Δ1,
          ImpLRule [(Γ0 ++ Γ1 , Δ0 ++ A :: Δ1) ;
                     (Γ0 ++ B :: Γ1 , Δ0 ++ Δ1)]
                    (Γ0 ++ (A --> B) :: Γ1 , Δ0 ++ Δ1)
.

Inductive KRRule : rlsT Seq :=
  | KRRule_I : forall A BΓ Γ0 Δ0 Δ1,
          (is_Boxed_list BΓ) ->
          (nobox_gen_ext BΓ Γ0) ->
         KRRule [(unboxed_list BΓ, [A])] (Γ0 , Δ0 ++ Box A :: Δ1).

(* At last we can define our calculus KS. *)

Inductive KS_rules : rlsT Seq :=
  | IdP : forall ps c, IdPRule ps c -> KS_rules ps c
  | BotL : forall ps c, BotLRule ps c -> KS_rules ps c
  | ImpR : forall ps c, ImpRRule ps c -> KS_rules ps c
  | ImpL : forall ps c, ImpLRule ps c -> KS_rules ps c
  | KR : forall ps c, KRRule ps c -> KS_rules ps c
.

(* We can show that all identities are provable in KS. *)

Lemma Id_all_form : forall (A : MPropF) l0 l1 l2 l3,
          derrec KS_rules (fun _ => False) (l0 ++ A :: l1, l2 ++ A :: l3).
Proof.
assert (DersNilF: dersrec KS_rules  (fun _ : rel (list (MPropF)) => False) []).
apply dersrec_nil.

induction A as [n| | |].
- intros. assert (IdPRule [] (l0 ++ # n :: l1, l2 ++ # n :: l3)). apply IdPRule_I. apply IdP in H.
  pose (derI (rules:=KS_rules) (prems:=fun _ : rel (list (MPropF)) => False) (ps:=[])
  (l0 ++ # n :: l1, l2 ++ # n :: l3) H DersNilF). assumption.
- intros. assert (BotLRule [] (l0 ++ Bot :: l1, l2 ++ Bot :: l3)). apply BotLRule_I. apply BotL in H.
  pose (derI (rules:=KS_rules) (prems:=fun _ : rel (list (MPropF)) => False) (ps:=[])
  (l0 ++ Bot :: l1, l2 ++ Bot :: l3) H DersNilF). assumption.
- intros. assert (ImpRRule [(l0 ++ A1 :: A1 --> A2 :: l1, l2 ++ A2 :: l3)] (l0 ++ A1 --> A2 :: l1, l2 ++ A1 --> A2 :: l3)).
  apply ImpRRule_I. apply ImpR in H.
  assert (ImpLRule [((l0 ++ [A1]) ++ l1, l2 ++ A1 :: A2 :: l3); ((l0 ++ [A1]) ++ A2 :: l1, l2 ++ A2 :: l3)] ((l0 ++ [A1]) ++ A1 --> A2 :: l1, l2 ++ A2 :: l3)).
  apply ImpLRule_I. repeat rewrite <- app_assoc in H0. simpl in H0. apply ImpL in H0.
  pose (IHA1 l0 l1 l2 (A2 :: l3)). pose (IHA2 (l0 ++ [A1]) l1 l2 l3). repeat rewrite <- app_assoc in d0. simpl in d0.
  pose (dlCons d0 DersNilF). pose (dlCons d d1).
  pose (derI (rules:=KS_rules) (prems:=fun _ : rel (list (MPropF)) => False) (ps:=[(l0 ++ A1 :: l1, l2 ++ A1 :: A2 :: l3); (l0 ++ A1 :: A2 :: l1, l2 ++ A2 :: l3)])
  (l0 ++ A1 :: A1 --> A2 :: l1, l2 ++ A2 :: l3) H0 d2). pose (dlCons d3 DersNilF).
  pose (derI (rules:=KS_rules) (prems:=fun _ : rel (list (MPropF)) => False) (ps:=[(l0 ++ A1 :: A1 --> A2 :: l1, l2 ++ A2 :: l3)])
  (l0 ++ A1 --> A2 :: l1, l2 ++ A1 --> A2 :: l3) H d4). assumption.
- intros. assert (KRRule [(unboxed_list (top_boxes (l0 ++ Box A :: l1)), [A])] (l0 ++ Box A :: l1, l2 ++ Box A :: l3)).
  apply KRRule_I. apply is_Boxed_list_top_boxes. rewrite top_boxes_distr_app. simpl. apply univ_gen_ext_combine.
  apply nobox_gen_ext_top_boxes. apply univ_gen_ext_cons. apply nobox_gen_ext_top_boxes.
  rewrite top_boxes_distr_app in X. simpl in X. rewrite unbox_app_distrib in X. simpl in X.
  repeat rewrite <- app_assoc in X. simpl in X.
  pose (IHA (unboxed_list (top_boxes l0)) (unboxed_list (top_boxes l1)) [] []).
  simpl in d. pose (dlCons d DersNilF). apply KR in X.
  pose (derI (rules:=KS_rules) (prems:=fun _ : rel (list (MPropF)) => False) (ps:=[(unboxed_list (top_boxes l0) ++ A :: unboxed_list (top_boxes l1), [A])])
  (l0 ++ Box A :: l1, l2 ++ Box A :: l3) X d0). assumption.
Qed.

Definition KS_prv s := derrec KS_rules (fun _ => False) s.
Definition KS_drv s := derrec KS_rules (fun _ => True) s.

