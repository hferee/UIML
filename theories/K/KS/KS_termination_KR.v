Require Import List.
Export ListNotations.
Require Import Lia.
Require Import PeanoNat.

Require Import KS_calc.
Require Import KS_dec.
Require Import KS_termination_measure.
Require Import KS_termination_prelims.



(* Now let us tackle the KR rule. *)

Fixpoint prems_Box_R (l : list MPropF) (s : Seq) : list (list Seq) :=
match l with
  | nil => nil
  | h :: t => match h with
              | Box A => [((unboxed_list (top_boxes (fst s))), [A])] :: (prems_Box_R t s)
              | _ => prems_Box_R t s
              end
end.

 Lemma KR_help01 : forall prems s (l : list MPropF), InT prems (prems_Box_R l s) ->
                  (existsT2 (A : MPropF),
                        (In (Box A) l) /\
                        (prems = [(unboxed_list (top_boxes (fst s)) , [A])])).
Proof.
intros prems s. destruct s. induction l1 ; intros X.
- simpl in X. inversion X.
- simpl in X. destruct a.
  * apply IHl1 in X. destruct X as [x p]. repeat destruct p. subst.
     exists x. repeat split ; try auto ; try apply in_cons ; try assumption.
  * apply IHl1 in X. destruct X as [x p]. repeat destruct p. subst.
    exists x. repeat split ; try auto ; try apply in_cons ; try assumption.
  * apply IHl1 in X. destruct X as [x p]. repeat destruct p. subst.
    exists x. repeat split ; try auto ; try apply in_cons ; try assumption.
  * inversion X.
    + subst. exists a. repeat split ; try auto ; try apply in_eq.
    + apply IHl1 in H0. destruct H0  as [x p]. repeat destruct p. subst.
      exists x. repeat split ; try auto ; try apply in_cons ; try assumption.
Qed.

Lemma KR_help1 : forall prems s, InT prems (prems_Box_R (top_boxes (snd s)) s) ->
                                         KRRule prems s.
Proof.
intros prems  s X. destruct (@KR_help01 _ _ _ X) as (x&Hi&Heq).
repeat destruct s0. destruct s. simpl in X.
repeat destruct p. subst. simpl in *. assert (In (Box x) l0). apply top_boxes_incl_list.
assumption. apply in_splitT in H. destruct H. repeat destruct s.
rewrite e. apply KRRule_I. intro. intros. apply in_top_boxes in H.
destruct H. repeat destruct s. repeat destruct p. exists x2. assumption.
simpl. apply top_boxes_nobox_gen_ext.
Qed.



Lemma KR_help02 : forall Γ Δ0 Δ1 BΓ A l, KRRule [(unboxed_list BΓ, [A])] (Γ, Δ0 ++ Box A :: Δ1) ->
                                             (is_Boxed_list BΓ) ->
                                             (nobox_gen_ext BΓ Γ) ->
                                             (In (Box A) l) ->
                                             InT [(unboxed_list BΓ, [A])] (prems_Box_R l (Γ, Δ0 ++ Box A :: Δ1)).
Proof.
induction l ; intros.
- inversion H0.
- simpl. destruct a.
  * assert (InT (Box A) (# n :: l)). apply in_splitT in H0. destruct H0. destruct s. rewrite e.
    apply InT_or_app. right. apply InT_eq. inversion H1. inversion H3. apply InT_In in H3.
    pose (IHl X H X0 H3). assumption.
  * assert (InT (Box A) (Bot :: l)). apply in_splitT in H0. destruct H0. destruct s. rewrite e.
    apply InT_or_app. right. apply InT_eq. inversion H1. inversion H3. apply InT_In in H3.
    pose (IHl X H X0 H3). assumption.
  * assert (InT (Box A) (a1 --> a2 :: l)). apply in_splitT in H0. destruct H0. destruct s. rewrite e.
    apply InT_or_app. right. apply InT_eq. inversion H1. inversion H3. apply InT_In in H3.
    pose (IHl X H X0 H3). assumption.
  * assert (InT (Box A) (Box a :: l)). apply in_splitT in H0. destruct H0. destruct s. rewrite e.
    apply InT_or_app. right. apply InT_eq. inversion H1.
    + subst. inversion H3. subst. pose (nobox_gen_ext_top_boxes_identity X0 H). rewrite e.
      apply InT_eq.
    + subst. apply InT_In in H3. pose (IHl X H X0 H3). apply InT_cons. assumption.
Qed.

Lemma KR_help2 : forall prem s, KRRule [prem] s ->
                      InT [prem] (prems_Box_R (top_boxes (snd s)) s).
Proof.
intros. inversion X. subst. simpl.
pose (@KR_help02 Γ0 Δ0 Δ1 BΓ A (top_boxes (Δ0 ++ Box A :: Δ1))). apply i ; try assumption.
rewrite top_boxes_distr_app. simpl. apply in_or_app. right. apply in_eq.
Qed.

Lemma finite_KR_premises_of_S : forall (s : Seq), existsT2 listKRprems,
              (forall prems, ((KRRule prems s) -> (InT prems listKRprems)) *
                             ((InT prems listKRprems) -> (KRRule prems s))).
Proof.
intros. destruct s.
exists (prems_Box_R (top_boxes l0) (l,l0)).
intros. split ; intro.
- inversion X. subst.
  pose (@KR_help2 (unboxed_list BΓ, [A]) (l, Δ0 ++ Box A :: Δ1)). apply i.
  assumption.
- pose (@KR_help1 prems (l, l0)). apply k. assumption.
Qed.