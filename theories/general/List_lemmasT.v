Require Import List.
Import ListNotations.
Require Import PeanoNat.
Set Implicit Arguments.

Require Import existsT.
Require Import genT gen.


Open Scope type_scope.

Ltac app_assoc_solve G := rewrite <- (app_assoc G); reflexivity.
Ltac app_assoc_solve2 G H := rewrite <- (app_assoc G); simpl;
                             rewrite <- (app_assoc H); reflexivity.
Ltac eapp_assoc_solve2 G H := erewrite <- (app_assoc G); simpl;
                             erewrite <- (app_assoc H); reflexivity.
Ltac app_assoc_hyp G H := rewrite <- (app_assoc G) in H.
Ltac app_assoc_hyp_inv G H := rewrite <- (app_assoc G) in H; apply app_inv_head in H.

Ltac list_assoc_l := repeat (rewrite !app_assoc || rewrite !app_comm_cons).
Ltac list_assoc_r := 
  repeat (rewrite <- !app_assoc || rewrite <- !app_comm_cons).
Ltac list_app_nil := repeat (rewrite !app_nil_l || rewrite !app_nil_r).
Ltac list_assoc_l_simp := repeat
  (rewrite !app_assoc || rewrite !app_comm_cons || list_app_nil).
Ltac list_assoc_r_simp := repeat
  (rewrite <- !app_assoc || rewrite <- !app_comm_cons || list_app_nil).
Ltac list_assoc_l_simp' := repeat
  (rewrite !app_assoc || rewrite !app_comm_cons || rewrite !app_nil_l
  || rewrite !app_nil_r).
Ltac list_assoc_r_simp' := repeat
  (rewrite <- !app_assoc || rewrite <- !app_comm_cons || rewrite !app_nil_l
  || rewrite !app_nil_r).
Ltac list_eq_assoc := list_assoc_r ; reflexivity.

Lemma if_eq_rev_eq: forall {T} (a b : list T),
  a = b -> (rev a = rev b).
Proof. intros. subst. reflexivity. Qed.

Lemma if_rev_eq: forall {T} (a b : list T),
  (rev a = rev b) -> a = b.
Proof. intros. 
pose (@if_eq_rev_eq T (rev a) (rev b) H).
rewrite -> !rev_involutive in e.
exact e.
Qed.

(* rewriting with this won't loop, useful following list_assoc_l *)
Lemma cons_single A X (v : A) Y: X ++ v :: Y = X ++ [v] ++ Y.
Proof. simpl. reflexivity. Qed.

Lemma partition_2_2 : forall {A : Type} (l1 l2 l3 l4 : list A) a b,
l1 ++ a :: l2 = l3 ++ b :: l4 ->
  (exists l5, l1 = l3 ++ b :: l5 /\ l4 = l5 ++ a :: l2) \/
  (l3 = l1 /\ a = b /\ l2 = l4) \/
  (exists l5, l3 = l1 ++ a :: l5 /\ l2 = l5 ++ b :: l4).
Proof.
  induction l1; intros l2 l3 l4 b c H.
  - simpl in *. destruct l3.
    right. left. simpl in *. inversion H.
    subst. apply conj. reflexivity. apply conj; reflexivity.
    simpl in H. inversion H as [[H2 H3]].
    subst. right. right. exists l3.  apply conj; reflexivity.
    
  - destruct l3. simpl in *. inversion H as [[H2 H3]].
    subst. left. exists l1.  apply conj; reflexivity.
    simpl in H. inversion H as [[H2 H3]]. subst.
    apply IHl1 in H3. destruct H3 as [[l5 [H4 H5]] | [[H4 H5] | [l5 [H4 H5]]]];
                        subst.
    + left. exists l5. simpl.  apply conj; reflexivity. 
    + right. left.  apply conj. reflexivity.  assumption. 
    + right. right. exists l5. apply conj; reflexivity.
Qed.

Lemma partition_2_2T : forall {A : Type} (l1 l2 l3 l4 : list A) a b,
l1 ++ a :: l2 = l3 ++ b :: l4 ->
  (existsT2 l5, (l1 = l3 ++ b :: l5) * (l4 = l5 ++ a :: l2)) +
  (((l3 = l1)* (a = b) * (l2 = l4)) +
  (existsT l5, (l3 = l1 ++ a :: l5) * (l2 = l5 ++ b :: l4))).
Proof.
  induction l1; intros l2 l3 l4 b c H.
  - simpl in *. destruct l3.
    right. left. simpl in *. inversion H.
    subst. repeat split. 
    simpl in H. inversion H as [[H2 H3]].
    subst. right. right. exists l3.  repeat split. 
    
  - destruct l3. simpl in *. inversion H as [[H2 H3]].
    subst. left. exists l1.  repeat split. 
    simpl in H. inversion H as [[H2 H3]]. subst.
    apply IHl1 in H3. destruct H3 as [[l5 [H4 H5]] | [[[H4 H5]] | [l5 [H4 H5]]]];
                        subst.
    + left. exists l5. simpl.  repeat split. 
    + right. left.  repeat split. 
    + right. right. exists l5. repeat split. 
Qed.

Lemma partition_3_2 : forall {A : Type}  (Gam Delt : list A) G' H' Gam1 Delt1 Gam2 Delt2 G H J,
    G ++ (Gam1, Delt1) :: H ++ (Gam2, Delt2) :: J = G' ++ (Gam, Delt) :: H' ->
    (exists l, G = G' ++ (Gam,Delt) :: l /\ H' = l ++ (Gam1, Delt1) :: H ++ (Gam2, Delt2) :: J) \/
    (G' = G /\ Gam1 = Gam /\ Delt1 = Delt /\ H' =  H ++ (Gam2, Delt2) :: J) \/
    (exists l1 l2, G' = G ++ (Gam1, Delt1) :: l1 /\
                   H = l1 ++ (Gam, Delt) :: l2 /\
                   H' = l2 ++ (Gam2, Delt2) :: J) \/
    (G' = G ++ (Gam1,Delt1) :: H /\ Gam2 = Gam /\ Delt2 = Delt /\ J = H' ) \/
    (exists l, G' = G ++ (Gam1, Delt1) :: H ++ (Gam2, Delt2) :: l /\
               J = l++ (Gam, Delt) ::H').
Proof.
  intros A l1 m1 G' H' l2 m2 l3 m3 G H J.
  revert G J H l1 m1 G' H' l2 m2 l3 m3.
  induction G; intros J H l1 m1 G' H' l2 m2 l3 m3 H2.
  - simpl in *. destruct G'.
    right. left. simpl in H2. inversion H2. 
    repeat apply conj; reflexivity.
    simpl in H2. inversion H2 as [[H3 H4]].
    right. right. edestruct  (partition_2_2 _ _ _ _ _ _ H4) as [H0 | [[H0 H5] | H0]].
    + left. destruct H0 as [l5 [H0' HH]]. subst. exists G', l5.
      repeat apply conj; try reflexivity. 
    + right. left. subst. inversion H2 as [H3]. apply app_inv_head in H3.
      inversion H3.
      repeat apply conj; reflexivity.
    + right. right. destruct H0 as [l5 [H0' H5]]. exists l5.
      subst.  inversion H2. app_assoc_hyp_inv H H1. simpl in H1.
      inversion H1.
      repeat apply conj; reflexivity.
  -  simpl in *. destruct G'. simpl in *. left.
     inversion H2 as [[H3 H4]].
     exists G. 
     repeat apply conj; reflexivity.
     simpl in H2. inversion H2 as [[H3 H4]].
     apply IHG in H4.
     destruct H4 as [ [ll [HH1 HH2]] | 
                      [[HH1 [HH2 [HH3]]] | 
                       [ [ll1 [ll2 [HH1 [HH2 HH3]]]] | 
                         [[HH1 [HH2 [HH3 HH4]]] | [ll [HH1 HH2]]]]]]; subst.
     + left. exists ll. 
       repeat apply conj; reflexivity.
     + right. left.  
       repeat apply conj; reflexivity.
     + right. right. left. exists ll1. exists ll2. 
       repeat apply conj; reflexivity.
     + right. right. right. left. 
       repeat apply conj; reflexivity.
     + right. right. right. right. exists ll. 
       repeat apply conj; reflexivity.

Unshelve.    
all : try assumption.
Qed.

Lemma eq_app_canc1 : forall {A : Type} (l1 l2 l2': list A),
  (l1 ++ l2 = l1 ++ l2') <-> (l2 = l2').
Proof. intros.  unfold iff. split ; intros.
  induction l1. simpl in H. exact H.
  eapply IHl1. simpl in H. inversion H. reflexivity.
  subst. reflexivity. Qed.

Lemma eq_app_canc2 : forall {A : Type} (l1 l1' l2: list A),
  (l1 ++ l2 = l1' ++ l2) <-> (l1 = l1').
Proof. intros.  unfold iff. split ; intros.
  apply if_eq_rev_eq in H.
  rewrite -> !rev_app_distr in H.
  rewrite -> eq_app_canc1 in H.
  apply if_rev_eq in H. exact H.
  subst. reflexivity. Qed.

Lemma app_cons_single : forall {A : Type} (l1 l2 : list A) a,
  l1 ++ a :: l2 = (l1 ++ [a]) ++ l2.
Proof.
  induction l1; intros. reflexivity.
  simpl. rewrite IHl1. reflexivity.
Qed.

Lemma partition_2_3 : forall {A : Type} (l1 l2 l3 l4 : list A) a b,
    l1 ++ a :: b :: l2 = l3 ++ l4 ->
    (l3 = l1 /\ l4 = a :: b :: l2) \/
    (exists l5, l1 = l3 ++ l5 /\ l4 = l5 ++ a :: b :: l2) \/
    (l3 = l1 ++ [a] /\ l4 = b :: l2) \/
    (l3 = l1 ++ [a;b] /\ l4 = l2) \/
    (exists l5, l3 = l1 ++ [a;b] ++ l5 /\ l2 = l5 ++ l4).
Proof.
  induction l1; intros *; intros H.
  - destruct l3. left.  auto. 
    right.
    simpl in *. inversion H as [[H1 H2]]. subst.
    destruct l3. simpl in *. subst.
    right. left.  auto. 
    simpl in H2. inversion H2 as [[H1 H3]].
    subst. right. right. right. exists l3. auto. 
    
  - simpl in *. destruct l3. right. left. 
    exists (a::l1). auto.
    simpl in *. inversion H as [[H1 H2]].  subst.
    apply IHl1 in H2. 
    destruct H2 as [ [H3 H4] | [[l5 [H3 H4]] | [ [H3 H4] | [ [H3 H4] | [l5 [ H4 H5]]]]]];
      subst.
    + left. auto. 
    + inversion H as [H2]. app_assoc_hyp_inv l3 H2. subst. right. left.
      exists l5. auto. 
    + inversion H as [H2]. rewrite <- app_assoc in H2.
      apply app_inv_head in H2. simpl in H2. inversion H2 as [H3].
      subst. right. right. left. apply conj; reflexivity.
    + inversion H as [H2]. app_assoc_hyp_inv l1 H2. simpl in H2.
      inversion H2 as [H3]. subst. right. right. right. left.
      apply conj; reflexivity.
    + subst. right. right. right. right. inversion H as [H2].
      app_assoc_hyp_inv l1 H2. simpl in *. inversion H2. subst.
      exists l5.  apply conj; reflexivity.
Qed.

Lemma subst_dep : forall (T : Type) (G1 G2 : T) P (P2 : forall (G : T), P G  -> nat)  (D1 : P G1),
    G1 = G2  ->
    exists (D2 : P G2), P2 G1 D1 = P2 G2 D2.
Proof.
  intros T G1 G2 P P2 D1 Heq.
  generalize dependent D1. subst.
  intros D1. exists D1. reflexivity.
Qed.

Ltac finish_ht_admis_ex1 := simpl; apply le_n_S;  assumption.
Ltac finish_ht_admis_ex2 := simpl; apply le_n_S;
                            eapply (Nat.le_trans _ _ _ _ _);
                            assumption.
Ltac find_trans_solve :=      match goal with
               | [ H1 : ?n1 <= ?n2, H2 : ?n2 <= ?n3 |- ?n1 <= ?n3] =>
                 apply (Nat.le_trans n1 n2 n3 H1 H2) end.
Ltac finish_ht_admis_ex3 :=  simpl; apply le_n_S; find_trans_solve.
Ltac ap_part_2_2 P1 l5 P3 P4 P5 :=
  apply partition_2_2 in P1;
  destruct P1 as [ [l5 [P3 P4]] | [ [P3 [P4 P5]] |  [l5 [P3 P4]]]].

Ltac ap_part_2_3 P5 l5 P55 := apply partition_2_3 in P5;
    destruct P5 as [ [P5 PP5] | [ [l5 [P5 PP5]]
                                | [[P5 PP5] | [[P5 PP5] | [l5 [P5 PP5]]]]]].

Lemma list_rearr1 : forall {A : Type} (a : A) G0 l5 H,
      (G0 ++ a :: l5 ++ H) =
           (((G0 ++ [a]) ++ l5) ++  H).
Proof.
  intros.     rewrite app_cons_single.
  rewrite app_assoc. reflexivity.
Qed.

Lemma list_rearr2 : forall {A : Type} (a : A) G0 l5 H,
  ((G0 ++ [a]) ++ l5) ++ H =  G0 ++ a :: l5 ++ H.
Proof. intros. do 2 rewrite <- app_assoc. reflexivity. Qed.

Lemma list_rearr4 : forall {T1 T2 T3 : Type} G (A B E : T1) (Delt : list T2)
                           Gam1 Gam2 (delt : T3) H,
    G ++ (Gam1 ++ E :: A :: B :: Gam2, Delt, delt) :: H =
    G ++ ((Gam1 ++ [E]) ++ A :: B :: Gam2, Delt, delt) :: H.
Proof. intros. rewrite <- app_assoc.  reflexivity. Qed.

Lemma list_rearr5 : forall {T1 T2 T3 : Type} G (E B : T1)
                           Gam1 Gam2 (Delt : list T2) (delt : T3) H,
    G ++ ((Gam1 ++ [E]) ++ B :: Gam2, Delt, delt) :: H =
    G ++ (Gam1 ++ E :: B :: Gam2, Delt, delt) :: H.
Proof. intros. rewrite <- app_assoc. reflexivity. Qed.

Lemma list_rearr6 : forall {T1 T2 T3 : Type} (E : T1) G l5 Gam3 Gam2
                           (Delt : list T2) (delt : T3) H,
    G ++ (Gam3 ++ E :: l5 ++ Gam2, Delt, delt) :: H =
    G ++ (((Gam3 ++ [E]) ++ l5) ++ Gam2, Delt, delt) :: H.
Proof. intros. rewrite (app_cons_single Gam3).
       rewrite (app_assoc _ l5). reflexivity.
Qed.

Lemma list_rearr7 : forall {T1 T2 T3 : Type} G (E : T1) l5 Gam3 Gam2
                           (Delt : list T2) (delt : T3) H,
G ++ (((Gam3 ++ [E]) ++ l5) ++ Gam2, Delt, delt) :: H =
      G ++ (Gam3 ++ E :: l5 ++ Gam2, Delt, delt) :: H.
Proof. intros.  do 2 rewrite <- app_assoc. reflexivity. Qed.

Lemma list_rearr8 : forall {T1 T2 T3 : Type} G Gam1 Gam2 (A B : T1)
                           (Delt : list T2) (delt : T3) H,
 G ++ ((Gam1 ++ [A; B]) ++ Gam2, Delt, delt) :: H =
      G ++ (Gam1 ++ A :: B :: Gam2, Delt, delt) :: H.
Proof. intros. rewrite <- app_assoc. reflexivity. Qed.

Lemma list_rearr9 : forall {T1 T2 T3 : Type} G Gam1 Gam2 (A B : T1)
                           (Delt : list T2) (delt : T3) H,
G ++ (Gam1 ++ B :: A :: Gam2, Delt, delt) :: H =
G ++ (((Gam1 ++ [B]) ++ [A]) ++ Gam2, Delt, delt) :: H.
Proof. intros.   rewrite (app_cons_single _ _ B);
  rewrite (app_cons_single _ _ A). reflexivity.
Qed.

Lemma list_rearr10 : forall {T1 T2 T3 : Type} G Gam1 Gam4 (A B : T1) l5
                           (Delt : list T2) (delt : T3) H,
G ++ ((Gam1 ++ [A; B] ++ l5) ++ Gam4, Delt, delt) :: H =
       G ++ (Gam1 ++ A :: B :: l5 ++ Gam4, Delt, delt) :: H.
Proof. intros. rewrite <- app_assoc. reflexivity. Qed.

Lemma list_rearr11 : forall {T1 T2 T3 : Type} G Gam1 Gam4 (A B : T1) l5
                           (Delt : list T2) (delt : T3) H,
G ++ (Gam1 ++ B :: A :: l5 ++ Gam4, Delt, delt) :: H =
      G ++ ((((Gam1 ++ [B]) ++ [A]) ++ l5) ++ Gam4, Delt, delt) :: H.
Proof.
  intros. rewrite (app_cons_single _ _ B).
  rewrite (app_cons_single _ _ A).
  rewrite (app_assoc _ l5). reflexivity.
Qed.

Lemma list_rearr13 : forall {T : Type} a (G l5 H : list T),
     G ++ a :: l5 ++ H = (G ++ a :: l5) ++ H.
Proof.
  intros. rewrite app_comm_cons. rewrite app_assoc.
  reflexivity. Qed.

Lemma list_rearr14 : forall {T : Type} a b (F G H : list T),
  F ++ a :: (G ++ b :: H) = (F ++ a :: G) ++ b :: H.
Proof.
  intros. rewrite app_comm_cons. rewrite app_assoc.
  reflexivity. Qed.

Lemma list_rearr15 : forall {T Xt : Type} (F G H : list T) (X : Xt),
  (F ++ (G ++ H), X) = ((F ++ G) ++ H, X).
Proof.  intros. rewrite app_assoc.  reflexivity. Qed.

Lemma list_rearr15_R : forall {T Xt : Type} (F G H : list T) (X : Xt),
  (X, F ++ (G ++ H)) = (X, (F ++ G) ++ H).
Proof.  intros. rewrite app_assoc.  reflexivity. Qed.

Lemma list_rearr16' : forall {T : Type} (F G : list T) (a : T),
  F ++ (a :: G) = (F ++ [a]) ++ G.
Proof.  intros. rewrite <- app_assoc. simpl.  reflexivity. Qed.

Lemma list_rearr16 : forall {T Xt : Type} (F G : list T) (a : T) (X : Xt),
  (F ++ (a :: G), X) = ((F ++ [a]) ++ G, X).
Proof.  intros. rewrite <- app_assoc. simpl.  reflexivity. Qed.

Lemma list_rearr16_R : forall {T Xt : Type} (F G : list T) (a : T) (X : Xt),
  (X, F ++ (a :: G)) = (X, (F ++ [a]) ++ G).
Proof.  intros. rewrite <- app_assoc. simpl.  reflexivity. Qed.

Lemma list_rearr17_R : forall {T1 T2 : Type} (Phi : T2) Delt1 (B A : T1) eqr3 U Psi2,
(Phi, Delt1 ++ B :: A :: eqr3 ++ U :: Psi2) =
(Phi, (Delt1 ++ B :: A :: eqr3) ++ U :: Psi2).
Proof. intros. rewrite <- app_assoc. reflexivity. Qed.

(* not sure if we ever need this *)
Lemma list_rearr18 : forall {T : Type} (F G H : list T) (a : T),
  (F ++ G ++ a :: H) = (F ++ G) ++ a :: H.
Proof.  intros. apply app_assoc. Qed.

Lemma list_rearr19 : forall {T : Type} (F G H : list T) (a : T),
  (F ++ G) ++ a :: H = F ++ (G ++ [a]) ++ H.
Proof.  intros. list_assoc_r. simpl. reflexivity. Qed.

Lemma list_rearr20 : forall {T : Type} (F G : list T) (a b : T),
  F ++ a :: b :: G = F ++ [a ; b] ++ G.
Proof.  intros. list_assoc_r. simpl. reflexivity. Qed.

Lemma list_rearr21 : forall {T : Type} (F G : list T) (a b : T),
  (F ++ [a]) ++ b :: G = F ++ [a ; b] ++ G.
Proof.  intros. list_assoc_r. simpl. reflexivity. Qed.

Lemma list_rearr22 : forall {T : Type} (F G : list T) (a b : T),
  F ++ a :: b :: G = (F ++ [a]) ++ b :: G.
Proof.  intros. list_assoc_r. simpl. reflexivity. Qed.

Lemma list_rearr23 : forall {T : Type} (b a : T) (F G : list T),
  a :: F ++ b :: G = (a :: F) ++ b :: G.
Proof.  intros. list_assoc_r. simpl. reflexivity. Qed.

Lemma cons_eq_app: forall (A : Type) (x y z : list A) (a : A),
  a :: x = y ++ z -> y = [] /\ z = a :: x \/
  exists (y' : list A), y = a :: y' /\ x = y' ++ z.
Proof.
intros.
destruct y. simpl in H. subst. tauto.
simpl in H.
injection H.
intros. right. subst.
exists y. tauto.
Qed.

Lemma cons_eq_appT: forall (A : Type) (x y z : list A) (a : A),
  a :: x = y ++ z -> sum ((y = []) * (z = a :: x)) 
  (sigT (fun y' : list A => prod (y = a :: y') (x = y' ++ z))).
Proof.
intros.
destruct y. simpl in H. subst. tauto.
simpl in H.
injection H.
intros. right. subst.
exists y. tauto.
Qed.

Lemma cons_eq_appT2: forall (A : Type) (x y z : list A) (a : A),
    a :: x = y ++ z ->
    ((y = []) * (z = a :: x)) +
  existsT2 (y' : list A), (y = a :: y') * (x = y' ++ z).
Proof.
  intros.
  destruct y. simpl in H. subst. tauto.
  simpl in H.
  injection H.
  intros. right. subst.
  exists y. tauto.
Qed.

Definition app_eq_cons (A : Type) (x y z : list A) (a : A) p :=
  @cons_eq_app A x y z a (eq_sym p).

Definition app_eq_consT2 (A : Type) (x y z : list A) (a : A) p :=
  @cons_eq_appT2 A x y z a (eq_sym p).

Lemma app_eq_nilT : forall (A : Type) (l l' : list A),
    l ++ l' = [] -> (l = []) * (l' = []).
Proof.  destruct l; intros l' H. tauto. discriminate. Qed.

Lemma app_eq_app: forall (A : Type) (w x y z : list A),
  w ++ x = y ++ z -> exists (m : list A),
    w = y ++ m /\ z = m ++ x \/ y = w ++ m /\ x = m ++ z.
Proof.
intro. intro.
induction w.
simpl. intros.
exists y. rewrite H. tauto.
intros. simpl in H.
apply cons_eq_app in H.
destruct H.  destruct H.  rewrite H. simpl.
exists (a :: w).  rewrite H0. simpl. tauto.
destruct H.  destruct H.
apply IHw in H0.  destruct H0.  destruct H0. destruct H0.
rewrite H.  rewrite H0.  rewrite H1.  simpl.
exists x1. tauto.
destruct H0.
rewrite H.  rewrite H0.  rewrite H1.  simpl.
exists x1. tauto.
Qed.

Lemma app_eq_appT: forall (A : Type) (w x y z : list A),
  w ++ x = y ++ z -> sigT (fun m : list A =>
    sum ((w = y ++ m) * (z = m ++ x)) ((y = w ++ m) * (x = m ++ z))).
Proof.  intro. intro.  induction w.
simpl. intros.
exists y. rewrite H. tauto.
intros. simpl in H.
apply cons_eq_appT in H.
destruct H.  destruct p.  subst. simpl.
exists (a :: w). simpl.  tauto.
destruct s.  destruct p.
apply IHw in e0.  destruct e0. 
destruct s ; destruct p ; subst ; simpl ; exists x1 ; tauto.
Qed.

Lemma app_eq_appT2: forall (A : Type) (w x y z : list A),
  w ++ x = y ++ z -> existsT2 (m : list A),
    ((w = y ++ m) * (z = m ++ x)) + ((y = w ++ m) * (x = m ++ z)).
Proof.
  induction w; intros *; intros H; simpl in *.
  subst. exists y. right. tauto.
  apply cons_eq_appT2 in H. destruct H as [[H1 H2]| [l [? H3]]]; subst.
  exists (a :: w). tauto.
  eapply IHw in H3. destruct H3 as [l2 [[H3 H4] | [H3 H4]]]; subst.
  exists l2. tauto.
  exists l2. tauto.
Qed.

Definition app_eq_consT (A : Type) (x y z : list A) (a : A) p :=
  @cons_eq_appT A x y z a (eq_sym p).

Lemma list_eq_nil: forall (A : Type) (x y : list A) (u : A),
  x ++ u :: y = [] -> False.
Proof.  intros.  apply app_eq_nil in H.  cD.  discriminate.  Qed.

Lemma app_eq_unitT2 :
  forall {A : Type} (x y:list A) (a:A),
    x ++ y = [a] -> ((x = []) * (y = [a])) + ((x = [a]) * (y = [])).
Proof.
  intros *; intros H.
  destruct x. auto.
  simpl in *. inversion H. subst. right.
  rewrite H2. apply app_eq_nilT in H2. destruct H2 as [H2a H2b].
  subst. auto.
Qed.

Definition nil_eq_list A x y u p := @list_eq_nil A x y u (eq_sym p).
Definition nil_eq_app A u v p := @app_eq_nil A u v (eq_sym p).
Definition nil_eq_appT A u v p := @app_eq_nilT A u v (eq_sym p).
Definition unit_eq_app A x y a p := @app_eq_unit A x y a (eq_sym p).
Definition unit_eq_appT2 A x y a p := @app_eq_unitT2 A x y a (eq_sym p).

Lemma list_eq_single: forall (A : Type) (x y : list A) (u v : A),
  x ++ u :: y = [v] -> x = [] /\ y = [] /\ u = v.
Proof.  intros.  apply app_eq_cons in H.  sD.  injection H0 as.  subst.  tauto.
        apply app_cons_not_nil in H1.  contradiction.  Qed.

Lemma list_eq_singleT: forall (A : Type) (x y : list A) (u v : A),
  x ++ u :: y = [v] -> prod (x = []) (prod (y = []) (u = v)).
Proof.  intros.  apply app_eq_consT in H.  sD.  injection H0 as.  subst.  tauto.
  apply nil_eq_appT in H1. cD. discriminate H2. Qed.

Lemma list_eq_singleT_nobrac: forall (A : Type) (x y : list A) (u v : A),
  x ++ u :: y = [v] -> (x = []) * (y = []) * (u = v).
Proof.  intros.  apply app_eq_consT2 in H. sD.  injection H0 as.  subst.  tauto.
  apply app_cons_not_nil in H1.  contradiction.  Qed.

Definition single_eq_list A x y u v p := @list_eq_single A x y u v (eq_sym p).
Definition single_eq_listT A x y u v p := @list_eq_singleT A x y u v (eq_sym p).
Definition single_eq_listT_nobrac A x y u v p := @list_eq_singleT_nobrac A x y u v (eq_sym p).

Lemma nnn_app_eq: forall {A : Type} (x : list A), [] ++ [] ++ [] ++ x = x.
Proof.  intros.  simpl. reflexivity. Qed.

Definition eq_nnn_app {A : Type} (x : list A) := eq_sym (nnn_app_eq x).


(* Caitlin added from here for weakening. *)

Lemma cons_singleton : forall {A : Type} (l : list A) a,
    a :: l = [a] ++ l.
Proof. induction l; intros b; firstorder. Qed.

Ltac list_cons_singleton a := repeat rewrite (cons_singleton _ a).
Ltac tac_cons_singleton_arg a l :=
    match l with
    | nil => idtac
    | _ => rewrite (cons_singleton l a)
    end.

Ltac tac_cons_singleton :=
  repeat
  match goal with
   | [ |- context [?a :: ?l]] => progress (tac_cons_singleton_arg a l)
  end.

(* Caitlin added from here for contraction. *)

Ltac rem_nil_goal := repeat rewrite app_nil_l; repeat rewrite app_nil_r.
Ltac rem_nil_hyp_arg H := repeat rewrite app_nil_l in H; repeat rewrite app_nil_r in H.
Ltac rem_nil_hyp :=
  match goal with
  | [ H : context[ [] ++ ?A ] |- _ ] => progress rem_nil_hyp_arg H
  | [ H : context[ ?A ++ [] ] |- _ ] => progress rem_nil_hyp_arg H
  | _ => idtac
  end.

Ltac rem_nil := rem_nil_hyp; rem_nil_goal.

Ltac list_assoc_r_single :=
  list_assoc_r; tac_cons_singleton; rem_nil.

Ltac app_bracket_middle_arg l :=
  repeat match l with
         | ?l1 ++ ?l2 ++ ?l3 ++ ?l4 => rewrite (app_assoc l2)
         end.

Ltac add_empty_hyp_L l H :=  rewrite <- (app_nil_l l) in H.
Ltac add_empty_goal_L l :=  rewrite <- (app_nil_l l).
Ltac add_empty_hyp_R l H :=  rewrite <- (app_nil_r l) in H.
Ltac add_empty_goal_R l :=  rewrite <- (app_nil_r l).
Ltac rem_empty_hyp_L l H :=  rewrite (app_nil_l l) in H.
Ltac rem_empty_goal_L l :=  rewrite (app_nil_l l).
Ltac rem_empty_hyp_R l H :=  rewrite (app_nil_r l) in H.
Ltac rem_empty_goal_R l :=  rewrite (app_nil_r l).

Ltac breakdown :=
  repeat (
      repeat (match goal with
              | [ H : ?A ++ ?B = ?x ++ ?y |- _ ] => apply app_eq_app in H; sE; subst
              end) ;
      repeat (match goal with
              | [H2 : [?a] = ?A ++ ?B |- _ ] => apply unit_eq_app in H2; sE; subst
              end));
  repeat try rewrite app_nil_r; repeat try rewrite app_nil_l;
  repeat (match goal with
          | [ H3 : context[ ?x ++ [] ] |- _ ] => rewrite (app_nil_r x) in H3
          end);
  repeat (match goal with
          | [ H3 : context[ [] ++ ?x ] |- _ ] => rewrite (app_nil_l x) in H3
          end).

Ltac tac_cons_singleton_arg_hyp H a l :=
    match l with
    | nil => idtac
    | _ => rewrite (cons_singleton l a) in H
    end.

Ltac tac_cons_singleton_hyp H :=
  repeat
  match goal with
  | [ H : context [?a :: ?l] |- _] => progress (tac_cons_singleton_arg_hyp H a nil ||
                                                tac_cons_singleton_arg_hyp H a l)
  end.

Ltac list_assoc_r_s_arg H :=
  tac_cons_singleton_hyp H; repeat rewrite <- !app_assoc in H.


Ltac list_assoc_r_arg H :=
  repeat (rewrite <- !app_assoc in H || rewrite <- !app_comm_cons in H).
Ltac list_assoc_l'_arg H := repeat (rewrite !app_assoc in H || rewrite !app_comm_cons in H).
Ltac list_assoc_l'_arg_conc H := list_assoc_l; list_assoc_l'_arg H.
Ltac list_assoc_r_arg_conc H := list_assoc_r; list_assoc_r_arg H.


Ltac list_assoc_r_singleton_hyp H :=
  list_assoc_r_arg H; tac_cons_singleton_hyp H.

Ltac list_assoc_r_singleton_hyp2 H :=
  list_assoc_r_s_arg H.

Definition non_empty {A : Type} (l : list A) :=
  match l with
  | nil => False
  | _ => True
  end.

Ltac check_app_head l1 l2 :=
  match l1 with
  | l2 ++ ?l3 => idtac
  | _ => fail
  end.

Ltac check_app_tail l1 l2 :=
  match l1 with
  | ?l3 ++ l2 => idtac
  | _ => fail
  end.

(* Updated *)
Ltac clear_useless :=
  repeat match goal with
         | [H : ?a = ?a |- _] => clear H
         | [H : [?a] = [?a] |- _] => clear H
         | [H : ?a :: ?b = ?a :: ?b |- _] => clear H
         | [H1 : ?a, H2 : ?a |- _] => clear H2
         | [H1 : [?a] = [?b], H2 : ?c = ?d |- _ ] =>
           rewrite H2 in H1; match type of H1 with ?d = ?d => clear H1 end
         | [H1 : [?a] = [?b], H2 : ?c = ?d |- _ ] =>
           rewrite <- H2 in H1; match type of H1 with ?d = ?d => clear H1 end
         end.

Ltac clear_useless_weak :=
  repeat match goal with
         | [H : ?a = ?a |- _] => clear H
         | [H : [?a] = [?a] |- _] => clear H
         | [H : ?a :: ?b = ?a :: ?b |- _] => clear H
         | [H1 : ?a, H2 : ?a |- _] => clear H2
         end.

(*
Lemma testing_clear_useless : forall (a b c : nat) (l1 l2 l3 : list nat),
    a::l1 = b::l2 ->
    [b] = [c] ->
    c = a ->
    l2 = l2 ->
    [l2] = [l2] ->
    True.
Proof.  
  clear_useless.
Admitted.
 *)

Ltac inv_singleton :=
    repeat ( match goal with
       | [ H : ?a :: [] = ?c :: ?d |- _ ] => inversion H; subst
       | [ H : ?a :: ?b = ?c :: [] |- _ ] => inversion H; subst
       | [ H : ?a :: ?b = ?c :: ?d |- _ ] => inversion H; subst
       | [ H : ((?a,?b) = ?c) |- _ ] => inversion H; subst
       | [ H : ?c = (?a,?b) |- _ ] => inversion H; subst
             end; clear_useless).

Ltac inversion_cons :=
  repeat match goal with
         | [ H : ?a :: ?l1 = ?b :: ?l2 |- _] => inversion H; subst; clear_useless
         end.

(* begin git conflict 1 *)

Ltac inversion_pair :=
  repeat (clear_useless; match goal with
  | [ H : (?a,?b)=(?c,?d) |- _ ] => inversion H; clear H; subst
  end; clear_useless).

Ltac inv_singleton_str :=
    repeat ( match goal with
       | [ H : ?a :: [] = ?c :: ?d |- _ ] => inversion H; subst
       | [ H : ?a :: ?b = ?c :: [] |- _ ] => inversion H; subst
       | [ H : ?a :: ?b = ?c :: ?d |- _ ] => inversion H; subst
       | [ H : ((?a,?b) = ?c) |- _ ] => inversion H; subst
       | [ H : ?c = (?a,?b) |- _ ] => inversion H; subst
       | [ H : ?C ?a = ?C ?b |- _ ] => inversion H; subst
             end; clear_useless).


Lemma tail_inv_singleton : forall {T : Type} (l1 l2 : list T) a b,
    l1 ++ [a] = l2 ++ [b] -> (l1 = l2) * (a = b).
Proof.
  induction l1; intros l2 c d Heq.
  simpl in *. destruct l2. simpl in Heq. inversion Heq. firstorder.
  simpl in Heq. destruct l2. simpl in Heq. inversion Heq.
  simpl in Heq. inversion Heq.
  simpl in Heq. destruct l2. simpl in Heq. destruct l1. simpl in Heq. inversion Heq.
  simpl in Heq. inversion Heq.
  simpl in Heq. inversion Heq. subst.
  apply IHl1 in H1. destruct H1 as [IH1 IH2].
  subst. firstorder.
Qed.

Lemma tail_inv_singleton2 : forall {T : Type} (l1 l2 : list T) a b a' b',
    l1 ++ [a;a'] = l2 ++ [b;b'] -> (l1 = l2) * (a = b) * (a' = b').
Proof.
  induction l1; intros l2 c d a' b' Heq.
  simpl in *. destruct l2. simpl in Heq. inversion Heq. firstorder.
  simpl in Heq. destruct l2. simpl in Heq. inversion Heq.
  simpl in Heq. destruct l2. inversion Heq.
  simpl in Heq. inversion Heq.
  destruct l2. simpl in Heq. destruct l1. simpl in Heq. inversion Heq.
  simpl in Heq. destruct l1; inversion Heq.
  simpl in Heq. inversion Heq. subst.
  apply IHl1 in H1. destruct H1 as [[H1 H2] H3]. 
  subst. firstorder.
Qed.

Lemma list_insert1 : forall {T : Type} (Gam1 Gam2 Sigm1 Sigm2 : list T) A B,
    Gam1 ++ [A] ++ Gam2 = Sigm1 ++ Sigm2 ->
    existsT2 Gam1' Gam2', (Sigm1 ++ [B] ++ Sigm2 = Gam1' ++ [A] ++ Gam2') *
                      (forall B, InT B Gam1 -> InT B Gam1') *
                      (forall B, InT B Gam2 -> InT B Gam2').
Proof.
  intros *; intros Heq.
  destruct Sigm2. rewrite app_nil_r.
  rewrite app_nil_r in Heq. subst.
  eexists. eexists.
  split. split. rewrite <- app_assoc. simpl. reflexivity.
  firstorder.
  intros C HC. apply InT_appL. assumption.
  apply partition_2_2T in Heq.
  sD. subst.
  eexists (Sigm1 ++ [B] ++ [t] ++ Heq).
  eexists Gam2. split. split. list_assoc_r. reflexivity. firstorder.
  apply InT_appE in X. destruct X. apply InT_appL. assumption.
  apply InT_appR. apply InT_appR.
  assumption.
  firstorder.
  subst.
  eexists (Gam1 ++ [B]), (Sigm2). split. split.
  assert (Hyp: t :: Sigm2 = [t] ++ Sigm2). simpl. reflexivity.
  rewrite Hyp. apply app_assoc.
  intros C HC. apply InT_appL. assumption.
  firstorder.
  subst.
  list_assoc_r. eexists Gam1, (Heq ++ [B] ++ [t] ++ Sigm2).
  split. split. reflexivity.
  firstorder.
  intros C HC. apply InT_appE in HC.
  destruct HC. apply InT_appL. assumption.
  apply InT_appR. apply InT_appR. assumption.
Qed.

  Inductive InT_pair_triple {T1 T2 T3 : Type} (t12 : T1*T2) : list ((list T1) * (list T2) * T3) -> Type :=
  | InT_pt_hd l a b c t1 t2 : t12 = (t1,t2) -> InT t1 a -> InT t2 b -> InT_pair_triple t12 ((a,b,c) :: l)
  | InT_pt_tl l a b c : InT_pair_triple t12 l -> InT_pair_triple t12 ((a,b,c) :: l).

Lemma  InT_pt_I : forall {T1 T2 T3 : Type} L1 (l1 l2 : list T1) (l3 l4 : list T2) (d : T3) A B,
  InT_pair_triple (A,B) (L1 ++ [(l1 ++ [A] ++ l2, l3 ++ [B] ++ l4, d)]).
Proof.
  induction L1; intros. simpl.
  econstructor. reflexivity.
  apply InT_appR. econstructor. reflexivity.
  apply InT_appR. econstructor. reflexivity.

  simpl. destruct a as [[a b] c].
  econstructor 2. apply IHL1.
Qed.

Lemma partition_singleton_app : forall {T : Type} (L1 L2 L3 : list T) A B,
    L1 ++ [A] = L2 ++ [B] ++ L3 ->
    ((L3 = []) * (L1 = L2) * (A = B)) +
    (existsT2 L4, (L3 = L4 ++ [A]) * (L1 = L2 ++ [B] ++ L4)).
Proof.
  induction L1; intros L2 L3 A B H.
  simpl in *. destruct L2. simpl in *. inversion H. firstorder.
  simpl in *. destruct L2; discriminate.
  simpl in H. destruct L2. simpl in *. inversion H. subst.
  right. exists L1. firstorder.
  simpl in H. inversion H. subst.
  apply IHL1 in H2. sD. subst. firstorder.
  subst. right. eexists. split; reflexivity.
Qed.


Lemma InT_mid : forall {T : Type} (l1 l2 : list T) A,
  InT A (l1 ++ [A] ++ l2).
Proof.
  intros. apply InT_appR. apply InT_appL.
  econstructor. reflexivity.
Qed.


Lemma InT_singleton_mid : forall {T : Type} (l1 l2 l3 l4 : list T) A B,
    A <> B ->
    l1 ++ [A] ++ l2 = l3 ++ [B] ++ l4 ->
    InT A l3 + InT A l4.
Proof.
  intros *. intros Hneq Heq.
  pose proof (InT_mid l1 l2 A) as Hin.
  rewrite Heq in Hin.
  apply InT_appE in Hin.
  destruct Hin. left. assumption.
  inversion i. subst. contradiction.
  subst. right. assumption.
Qed.

Lemma list_nil_or_tail_singleton : forall {T : Type} (l : list T),
    (l = []) + existsT2 l2 a, l = l2 ++ [a].
Proof.
  induction l.
  firstorder.
  right. destruct IHl. subst. exists nil, a. firstorder.
  destruct s as [l2' [a' H]].
  subst. exists (a :: l2'), a'.  firstorder. 
Qed.

Lemma InT_app_or : forall {T : Type} (l1 l2 : list T) A,
      InT A (l1 ++ l2) -> InT A l1 + InT A l2.
Proof.
induction l1. intros. rewrite app_nil_l in X. right. assumption.
intros. remember ((a :: l1) ++ l2) as l. destruct X.
subst. inversion Heql. left. apply InT_eq. inversion Heql.
subst. apply IHl1 in X. destruct X. left. apply InT_cons. assumption.
right. assumption.
Qed.

Lemma InT_or_app : forall {T : Type} (l1 l2 : list T) A,
       (InT A l1 + InT A l2) -> InT A (l1 ++ l2).
Proof.
induction l1. intros. rewrite app_nil_l. destruct X. inversion i.
assumption.
intros. destruct X. remember (a:: l1) as l. destruct i.
inversion Heql. subst. apply InT_eq. inversion Heql. subst.
simpl. apply InT_cons. apply IHl1. left. assumption.
simpl. apply InT_cons. apply IHl1. right. assumption.
Qed.



(*
Lemma partition_LNS_app_mid : forall {T1 T2 : Type} L1 L2 L3 (Gam Sigm Sigm' : list T1) (Delt \u03a0 \u03a0' : list T2) d,
    L1 ++ [(Gam,Delt,d);(Sigm,\u03a0,bac)] =
    L2 ++ (Sigm',\u03a0',fwd) :: L3 ->
    existsT2 L4, (L3 = L4 ++ [(Sigm,\u03a0,bac)]) * (L1 ++ [(Gam,Delt,d)] = L2 ++ [(Sigm',\u03a0',fwd)] ++ L4).
Proof.
  intros *; intros Heq.
  rewrite app_cons_single in Heq.
  destruct (list_nil_or_tail_singleont L3) as [|[l2 [a Heq2]]];
  subst. eapply tail_inv_singleton in Heq.
  destruct Heq as [H1 H2]. inversion H2.
  exists l2. subst.
  rewrite (cons_singleton (l2 ++ _)) in Heq.
  list_assoc_l'_arg Heq.
  eapply tail_inv_singleton in Heq.
  destruct Heq as [H1 H2]. subst. rewrite H1.
  firstorder.
Qed.
*)
Ltac hd_tl_inv_arg H :=
    match goal with
  | [ H : context[?a :: nil] |- _ ] => fail
  | [ H : context[?a :: ?l] |- _ ] => repeat rewrite (cons_singleton l a) in H
    end.

Ltac list_assoc_r_single_hyp :=
  match goal with
  | [ H : (?l1 : list ?T) = ?l2 |- _ ] => list_assoc_r_arg H; tac_cons_singleton_hyp H ; rem_nil_hyp_arg H
  end.

Ltac list_assoc_r_single_arg H :=
  list_assoc_r_arg H; tac_cons_singleton_hyp H ; rem_nil_hyp_arg H.

Lemma app_singleton_inversion : forall {T : Type} (l1 l2 : list T) a b,
    [a] ++ l1 = [b] ++ l2 -> (a = b) * (l1 = l2).
Proof. intros *;  intros H; inversion H. firstorder. Qed.

Lemma app_singleton_tl_inversion : forall {T : Type} (l1 l2 : list T) a b,
    l1 ++ [a] = l2 ++ [b] -> (a = b) * (l1 = l2).
Proof.
  intros T l1 l2 a b H.
  eapply if_eq_rev_eq in H.
  do 2 rewrite rev_unit in H.
  inversion H. apply if_rev_eq in H2.
  subst. firstorder.
Qed.

Ltac inv_app_hd :=
  repeat match goal with
  | [ H : [?a] ++ ?l1 = [?b] ++ ?l2 |- _ ] => apply app_singleton_inversion in H; destruct H as [? H]; try subst a; try subst b
  | _ => idtac
         end.

Ltac inv_app_tl :=
  repeat match goal with
  | [ H : ?l1 ++  [?a] = ?l2 ++ [?b] |- _ ] => apply app_singleton_tl_inversion in H; destruct H as [? H]; try subst a; try subst b
  | _ => idtac
         end.

Lemma app_hd_inversion : forall {T : Type} (l : list T) a b,
    [a] = [b] ++ l -> ( (a = b) * (l = []) ).
Proof.
  intros *; intros H.
  inversion H. firstorder.
Qed.

Lemma app_tl_inversion : forall {T : Type} (l : list T) a b,
    [a] = l ++ [b] -> ( (a = b) * (l = []) ).
Proof.
  induction l; intros aa bb H.
  simpl in *. inversion H. firstorder.
  simpl in H. inversion H.
  destruct l; discriminate.
Qed.

Ltac inv_app_hd_arg H :=
  repeat match type of H with
  | [?a] ++ ?l1 = [?b] ++ ?l2 => apply app_singleton_inversion in H; let H' := fresh "H" in destruct H as [H' H]; try rewrite H' in *; try rewrite <- H' in *
  | [?a] = [?b] ++ ?l2 => apply app_hd_inversion in H; let H' := fresh "H" in destruct H as [H' H]; try rewrite H' in *; try rewrite <- H' in *
  | [?b] ++ ?l2 = [?a] => symmetry in H; apply app_hd_inversion in H; let H' := fresh "H" in destruct H as [H' H]; try rewrite H' in *; try rewrite <- H' in *
  | _ => idtac
         end.

Ltac inv_app_tl_arg H :=
  repeat match type of H with
  | ?l1 ++  [?a] = ?l2 ++ [?b] => apply app_singleton_tl_inversion in H;let H' := fresh "H" in destruct H as [H' H]; try rewrite H' in *; try rewrite <- H' in *
  | [?a] = ?l2 ++ [?b] => apply app_tl_inversion in H; let H' := fresh "H" in destruct H as [H' H]; try rewrite H' in *; try rewrite <- H' in *
  | ?l2 ++ [?b] = [?a] => symmetry in H; apply app_tl_inversion in H; let H' := fresh "H" in destruct H as [H' H]; try rewrite H' in *; try rewrite <- H' in *
  | _ => idtac
         end.

Ltac inv_app_hd_tl_arg H :=
  list_assoc_r_single_arg H;
  inv_app_hd_arg H;
  list_assoc_l'_arg H;
  inv_app_tl_arg H;
  list_assoc_r_single_arg H;
  clear_useless.

(* Any equality between lists that have singletons as heads or tails -> destruct into respective smaller equalities. *)
Ltac inv_app_hd_tl :=
  repeat match goal with
  | [ H : ?l1 = ?l2 |- _ ] => inv_app_hd_tl_arg H
  end.

Ltac tac_cons_singleton_eq_hyp :=
  repeat match goal with
         | [ H : (?l1 : list ?T) = ?l2 |- _ ] => tac_cons_singleton_hyp H;
                                                   list_assoc_r_single_arg H
         end.


(* A version of app_eq_appT2_nn to rule out overlap between the two branchs where m = [] (hence No Nil mnemonic). *)
Lemma app_eq_appT2_nn: forall (A : Type) (w x y z : list A),
  w ++ x = y ++ z -> existsT2 (m : list A),
    ((w = y ++ m) * (z = m ++ x) * (m <> [])) + ((y = w ++ m) * (x = m ++ z)).
Proof.
  induction w; intros *; intros H; simpl in *.
  subst. exists y. right. tauto.
  apply cons_eq_appT2 in H. destruct H as [[H1 H2]| [l [? H3]]]; subst.
  exists (a :: w). left. simpl. split. split ; try auto. intro. inversion H.
  eapply IHw in H3. destruct H3 as [l2 [[H3 H4] | [H3 H4]]]; subst.
  exists l2. sD. subst. left. tauto.
  exists l2. right. tauto.
Qed.

Ltac app_eq_app_dest_arg H :=
  eapply app_eq_appT2_nn in H; sD; subst.

Ltac app_single_eq_dest_arg H :=
  apply unit_eq_appT2 in H; sD; subst.

Lemma app_eq_appT2_single_hdL : forall (A : Type) (x y z : list A) w,
    [w] ++ x = y ++ z ->
    (existsT2 m : list A,  ((y = [w] ++ m) * (x = m ++ z)))
       + ((y = []) * (z = [w] ++ x)).
Proof.
  intros *.
  intros H.
  destruct y. simpl in *.  subst.
  right. firstorder.
  left. simpl in *. inversion H.
  subst. exists y. firstorder.
Qed.

Lemma app_eq_appT2_single_hdR : forall (A : Type) (x z w : list A) y,
    w ++ x = [y] ++ z ->
    (existsT2 m : list A, (w = [y] ++ m) * (z = m ++ x)) +
    ( (w = []) * (x = [y] ++ z)).
Proof.
  intros *.
  intros H.
  symmetry in H.
  eapply app_eq_appT2_single_hdL.
  assumption.
Qed.

Lemma app_eq_appT2_single_tlL : forall (A : Type) (x y z : list A) w,
    x ++ [w] = y ++ z ->
    (existsT2 m : list A,  ((z = m ++ [w]) * (x = y ++ m)))
       + ((z = []) * (y = x ++ [w])).
Proof.
  intros *.
  intros H.
  destruct (list_nil_or_tail_singleton z). subst.
 rewrite app_nil_r in H. subst.
  right. firstorder. sD. subst.
  left. list_assoc_l'_arg H.
  eapply tail_inv_singleton in H.
  sD. subst.
  eexists. firstorder.
Qed.

Lemma app_eq_appT2_single_tlR : forall (A : Type) (x y z : list A) w,
     y ++ z = x ++ [w] ->
    (existsT2 m : list A,  ((z = m ++ [w]) * (x = y ++ m)))
       + ((z = []) * (y = x ++ [w])).
Proof.
  intros *.
  intros H.
  symmetry in H.
  eapply app_eq_appT2_single_tlL.
  assumption.
Qed.

(* Where we have a partitioning of lists, split into cases.  *)
Ltac app_eq_app_dest :=
  repeat match goal with
         | [ H : [?a] = ?l1 ++ ?l2 |- _ ] => app_single_eq_dest_arg H
         | [ H : ?l1 ++ ?l2 = [?a] |- _ ] => symmetry in H; app_single_eq_dest_arg H
         | [ H : [?a] = [?b] |- _ ] => inversion H
         | [ H : ?l1 ++ ?l2 = ?l3 ++ ?l4 |- _ ] => app_eq_app_dest_arg H
         end.

Ltac inv_app_hd_tl_full :=
  inv_app_hd_tl; repeat inversion_pair;
  tac_cons_singleton_eq_hyp.

Ltac app_eq_app_dest2 :=
  repeat (inv_app_hd_tl_full ; subst ; try match goal with
         | [ H : [?a] = ?l1 ++ ?l2 |- _ ] => app_single_eq_dest_arg H
         | [ H : ?l1 ++ ?l2 = [?a] |- _ ] => symmetry in H; app_single_eq_dest_arg H
         | [ H : [?a] = [?b] |- _ ] => inversion H
         | [ H : [?a] ++ ?l2 = ?l3 ++ ?l4 |- _ ] => eapply app_eq_appT2_single_hdL in H
         | [ H : ?l1 ++ ?l2 = [?a] ++ ?l4 |- _ ] => eapply app_eq_appT2_single_hdR in H
         | [ H : ?l1 ++ ?l2 = ?l3 ++ ?l4 |- _ ] => app_eq_app_dest_arg H
                                           end).

Ltac app_eq_app_dest3_arg_pre H :=
      (match goal with
      | H:[?a] = ?l1 ++ ?l2 |- _ => app_single_eq_dest_arg H
      | H:?l1 ++ ?l2 = [?a] |- _ => symmetry in H; app_single_eq_dest_arg H
      | H:[?a] = [?b] |- _ => inversion H; clear H
       end).

Ltac app_eq_app_dest3_argL H :=
      (match goal with
      | H:[?a] ++ ?l2 = ?l3 ++ ?l4 |- _ => eapply app_eq_appT2_single_hdL in H
      | H:?l1 ++ ?l2 = [?a] ++ ?l4 |- _ => eapply app_eq_appT2_single_hdR in H
       end).

Ltac app_eq_app_dest3_argR H :=
      (match goal with
      | H: ?l2 ++ [?a] = ?l3 ++ ?l4 |- _ => eapply app_eq_appT2_single_tlL in H
      | H:?l1 ++ ?l2 = ?l4 ++ [?a] |- _ => eapply app_eq_appT2_single_tlR in H
       end).

Ltac app_eq_app_dest3_arg_app H :=
      (match goal with
      | H:?l1 ++ ?l2 = ?l3 ++ ?l4 |- _ => app_eq_app_dest_arg H
       end).

Ltac app_eq_app_dest3_arg H :=
  (progress app_eq_app_dest3_arg_pre H) ||
  (progress (list_assoc_r_single_arg H; app_eq_app_dest3_argL H)) ||
  (progress (list_assoc_l'_arg H; app_eq_app_dest3_argR H)) ||
  (progress (list_assoc_r_single_arg H; app_eq_app_dest3_arg_app H)).

Ltac app_eq_app_dest3 :=
  repeat (inv_app_hd_tl_full ; subst ; match goal with
  | [H : (?l1 : list ?T) = ?l2 |- _ ] => app_eq_app_dest3_arg H; sD; subst
          end); try (inv_app_hd_tl_full ; subst).

Ltac app_eq_app_dest3' :=
  repeat ((inv_app_hd_tl_full ; subst ; match goal with
  | [H : (?l1 : list ?T) = ?l2 |- _ ] => app_eq_app_dest3_arg H; sD; subst
          end); try (inv_app_hd_tl_full ; subst)).




Ltac eapply_refl tac := eapply tac; reflexivity.


Ltac assoc_mid_loc L :=
  repeat match goal with
         | [ |- context[ ?l1 ++ ?l2 ++ L ++ ?l3 ] ] => rewrite (app_assoc l1)
         end.

Ltac tac_match l1 l2 :=
  match l1 with
  | [] => fail
  | l2 ++ ?s1 => idtac
  | ?s1 ++ l2 => try rewrite <- (app_nil_r ?L1)
  | ?s1 ++ l2 ++ ?s2 => try rewrite (app_assoc _ s1)
  | ?s1 ++ ?s2 => try rewrite (app_assoc _ s1); tac_match s2 l2
  end. 

      Ltac tac_match' l1 AA :=
  match l1 with
  | [] => fail
  | AA :: ?s1 => idtac
  | ?s1 ++ [AA] => try rewrite <- (app_nil_r ?L1)
  | ?s1 ++ AA :: ?s2 => try rewrite (app_assoc _ s1)
  | ?s1 ++ ?s2 => try rewrite (app_assoc _ s1); tac_match' s2 AA
  end.

      
      Ltac get_last_app H :=
  match H with
  | ?H1 ++ ?H2 => get_last_app H2
  | _ => constr:(H)
  end.

Ltac get_snd_last_app H :=
  match H with
  | ?H1 ++ ?H2 ++ ?H3 => get_snd_last_app (H2 ++ H3)
  | ?H1 ++ ?H2 => constr:(H1)
  | _ => constr:(H)
  end.

(* end git conflict 1 *)

(* begin git conflict 2 *)

(* for manipulating lists got by appending shorter lists *)
Inductive app_split_at X (T : list X) : list X -> list X -> list X -> Type :=
  | asa_single : app_split_at T T [] []
  | asa_appL : forall A B C D, 
    app_split_at T A B C -> app_split_at T (A ++ D) B (C ++ D)
  | asa_appR : forall A B C D, 
    app_split_at T A B C -> app_split_at T (D ++ A) (D ++ B) C
  .

(* to show/solve app_split_at T A ?BC *)
Ltac solve_asa := apply asa_single || 
  (apply asa_appL ; solve_asa) || 
  (apply asa_appR ; solve_asa) .

Lemma asa_eq X (T A B C : list X) : app_split_at T A B C -> A = B ++ T ++ C.
Proof. intro asa. induction asa ; subst.
rewrite app_nil_r. reflexivity. list_eq_assoc. list_eq_assoc. Qed.


(* end git conflict 2 *)