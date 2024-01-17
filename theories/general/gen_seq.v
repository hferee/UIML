

Require Export List.
Export ListNotations.
Set Implicit Arguments.

From Coq Require Import ssreflect.

(* Add LoadPath "../modal".
Add LoadPath "../tense-lns". *)
Require Import gen genT ddT gen_tacs.
Require Import gstep.
Require Import List_lemmasT swappedT existsT.
Require Import Coq.Program.Basics.

Inductive rlsmap U W (f : U -> W) (rls : rlsT U) : rlsT W :=
  | rmI : forall ps c, rls ps c -> rlsmap f rls (map f ps) (f c).

Lemma rmI_eq U W (f : U -> W) (rls : rlsT U) ps c mps mc :
  rls ps c -> mps = map f ps -> mc = f c -> rlsmap f rls mps mc.
Proof. intros. subst. apply rmI ; assumption. Qed.

Inductive relmap U W (f : U -> W) (rel : relationT U) : relationT W :=
  | rlI : forall p c, rel p c -> relmap f rel (f p) (f c).

Lemma rlI_eq U W (f : U -> W) (rel : relationT U) p c mp mc :
  rel p c -> mp = f p -> mc = f c -> relmap f rel mp mc.
Proof. intros. subst. apply rlI ; assumption. Qed.

(** seqext, seqrule, extending sequent and rule with left- and right-contexts
  in antecedent and consequent **)
Definition seqext (W : Type) Gam1 Gam2 Delt1 Delt2 (seq : rel (list W)) :=
  match seq with | pair U V => pair (Gam1 ++ U ++ Gam2) (Delt1 ++ V ++ Delt2) end.

Lemma seqext_seqext: forall V (Gam1 Gam2 Delt1 Delt2 Phi1 Phi2 Psi1 Psi2 : list V) seq,
  seqext Gam1 Gam2 Delt1 Delt2 (seqext Phi1 Phi2 Psi1 Psi2 seq) =
  seqext (Gam1 ++ Phi1) (Phi2 ++ Gam2) (Delt1 ++ Psi1) (Psi2 ++ Delt2) seq.
Proof. intros. unfold seqext. destruct seq.
rewrite !app_assoc. reflexivity. Qed.  

Lemma map_seqext_seqext: forall V (Gam1 Gam2 Delt1 Delt2 Phi1 Phi2 Psi1 Psi2 : list V) seqs,
  map (seqext Gam1 Gam2 Delt1 Delt2) (map (seqext Phi1 Phi2 Psi1 Psi2) seqs) =
  map (seqext (Gam1 ++ Phi1) (Phi2 ++ Gam2) (Delt1 ++ Psi1) (Psi2 ++ Delt2)) seqs.
Proof. induction seqs. tauto. 
simpl. rewrite IHseqs. rewrite seqext_seqext. reflexivity. Qed.  

Inductive seqrule (W : Type) (pr : rlsT (rel (list W))) : 
    rlsT (rel (list W)) := 
  | Sctxt : forall ps c Phi1 Phi2 Psi1 Psi2, pr ps c -> 
    seqrule pr (map (seqext Phi1 Phi2 Psi1 Psi2) ps) (seqext Phi1 Phi2 Psi1 Psi2 c).

Lemma seqext_def : forall (W : Type) Phi1 Phi2 Psi1 Psi2 U V,
      @seqext W Phi1 Phi2 Psi1 Psi2 (U,V) = (Phi1 ++ U ++ Phi2, Psi1 ++ V ++ Psi2).
Proof. reflexivity. Qed.

Lemma Sctxt_e: forall (W : Type) (pr : rlsT (rel (list W))) ps U V Phi1 Phi2 Psi1 Psi2,
  pr ps (U, V) ->
  seqrule pr (map (seqext Phi1 Phi2 Psi1 Psi2) ps) (Phi1 ++ U ++ Phi2, Psi1 ++ V ++ Psi2).
Proof.
  intros until 0. intros H. rewrite <- seqext_def.
  apply Sctxt. exact H.
Qed.

Lemma Sctxt_eq: forall (W : Type) pr ps mps (ca cs U V Phi1 Phi2 Psi1 Psi2 : list W),
  pr ps (U, V) -> ca = Phi1 ++ U ++ Phi2 -> cs = Psi1 ++ V ++ Psi2 ->
  mps = map (seqext Phi1 Phi2 Psi1 Psi2) ps -> seqrule pr mps (ca, cs).
Proof. intros.  subst. apply Sctxt_e. exact X. Qed.  

Lemma seqrule_id (W : Type) (pr : rlsT (rel (list W))) :
  forall ps c, pr ps c -> seqrule pr ps c.
Proof. intros. destruct c as [ca cs].
apply (Sctxt_eq pr ps ca cs [] [] [] []). assumption.
simpl. rewrite app_nil_r.  reflexivity.
simpl. rewrite app_nil_r.  reflexivity.
clear X. induction ps.  simpl.  reflexivity.
simpl. rewrite <- IHps.
destruct a. unfold seqext. simpl.  rewrite !app_nil_r.
reflexivity. Qed.

Lemma seqrule_seqrule (W : Type) (pr : rlsT (rel (list W))) :
  rsub (seqrule (seqrule pr)) (seqrule pr).
Proof. unfold rsub. intros. inversion X. subst. clear X. 
inversion X0.  subst. clear X0.
rewrite seqext_seqext.
destruct c0 as [ca cs].
eapply Sctxt_eq. exact X. 
reflexivity.  reflexivity.
clear X. induction ps0.  simpl.  reflexivity.
simpl. rewrite IHps0.  rewrite seqext_seqext. reflexivity. Qed.

Definition seqrule_seqrule' (W : Type) pr :=
  rsubD (@seqrule_seqrule W pr).
 
Lemma derl_seqrule'' (W : Type) (rules : rlsT (rel (list W))) :
  forall Phi1 Phi2 Psi1 Psi2, (forall ps c, derl rules ps c -> 
   derl (seqrule rules) (map (seqext Phi1 Phi2 Psi1 Psi2) ps) (seqext Phi1 Phi2 Psi1 Psi2 c)) * 
  (forall ps cs, dersl rules ps cs -> 
    dersl (seqrule rules) (map (seqext Phi1 Phi2 Psi1 Psi2) ps) 
    (map (seqext Phi1 Phi2 Psi1 Psi2)cs)).
Proof. intros Phi1 Phi2 Psi1 Psi2.
eapply (derl_dersl_rect_mut (rules := rules)
  (fun ps c => fun _ => derl (seqrule rules)
    (map (seqext Phi1 Phi2 Psi1 Psi2) ps) (seqext Phi1 Phi2 Psi1 Psi2 c))
  (fun ps cs : list _ => fun _ => dersl (seqrule rules)
    (map (seqext Phi1 Phi2 Psi1 Psi2) ps) (map (seqext Phi1 Phi2 Psi1 Psi2) cs))).
- simpl. intros. apply asmI.
- intros. eapply dtderI.  apply Sctxt. eassumption.  assumption. 
- simpl. apply dtNil.
- intros. rewrite map_app. simpl. apply dtCons ; assumption. Qed.
 
Definition derl_seqrule' W rules Phi1 Phi2 Psi1 Psi2 := 
  fst (@derl_seqrule'' W rules Phi1 Phi2 Psi1 Psi2).
Definition dersl_seqrule' W rules Phi1 Phi2 Psi1 Psi2 := 
  snd (@derl_seqrule'' W rules Phi1 Phi2 Psi1 Psi2).
 
Lemma derl_seqrule (W : Type) (rules : rlsT (rel (list W))) :
  rsub (seqrule (derl rules)) (derl (seqrule rules)).
Proof.  unfold rsub.  intros.  destruct X.  
apply derl_seqrule'. assumption. Qed.

Lemma seqrule_derl_seqrule (W : Type) (rules : rlsT (rel (list W))) :
  rsub (seqrule (derl (seqrule rules))) (derl (seqrule rules)).
Proof.  eapply rsub_trans. apply derl_seqrule.
 unfold rsub.  intros.  eapply derl_mono. 2: eassumption.
 apply seqrule_seqrule. Qed.

Definition seqrule_derl_seqrule' W rules :=
  rsubD (@seqrule_derl_seqrule W rules).

(* seqrule_s ps c qs d means that d is a sequent extension of c 
  and that each q in qs is a corresponding sequent extension of the
  corresponding p in ps *)
Inductive seqrule_s (W : Type) (ps : list (rel (list W))) (c : rel (list W)) : 
    rlsT (rel (list W)) := 
  | Sctxt_s : forall Phi1 Phi2 Psi1 Psi2, 
    seqrule_s ps c (map (seqext Phi1 Phi2 Psi1 Psi2) ps) (seqext Phi1 Phi2 Psi1 Psi2 c).

Inductive seqrule' (W : Type) (pr : rlsT (rel (list W))) : 
    rlsT (rel (list W)) := 
  | Sctxt' : forall ps c pse ce,
    pr ps c -> seqrule_s ps c pse ce -> seqrule' pr pse ce.

Check (Sctxt' _ _ (Sctxt_s _ _ _ _ _ _)). 

(* Check, get same as Sctxt but for seqrule' *)
Lemma Sctxt_alt : forall (W : Type) (pr : rlsT (rel (list W))) ps c Phi1 Phi2 Psi1 Psi2,
    pr ps c -> seqrule' pr (map (seqext Phi1 Phi2 Psi1 Psi2) ps) (seqext Phi1 Phi2 Psi1 Psi2 c).
Proof.
  intros until 0. intros H.
  eapply Sctxt'. exact H. apply Sctxt_s.
Qed.

Lemma Sctxt_e': forall (W : Type) (pr : rlsT (rel (list W))) ps U V Phi1 Phi2 Psi1 Psi2,
  pr ps (U, V) ->
  seqrule pr (map (seqext Phi1 Phi2 Psi1 Psi2) ps) ((Phi1 ++ U) ++ Phi2, Psi1 ++ V ++ Psi2).
Proof.
  intros until 0. intros H.
  rewrite <- app_assoc. apply Sctxt_e. exact H.
Qed.  

Lemma seqext_defp : forall (W : Type) Phi1 Phi2 Psi1 Psi2 seq,
      @seqext W Phi1 Phi2 Psi1 Psi2 seq =
        let (U, V) := seq in (Phi1 ++ U ++ Phi2, Psi1 ++ V ++ Psi2).
Proof. reflexivity. Qed.

Lemma seqrule_same: forall (W : Type) pr ps (c c' : rel (list W)),
  seqrule pr ps c -> c = c' -> seqrule pr ps c'.
Proof. intros. subst. assumption. Qed.  

Lemma seqrule_mono X (rulesa rulesb : rlsT (rel (list X))) :
  rsub rulesa rulesb -> rsub (seqrule rulesa) (seqrule rulesb).
Proof. unfold rsub. intros. destruct X1. apply Sctxt. firstorder. Qed.

Definition seqrule_mono' X rulesa rulesb rs :=
  rsubD (@seqrule_mono X rulesa rulesb rs).

Lemma Sctxt_nil: forall (W : Type) pr c Gam1 Gam2 Delt1 Delt2, (pr [] c : Type) ->
  @seqrule W pr [] (seqext Gam1 Gam2 Delt1 Delt2 c).
Proof.
  intros until 0.  intros H. eapply Sctxt in H.
  simpl in H. exact H.
Qed.

Lemma InT_seqextL : forall {W : Type} Gam Delt A,
    InT A Gam ->
    existsT2 Phi1 Phi2, @seqext W Phi1 Phi2 Delt [] ([A], []) = (Gam, Delt).
Proof.
  induction Gam; intros Delt A Hin.
  inversion Hin.
  inversion Hin. subst.
  repeat eexists. unfold seqext.
  do 2 rewrite app_nil_r. erewrite app_nil_l.
     reflexivity.
  subst. destruct (IHGam  Delt _ X) as [H1 [H2 H3]].
  unfold seqext in *.
  inversion H3.
  repeat rewrite app_nil_r.
  repeat eexists. rewrite app_comm_cons. reflexivity.
Qed.

Lemma InT_seqextR : forall {W : Type} Gam Delt B,
    InT B Delt ->
    existsT2 Psi1 Psi2, @seqext W Gam [] Psi1 Psi2 ([], [B]) = (Gam, Delt).
Proof.
  induction Delt; intros A Hin.
  inversion Hin.
  inversion Hin. subst.
  repeat eexists. unfold seqext.
  do 2 rewrite app_nil_r. erewrite app_nil_l.
     reflexivity.
  subst. destruct (IHDelt _ X) as [H1 [H2 H3]].
  unfold seqext in *.
  inversion H3.
  repeat rewrite app_nil_r.
  repeat eexists. rewrite app_comm_cons. reflexivity.
Qed.

Lemma InT_seqext : forall {W : Type} Gam Delt A B,
    InT A Gam ->
    InT B Delt ->
    existsT2 Phi1 Phi2 Psi1 Psi2, @seqext W Phi1 Phi2 Psi1 Psi2 ([A], [B]) = (Gam, Delt).
Proof.
  intros until 0. intros Hin1 Hin2.
  destruct (@InT_seqextL _ _ Delt _ Hin1) as [H1 [H2 H3]].
  destruct (@InT_seqextR _ Gam _ _ Hin2) as [J1 [J2 J3]].
  unfold seqext in *.
  repeat rewrite app_nil_r in H3.
  repeat rewrite app_nil_r in J3.
  inversion H3. inversion J3.
  subst. repeat eexists.
Qed.

(* fmlsext copied from ../ll/fmlsext.v *)
Definition fmlsext (W : Type) Gam1 Gam2 (fmls : (list W)) := (Gam1 ++ fmls ++ Gam2).

Lemma fmlsext_fmlsext: forall V (Gam1 Gam2 Phi1 Phi2 : list V) seq,
  fmlsext Gam1 Gam2 (fmlsext Phi1 Phi2 seq) = fmlsext (Gam1 ++ Phi1) (Phi2 ++ Gam2) seq.
Proof. intros. unfold fmlsext.  rewrite !app_assoc. reflexivity. Qed.

Lemma map_fmlsext_fmlsext: forall V (Gam1 Gam2 Phi1 Phi2 : list V) seqs,
  map (fmlsext Gam1 Gam2) (map (fmlsext Phi1 Phi2) seqs) =
  map (fmlsext (Gam1 ++ Phi1) (Phi2 ++ Gam2)) seqs.
Proof. induction seqs. tauto.
simpl. rewrite IHseqs. rewrite fmlsext_fmlsext. reflexivity. Qed.

Lemma fmlsext_def : forall (W : Type) Phi1 Phi2 U,
      @fmlsext W Phi1 Phi2 U = (Phi1 ++ U ++ Phi2).
Proof. reflexivity. Qed.

Definition apfst U V W (f : U -> V) (p : U * W) := let (x, y) := p in (f x, y).
Definition apsnd U V W (f : U -> V) (p : W * U) := let (x, y) := p in (x, f y).

(** fst_ext_rls - adding left- and right-context 
  to the antecedent of a sequent rule *)
Inductive fst_ext_rls U W rls : rlsT (list U * W) :=
  | fextI : forall Gam1 Gam2 ps c, 
    rlsmap (apfst (fmlsext Gam1 Gam2)) rls ps c -> fst_ext_rls rls ps c.

Inductive snd_ext_rls U W rls : rlsT (U * list W) :=
  | sextI : forall Gam1 Gam2 ps c, 
    rlsmap (apsnd (fmlsext Gam1 Gam2)) rls ps c -> snd_ext_rls rls ps c.

Definition fextI' U W rls Gam1 Gam2 ps c rpc :=
  @fextI U W rls Gam1 Gam2 _ _ (rmI _ _ ps c rpc).

Lemma fextI_eq' U W rls Gam1 Gam2 ps (c : list U * W) mps mc :
  rls ps c -> mps = map (apfst (fmlsext Gam1 Gam2)) ps ->
  mc = apfst (fmlsext Gam1 Gam2) c -> fst_ext_rls rls mps mc.
Proof. intros. subst. apply fextI'. exact X. Qed.

Definition fextI_eqc' U W rls Gam1 Gam2 ps (c : list U * W) mc rpc :=
  @fextI_eq' U W rls Gam1 Gam2 ps (c : list U * W) _ mc rpc eq_refl.

Lemma fst_snd_ext W (rls : rlsT (list W * list W)) :
  req (seqrule rls) (fst_ext_rls (snd_ext_rls rls)).
Proof. split ; intros ps c.
- intro sr. destruct sr. eapply fextI. eapply rmI_eq.
eapply sextI. apply rmI. exact r.
2: destruct c.  2: simpl.  2: unfold fmlsext.  2: reflexivity.
clear r. induction ps. reflexivity.
destruct a. simpl.  rewrite - IHps. unfold fmlsext. reflexivity.
- intro fs. destruct fs. inversion r. clear r. subst.
destruct X. inversion r. clear r. subst.
destruct c0. simpl. unfold fmlsext.
eapply Sctxt_eq. exact X. reflexivity. reflexivity.
clear X.  induction ps0. reflexivity.
destruct a. simpl.  rewrite IHps0. reflexivity. Qed.

Lemma snd_fst_ext W (rls : rlsT (list W * list W)) :
  req (seqrule rls) (snd_ext_rls (fst_ext_rls rls)).
Proof. split ; intros ps c.
- intro sr. destruct sr. eapply sextI. eapply rmI_eq.
eapply fextI. apply rmI. exact r.
2: destruct c.  2: simpl.  2: unfold fmlsext.  2: reflexivity.
clear r. induction ps. reflexivity.
destruct a. simpl.  rewrite - IHps. unfold fmlsext. reflexivity.
- intro fs. destruct fs. inversion r. clear r. subst.
destruct X. inversion r. clear r. subst.
destruct c0. simpl. unfold fmlsext.
eapply Sctxt_eq. exact X. reflexivity. reflexivity.
clear X.  induction ps0. reflexivity.
destruct a. simpl.  rewrite IHps0. reflexivity. Qed.

Lemma rm_mono U W (f : U -> W) rlsa rlsb : 
  rsub rlsa rlsb -> rsub (rlsmap f rlsa) (rlsmap f rlsb).
Proof. intros rab ps c ra.
destruct ra.   pose (rab _ _ r).
apply rmI. apply r0. Qed.

Lemma fer_mono U W (rlsa rlsb : rlsT (list U * W)) :
  rsub rlsa rlsb -> rsub (fst_ext_rls rlsa) (fst_ext_rls rlsb).
Proof. intros rab ps c fea.
destruct fea.  destruct r.  pose (rab _ _ r).
eapply fextI. apply rmI. apply r0. Qed.
  
Lemma ser_mono U W (rlsa rlsb : rlsT (U * list W)) :
  rsub rlsa rlsb -> rsub (snd_ext_rls rlsa) (snd_ext_rls rlsb).
Proof. intros rab ps c sea.
destruct sea.  destruct r.  pose (rab _ _ r).
eapply sextI. apply rmI. apply r0. Qed.
  
(* derl_fst_ext_rls - similar for seqrule above *)
Lemma fst_ext_rls_fst_ext_rls (U W : Type) (pr : rlsT (list U * W)) :
  rsub (fst_ext_rls (fst_ext_rls pr)) (fst_ext_rls pr).
Proof. unfold rsub. intros. inversion X. subst. clear X. 
inversion X0.  subst. clear X0. destruct X. destruct r.
destruct c. simpl.  rewrite fmlsext_fmlsext.
eapply fextI' in p.  simpl in p.
eapply arg1_cong_imp. 2: exact p.  clear p.
induction ps ; simpl. reflexivity.
rewrite IHps.  destruct a. simpl. rewrite fmlsext_fmlsext. reflexivity. Qed.

Definition fst_ext_rls_fst_ext_rls' (U W : Type) pr :=
  rsubD (@fst_ext_rls_fst_ext_rls U W pr).
 
Lemma derl_fst_ext_rls'' (U W : Type) (rules : rlsT (list U * W)) :
  forall Phi1 Phi2, (forall ps c, derl rules ps c -> 
   derl (fst_ext_rls rules) 
     (map (apfst (fmlsext Phi1 Phi2)) ps) (apfst (fmlsext Phi1 Phi2) c)) * 
  (forall ps cs, dersl rules ps cs -> 
    dersl (fst_ext_rls rules) (map (apfst (fmlsext Phi1 Phi2)) ps) 
    (map (apfst (fmlsext Phi1 Phi2)) cs)).
Proof. intros Phi1 Phi2.
eapply (derl_dersl_rect_mut (rules := rules)
  (fun ps c => fun _ => derl (fst_ext_rls rules)
    (map (apfst (fmlsext Phi1 Phi2)) ps) (apfst (fmlsext Phi1 Phi2) c))
  (fun ps cs : list _ => fun _ => dersl (fst_ext_rls rules)
    (map (apfst (fmlsext Phi1 Phi2)) ps) (map (apfst (fmlsext Phi1 Phi2)) cs))).
- simpl. intros. apply asmI.
- intros. eapply dtderI. eapply fextI. apply rmI. eassumption.  assumption. 
- simpl. apply dtNil.
- intros. rewrite map_app. simpl. apply dtCons ; assumption. Qed.
 
Definition derl_fst_ext_rls' U W rules Phi1 Phi2 := 
  fst (@derl_fst_ext_rls'' U W rules Phi1 Phi2).
Definition dersl_fst_ext_rls' U W rules Phi1 Phi2 := 
  snd (@derl_fst_ext_rls'' U W rules Phi1 Phi2).
 
Lemma derl_fst_ext_rls (U W : Type) (rules : rlsT (list U * W)) :
  rsub (fst_ext_rls (derl rules)) (derl (fst_ext_rls rules)).
Proof.  unfold rsub.  intros.  destruct X.  destruct r.
apply derl_fst_ext_rls'. assumption. Qed.

Lemma fst_ext_rls_derl_fst_ext_rls (U W : Type) (rules : rlsT (list U * W)) :
  rsub (fst_ext_rls (derl (fst_ext_rls rules))) (derl (fst_ext_rls rules)).
Proof.  eapply rsub_trans. apply derl_fst_ext_rls.
 unfold rsub.  intros.  eapply derl_mono. 2: eassumption.
 apply fst_ext_rls_fst_ext_rls. Qed.

Definition fst_ext_rls_derl_fst_ext_rls' U W rules :=
  rsubD (@fst_ext_rls_derl_fst_ext_rls U W rules).

(* simple version of weakening, new stuff added at beginning or end,
  could do more complicated, but why bother, have exchange *)
Definition wkL_valid V W rules (cl : list V) cr :=
  forall Gam1 Gam2, derrec rules (@emptyT _) (fmlsext Gam1 Gam2 cl, cr : W).
Definition wkL_valid' V W rules seq := @wkL_valid V W rules (fst seq) (snd seq).

Definition can_wkL V W rules seq :=
  derrec rules emptyT seq -> @wkL_valid' V W rules seq.

Lemma can_wkL_req V W rlsa rlsb seq : req rlsa rlsb ->
  @can_wkL V W rlsa seq -> can_wkL rlsb seq.
Proof. unfold can_wkL. unfold wkL_valid'. unfold wkL_valid.
intros rab da derb *.
specialize (da (derrec_rmono (snd rab) derb)).
exact (derrec_rmono (fst rab) (da Gam1 Gam2)). Qed.

Lemma weakeningL: forall V W seq rules, @can_wkL V W (fst_ext_rls rules) seq.
Proof. unfold can_wkL. intros.
eapply derrec_all_rect in X. exact X.
intros. contradiction H.
intros ps concl ljpc dsps fwk.  destruct ljpc.  inversion r.
destruct c0. unfold wkL_valid'. unfold wkL_valid. simpl. subst. clear r.
intros *.  rewrite fmlsext_fmlsext.
eapply derI. eapply fextI. eapply rmI_eq. apply X0.
reflexivity.  reflexivity.
apply dersrecI_forall. intros c0 incm.
apply InT_mapE in incm. cD.
eapply ForallTD_forall in fwk.
2: apply InT_map.  2: exact incm1.
simpl in incm0. destruct incm0. simpl in fwk.
unfold wkL_valid' in fwk.  unfold wkL_valid in fwk.  simpl in fwk.
rewrite - fmlsext_fmlsext. apply fwk.  Qed.

Print Implicit weakeningL.

(** exchange **)
(* properties can exchange adjacent sublists, and resulting sequent
  is derivable (not conditional on unexchanged version being derivable *)
Definition can_exchL W Y rules seq :=
  forall (Gam Gams : list W) (Delt : Y), seq = pair Gam Delt -> swapped Gam Gams ->
  derrec rules (@emptyT _) (pair Gams Delt).

Definition can_exchR W Y rules seq :=
  forall (Gam : Y) (Delt Delts : list W), seq = pair Gam Delt -> swapped Delt Delts ->
  derrec rules (@emptyT _) (pair Gam Delts).

Inductive sing_empty X : list X -> Type :=
  | se_empty : sing_empty []
  | se_single : forall a, sing_empty [a].

Lemma sing_empty_app X (xs ys : list X):
  sing_empty (xs ++ ys) -> sum (xs = []) (ys = []).
Proof. intro. inversion X0. destruct xs. tauto.
simpl in H0. discriminate H0.
destruct xs. tauto.
injection H0 as. destruct xs. simpl in H0. subst. tauto.
simpl in H0. discriminate H0.  Qed.

Lemma sing_empty_app_cons X z (xs ys : list X):
  sing_empty (xs ++ z :: ys) -> (xs = []) * (ys = []).
Proof. intro se. inversion se.
list_eq_ncT. inversion H0.  list_eq_ncT. sD. inversion H1. tauto.
list_eq_ncT. Qed.

Inductive fst_rel (A B : Type) (R : relationT A) : relationT (A * B) :=
  fst_relI : forall x y z, R x y -> @fst_rel A B R (x, z : B) (y, z).

Inductive snd_rel (A B : Type) (R : relationT A) : relationT (B * A) :=
  snd_relI : forall x y z, R x y -> @snd_rel A B R (z : B, x) (z, y).

Lemma fext_e: forall (U W : Type) (pr : rlsT (list U * W)) ps cl cr Phi1 Phi2,
  pr ps (cl, cr) ->
  fst_ext_rls pr (map (apfst (fmlsext Phi1 Phi2)) ps) (Phi1 ++ cl ++ Phi2, cr).
Proof.  intros * H. rewrite <- fmlsext_def.
  eapply fextI. eapply rmI_eq. exact H. reflexivity.  reflexivity.  Qed.

Lemma sext_e: forall (U W : Type) (pr : rlsT (U * list W)) ps cl cr Phi1 Phi2,
  pr ps (cl, cr) ->
  snd_ext_rls pr (map (apsnd (fmlsext Phi1 Phi2)) ps) (cl, Phi1 ++ cr ++ Phi2).
Proof.  intros * H. rewrite <- fmlsext_def.
  eapply sextI. eapply rmI_eq. exact H. reflexivity.  reflexivity.  Qed.

Ltac concl_in_app X0 r sea :=
  pose X0 as r ; apply sea in r ;
  destruct r ; subst ; rewrite ?app_nil_r ; rewrite ?app_nil_l ;
  simpl in X0 ; rewrite ?app_nil_r in X0.

Ltac fwl_tac mid := eexists ; split ;
  [> assoc_mid mid ; apply fext_e ; eassumption |
    apply ForallTI_forall ; intros x inms ; apply InT_mapE in inms ;
    destruct inms as [x0 p] ; destruct p as [sex int] ;
    destruct x0 ; simpl in sex ; unfold fmlsext in sex ; destruct sex ;
    eexists ; split ;
      [> eapply InT_map ; eassumption |
      simpl ; unfold fmlsext ; apply fst_relI ; swap_tac ]].

Ltac fwr_tac mid := eexists ; split ;
  [> assoc_mid mid ; apply sext_e ; eassumption |
    apply ForallTI_forall ; intros x inms ; apply InT_mapE in inms ;
    destruct inms as [x0 p] ; destruct p as [sex int] ;
    destruct x0 ; simpl in sex ; unfold fmlsext in sex ; destruct sex ;
    eexists ; split ;
      [> eapply InT_map ; eassumption |
      simpl ; unfold fmlsext ; apply snd_relI ; swap_tac ]].

Lemma exchL_std_rule: forall U W (rules : rlsT (list U * W)),
  (forall ps U S, rules ps (U, S) -> sing_empty U) ->
  forall ps c, fst_ext_rls rules ps c ->
    can_trf_rules (fst_rel (@swapped _)) (fst_ext_rls rules) ps c.
Proof. unfold can_trf_rules.
intros U W rules se ps c sqr c' fr.  
pose (fun ps xs ys S rps => 
  sing_empty_app xs ys (se ps (xs ++ ys) S rps)) as sea.
inversion fr. subst. clear fr.
inversion sqr. clear sqr. subst.
inversion X0. destruct c as [pl pr].
simpl in H1. unfold fmlsext in H1.
inversion H1. subst. clear H1. clear X0.
inversion X. subst.
acacD'T2 ; subst.
- concl_in_app X1 r sea.  + fwl_tac H3.  + fwl_tac H1.
- concl_in_app X1 r sea.  concl_in_app X1 r sea.
+ fwl_tac H5.  + fwl_tac C.
+ list_eq_nc. destruct e. subst. rewrite ?app_nil_r. rewrite ?app_nil_l.
simpl in X1. rewrite ?app_nil_r in X1.
fwl_tac H1.
- fwl_tac pl.
- concl_in_app X1 r sea.  + fwl_tac H5.  + fwl_tac H3.
- fwl_tac pl.
- fwl_tac pl.
- concl_in_app X1 r sea.  + fwl_tac H1.  + fwl_tac H.
- concl_in_app X1 r sea.  concl_in_app X1 r sea.
+ fwl_tac H3.  + fwl_tac B.
+ list_eq_ncT. destruct e. subst. rewrite ?app_nil_r. rewrite ?app_nil_l.
  simpl in X1 ; rewrite ?app_nil_r in X1.
fwl_tac H.
- concl_in_app X1 r sea.  concl_in_app X1 r sea. concl_in_app X1 r sea.
+ fwl_tac H5.  + fwl_tac C.
+ list_eq_ncT. destruct e. subst. rewrite ?app_nil_r. rewrite ?app_nil_l.
  simpl in X1 ; rewrite ?app_nil_r in X1.
fwl_tac B.
+ list_eq_nc. destruct e.  list_eq_nc. destruct H1. subst.
rewrite ?app_nil_r. rewrite ?app_nil_l.
  simpl in X1 ; rewrite ?app_nil_r in X1.
fwl_tac H.
- fwl_tac pl.
Qed.

Print Implicit exchL_std_rule.

Lemma exchR_std_rule: forall U W (rules : rlsT (U * list W)),
  (forall ps U S, rules ps (U, S) -> sing_empty S) ->
  forall ps c, snd_ext_rls rules ps c ->
    can_trf_rules (snd_rel (@swapped _)) (snd_ext_rls rules) ps c.
Proof. unfold can_trf_rules.
intros U W rules se ps c sqr c' fr.  
pose (fun ps xs ys U rps => 
  sing_empty_app xs ys (se ps U (xs ++ ys) rps)) as sea.
inversion fr. subst. clear fr.
inversion sqr. clear sqr. subst.
inversion X0. destruct c as [pl pr].
simpl in H1. unfold fmlsext in H1.
inversion H1. subst. clear H1. clear X0.
inversion X. subst.
acacD'T2 ; subst.
- concl_in_app X1 r sea.  + fwr_tac H3.  + fwr_tac H1.
- concl_in_app X1 r sea.  concl_in_app X1 r sea.
+ fwr_tac H5.  + fwr_tac C.
+ list_eq_nc. destruct e. subst. rewrite ?app_nil_r. rewrite ?app_nil_l.
simpl in X1. rewrite ?app_nil_r in X1.
fwr_tac H1.
- fwr_tac pr.
- concl_in_app X1 r sea.  + fwr_tac H5.  + fwr_tac H3.
- fwr_tac pr.
- fwr_tac pr.
- concl_in_app X1 r sea.  + fwr_tac H1.  + fwr_tac H.
- concl_in_app X1 r sea.  concl_in_app X1 r sea.
+ fwr_tac H3.  + fwr_tac B.
+ list_eq_ncT. destruct e. subst. rewrite ?app_nil_r. rewrite ?app_nil_l.
  simpl in X1 ; rewrite ?app_nil_r in X1.
fwr_tac H.
- concl_in_app X1 r sea.  concl_in_app X1 r sea. concl_in_app X1 r sea.
+ fwr_tac H5.  + fwr_tac C.
+ list_eq_ncT. destruct e. subst. rewrite ?app_nil_r. rewrite ?app_nil_l.
  simpl in X1 ; rewrite ?app_nil_r in X1.
fwr_tac B.
+ list_eq_nc. destruct e.  list_eq_nc. destruct H1. subst.
rewrite ?app_nil_r. rewrite ?app_nil_l.
  simpl in X1 ; rewrite ?app_nil_r in X1.
fwr_tac H.
- fwr_tac pr.
Qed.

Print Implicit exchR_std_rule.

Definition rev_pair {U W} (p : U * W) := let (x, y) := p in (y, x).

Lemma sext_rev_fext U W (rules : rlsT (U * list W)) ps c :
  snd_ext_rls rules ps c ->
  fst_ext_rls (rlsmap rev_pair rules) (map rev_pair ps) (rev_pair c).
Proof. intro ser. destruct ser.  inversion r. destruct c0.
clear r. subst. simpl.
eapply fextI.  eapply rmI_eq. apply rmI. exact X.
2: reflexivity.
clear X.  induction ps0. reflexivity.
simpl. rewrite IHps0.  destruct a. reflexivity. Qed.

Print Implicit sext_rev_fext.


(*
this is not going to be worthwhile without a bunch more lemmas 
such as sext_rev_fext above, and more

Lemma exchR_std_rule: forall U W (rules : rlsT (U * list W)),
  (forall ps U S, rules ps (U, S) -> sing_empty S) ->
  forall ps c, snd_ext_rls rules ps c ->
    can_trf_rules (snd_rel (@swapped _)) (snd_ext_rls rules) ps c.
Proof. intros * se * ser.
pose (rlsmap rev_pair rules) as rrules.
pose (@exchL_std_rule _ _ rrules).
require c0.
{ intros * rr.  inversion rr. destruct c1. simpl in H1. inversion H1. subst.
eapply se. subst rrules. exact X. }
specialize (c0 (map rev_pair ps) (rev_pair c)).
require c0.  { subst rrules. exact (sext_rev_fext ser). }

destruct ser.
eapply fextI. inversion r.

*)

(* we may also want to refer to rules individually *)
Inductive Idrule (W : Type) : rlsT (rel (list W)) :=
  | Idrule_I : forall A, Idrule [] (pair [A] [A]).

Lemma sr_Id_alt X (A : X) ant suc: InT A ant -> InT A suc ->
  seqrule (@Idrule X) [] (ant, suc).
Proof. intros. apply InT_split in X1.
apply InT_split in X0. cD. subst. 
eapply Sctxt_eq. apply (Idrule_I A).
simpl. reflexivity.  simpl. reflexivity.  simpl. reflexivity. Qed.

