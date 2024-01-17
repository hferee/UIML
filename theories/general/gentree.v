
(* constructions for inductive proofs about derivations,
  adapted from ~jeremy/isabelle/2005/seqms/gentree.{thy,ML} *)

Set Implicit Arguments.
Require Import Coq.Program.Equality. (* for dependent induction/destruction *)
Require Import PeanoNat. (* for Nat *)

Require Import gen.
Require Import genT.
Require Import ddT.
Require Import dd_fc.
Require Import rtcT.

Require Import gstep.

(** conditions for inductive proofs for a tree **)

Definition gen_step_tr W rules fty P (A : fty) sub 
  (dt : @derrec_fc W rules emptyT) :=
  (forall A' : fty, sub A' A -> forall d, P A' d) ->
  (forall dtn, in_nextup_fc dtn dt -> P A dtn) -> P A dt.
  
(* here is the same thing based the conclusion of the tree *)
Definition gen_step_c W rules fty (P : fty -> W -> Type) A sub c 
  (dt : derrec rules emptyT c) :=
  (forall A' : fty, sub A' A -> 
    forall c (d : derrec rules emptyT c), P A' c) ->
  (forall cn (dtn : derrec rules emptyT cn),
    in_nextup dtn dt -> P A cn) -> P A c.

Definition gf2_step_tr W fty (P : fty -> W -> Type) A sub dtsr dts :=
    ((forall A', sub A' A -> (forall dts, AccT dtsr dts -> P A' dts)) ->
    (forall dts', dtsr dts' dts -> P A dts') -> P A dts).

(** results linking the conditions for inductive proofs for a tree **)

Lemma gs_gsc W fty rules P A sub (c : W) (dt : derrec rules emptyT c):
  iffT (@gen_step W fty P A sub (derrec rules emptyT) 
    (map (@derrec_fc_concl _ _ _) (nextup (fcI dt))) c)
  (@gen_step_c W rules fty P A sub c dt).
Proof. unfold gen_step.  unfold gen_step_c. apply pair ; intros.
- specialize (X X0). clear X0.
apply X. clear X.
apply ForallTI_forall.
intros x inmn.  apply InT_mapE in inmn. cD. subst.  split.
+  apply der_der_fc.
+ destruct inmn.  apply nextup_in_nu in inmn1.
simpl. rewrite der_concl_eq.  eapply X1 in inmn1. exact inmn1.
+ exact dt.
- specialize (X X0). clear X0.
apply X. clear X.
intros * inn.
eapply ForallTD_forall in X1. cD. exact X0.
apply in_nextup_nu in inn.  apply InT_mapI.
exists (fcI dtn). split. simpl. rewrite der_concl_eq. reflexivity.
exact inn. Qed.

Lemma gstr_gf2 W rules fty P A sub (dt : @derrec_fc W rules emptyT) :
  iffT (@gen_step_tr W rules fty P A sub dt)
    (@gf2_step_tr _ fty P A sub (@in_nextup_fc _ _ _) dt).
Proof. unfold gen_step_tr. unfold gf2_step_tr. apply pair ; intros.
- pose (fun A' saa dts => X0 A' saa dts (AccT_in_nextup_fc dts)) as X0'.
exact (X X0' X1).
- revert X1. apply X.  intros. apply (X0 A' X1). Qed.

Lemma gsc_gstr W rules fty P A sub c dt:
  iffT (@gen_step_c W rules fty P A sub c dt)
    (@gen_step_tr W rules fty (fun A' d => P A' (derrec_fc_concl d))
      (A : fty) sub (fcI dt)).
Proof. unfold gen_step_tr. unfold gen_step_c. simpl.
apply pair ; intros.
- rewrite (der_concl_eq dt). apply X. 
+ intros.  specialize (X0 A' X2 (fcI d)). simpl in X0.
rewrite (der_concl_eq d) in X0. exact X0.
+ intros * inn.
specialize (X1 (fcI dtn)). simpl in X1.
rewrite (der_concl_eq dtn) in X1. apply X1.
exact (in_nextup_fcI inn).
- rewrite (der_concl_eq dt) in X. apply X.
+ intros. apply (X0 A' X2).
destruct d. simpl. rewrite (der_concl_eq d). exact d.
+ intros dtn inn. destruct dtn.
simpl. rewrite (der_concl_eq d).
apply (X1 concl d).  dependent destruction inn. exact i. Qed.

(* so we have these results linking these various conditions *)
Check gs_gsc. Check gsc_gstr. Check gstr_gf2.  

(** lemmas enabling inductive proofs for a tree **)

Lemma gen_step_c_lem W rules fty (P : fty -> W -> Type) A sub : AccT sub A ->
  (forall A c dt, @gen_step_c W rules fty P A sub c dt) ->
  forall c (dt : derrec rules emptyT c), P A c.
Proof. intros acc gs. induction acc.
eapply derrec_all_rect. 
intros. destruct H.
unfold gen_step_c in gs.
intros ps concl rpc drs fps.
pose (derI _ rpc drs).
specialize (gs x concl d X).
apply gs. clear gs a X.
intros.  eapply ForallTD_forall in fps. apply fps.
exact (in_nextup_concl_in X). Qed.

(* this also gives an induction principle for derrec_fc *)
Lemma gen_step_tr_lem W rules fty P A sub : AccT sub A ->
  (forall A dt, @gen_step_tr W rules fty P A sub dt) -> forall dt, P A dt.
Proof. intros acc gs. induction acc.
unfold gen_step_tr in gs.  
pose (fun dt => gs x dt X) as p.
intro. destruct dt. revert d. revert concl.
(* note derrec_all_rect is forall conclusions, we want forall trees *)
eapply derrec_rect_mut_all.
- intros. destruct p0.
- intros * apd.  apply p. unfold nextup.
intros dtn ind.  destruct dtn.
exact (allP_all_in_d apd (in_trees_drs d (in_nextup_fc_nu ind))). Qed.

Lemma gf2_step_tr_lem W fty (P : fty -> W -> Type) A sub dtsr :
  (forall A dts, gf2_step_tr P A sub dtsr dts) -> 
     AccT sub A -> (forall dts, AccT dtsr dts -> P A dts).
Proof. intros gs acc. induction acc.
intros dts add. induction add.
unfold gf2_step_tr in gs. exact (gs _ _ X X0). Qed.

(* so have these lemmas for proving results inductively *)
Check gstep.gen_step_lemT. 
Check gen_step_c_lem.  Check gen_step_tr_lem. Check gf2_step_tr_lem.

(** conditions for inductive proofs for two trees **)

Definition dt2fun fty U W rlsa rlsb (P : fty -> U -> W -> Type) (A : fty)
  (da : @derrec_fc U rlsa emptyT) (db : @derrec_fc W rlsb emptyT) :=
  P A (derrec_fc_concl da) (derrec_fc_concl db).

Definition gen_step2_tr U W rulesa rulesb fty P (A : fty) sub 
  (dta : @derrec_fc U rulesa emptyT) (dtb : @derrec_fc W rulesb emptyT) :=
  (forall A' : fty, sub A' A -> forall da db, P A' da db) ->
  (forall dtna, in_nextup_fc dtna dta -> P A dtna dtb) ->
  (forall dtnb, in_nextup_fc dtnb dtb -> P A dta dtnb) -> P A dta dtb.
  
Definition gen_step2_c U W rulesa rulesb fty 
  (P : fty -> U -> W -> Type) (A : fty) sub ca cb
  (dta : derrec rulesa emptyT ca)
  (dtb : derrec rulesb emptyT cb) :=
  (forall A' : fty, sub A' A -> 
    forall ca (dta : derrec rulesa emptyT ca)
      cb (dtb : derrec rulesb emptyT cb), P A' ca cb) ->
  (forall cp (dtp : derrec rulesa emptyT cp),
    in_nextup dtp dta -> P A cp cb) ->
  (forall cq (dtq : derrec rulesb emptyT cq),
    in_nextup dtq dtb -> P A ca cq) -> P A ca cb.

Definition gf_step2_tr U W fty (P : fty -> U -> W -> Type) 
    A sub gfl gfr dta dtb :=
  (forall A', sub A' A ->
    forall a b, AccT gfl a -> AccT gfr b -> P A' a b) ->
  (forall dtp, gfl dtp dta -> P A dtp dtb) ->
  (forall dtq, gfr dtq dtb -> P A dta dtq) -> P A dta dtb.
  
Definition sum_step2_tr U W fty (P : fty -> U -> W -> Type)
    A sub gsl gsr dta dtb :=
  (forall A', sub A' A -> forall a b, P A' a b) ->
  (forall dta' dtb', gsl dta' + gsr dtb' < gsl dta + gsr dtb ->
    P A dta' dtb') -> P A dta dtb.

(** results linking the conditions for intudtive proofs for two trees **)
Lemma gs2_gs2c U W rulesa rulesb fty P (A : fty) sub ca cb dta dtb:
  iffT (@gen_step2 U W fty P A sub 
    (derrec rulesa emptyT) (derrec rulesb emptyT) 
    (der_botr_ps dta) ca (der_botr_ps dtb) cb)
  (@gen_step2_c U W rulesa rulesb fty P A sub ca cb dta dtb).
Proof. unfold gen_step2.  unfold gen_step2_c.
  rewrite <- !der_botr_ps_eq. apply pair ; intros.
- specialize (X X0). clear X0.
apply (fun fa fb => X fa fb dta dtb) ; clear X ; apply ForallTI_forall ;
intros x inmn ; apply InT_mapE in inmn ; cD ; subst ;  split ;
try apply der_der_fc.
+ destruct inmn.  apply nextup_in_nu in inmn1.
simpl. rewrite der_concl_eq.  eapply X1 in inmn1. exact inmn1.
+ destruct inmn.  apply nextup_in_nu in inmn1.
simpl. rewrite der_concl_eq.  eapply X2 in inmn1. exact inmn1.
- specialize (X X0). clear X0.
apply X ; clear X ; intros * inn.
+ eapply ForallTD_forall in X1. cD. exact X0.
apply in_nextup_nu in inn.  apply InT_mapI.
exists (fcI dtp). split. simpl. rewrite der_concl_eq. reflexivity.  exact inn.
+ eapply ForallTD_forall in X2. cD. exact X0.
apply in_nextup_nu in inn.  apply InT_mapI.
exists (fcI dtq). split. simpl. rewrite der_concl_eq. reflexivity.  exact inn.
Qed.

(*
(** results linking the conditions for intudtive proofs for two trees **)
Lemma gs2_gs2c U W rulesa rulesb fty P (A : fty) sub ca cb dta dtb:
  iffT (@gen_step2 U W fty P A sub 
    (derrec rulesa emptyT) (derrec rulesb emptyT) 
    (map (@derrec_fc_concl _ _ _) (nextup (fcI dta))) ca
    (map (@derrec_fc_concl _ _ _) (nextup (fcI dtb))) cb)
  (@gen_step2_c U W rulesa rulesb fty P A sub ca cb dta dtb).
Proof. unfold gen_step2.  unfold gen_step2_c. apply pair ; intros.
- specialize (X X0). clear X0.
apply (fun fa fb => X fa fb dta dtb) ; clear X ; apply ForallTI_forall ;
intros x inmn ; apply InT_mapE in inmn ; cD ; subst ;  split ;
try apply der_der_fc.
+ destruct inmn.  apply nextup_in_nu in inmn1.
simpl. rewrite der_concl_eq.  eapply X1 in inmn1. exact inmn1.
+ destruct inmn.  apply nextup_in_nu in inmn1.
simpl. rewrite der_concl_eq.  eapply X2 in inmn1. exact inmn1.
- specialize (X X0). clear X0.
apply X ; clear X ; intros * inn.
+ eapply ForallTD_forall in X1. cD. exact X0.
apply in_nextup_nu in inn.  apply InT_mapI.
exists (fcI dtp). split. simpl. rewrite der_concl_eq. reflexivity.  exact inn.
+ eapply ForallTD_forall in X2. cD. exact X0.
apply in_nextup_nu in inn.  apply InT_mapI.
exists (fcI dtq). split. simpl. rewrite der_concl_eq. reflexivity.  exact inn.
Qed.
*)

Lemma gs2tr_gf2 U W rulesa rulesb fty P A sub dta dtb :
  iffT (@gen_step2_tr U W rulesa rulesb fty P A sub dta dtb)
    (@gf_step2_tr _ _ fty P A sub 
      (@in_nextup_fc _ _ _) (@in_nextup_fc _ _ _) dta dtb).
Proof. unfold gen_step2_tr. unfold gf_step2_tr. apply pair ; intros.
- pose (fun A' saa a b => 
  X0 A' saa a b (AccT_in_nextup_fc a) (AccT_in_nextup_fc b)) as X0'.
exact (X X0' X1 X2).
- revert X2. revert X1. apply X.  intros. apply (X0 A' X1). Qed.

Lemma gs2c_gs2tr U W rulesa rulesb fty P A sub ca cb dta dtb:
  iffT (@gen_step2_c U W rulesa rulesb fty P A sub ca cb dta dtb)
  (@gen_step2_tr U W rulesa rulesb fty (dt2fun P) A sub (fcI dta) (fcI dtb)).
Proof. unfold gen_step2_tr. unfold gen_step2_c. unfold dt2fun. simpl.
apply pair ; intros.
- rewrite (der_concl_eq dta). rewrite (der_concl_eq dtb). apply X. 
+ intros A' saa ca0 da cb0 db.  
specialize (X0 A' saa (fcI da) (fcI db)). simpl in X0.
rewrite (der_concl_eq da) in X0.  rewrite (der_concl_eq db) in X0. exact X0.
+ intros * inn.  specialize (X1 (fcI dtp)). simpl in X1.
rewrite (der_concl_eq dtp) in X1.  rewrite (der_concl_eq dtb) in X1. apply X1.
exact (in_nextup_fcI inn).
+ intros * inn.  specialize (X2 (fcI dtq)). simpl in X2.
rewrite (der_concl_eq dtq) in X2. rewrite (der_concl_eq dta) in X2. apply X2.
exact (in_nextup_fcI inn).
- rewrite (der_concl_eq dta) in X. rewrite (der_concl_eq dtb) in X. apply X. 
+ intros A' saa *. apply (X0 A' saa).
destruct da. simpl. rewrite (der_concl_eq d). exact d.
destruct db. simpl. rewrite (der_concl_eq d). exact d.
+ intros * inn. destruct dtna.
simpl. rewrite (der_concl_eq d).  apply (X1 concl d).
dependent destruction inn. exact i.
+ intros * inn. destruct dtnb.
simpl. rewrite (der_concl_eq d).  apply (X2 concl d).
dependent destruction inn. exact i.  Qed.

(* so we have these results linking these various conditions *)
Check gs2_gs2c. Check gs2c_gs2tr. Check gs2tr_gf2.  

(** lemmas enabling inductive proofs for two trees **)

Lemma gen_step2_c_lem U W rulesa rulesb fty P A sub : AccT sub A ->
  (forall A ca cb dta dtb,
    @gen_step2_c U W rulesa rulesb fty P A sub ca cb dta dtb) ->
  forall ca (dta : derrec rulesa emptyT ca) cb (dtb : derrec rulesb emptyT cb),
    P A ca cb.
Proof. intros acc gs. induction acc.
eapply derrec_all_rect2. 
intros. destruct H.  intros. destruct H.
unfold gen_step2_c in gs.
intros *. intros rx ry drx dry fpx fpy.
pose (derI _ rx drx) as dx.  pose (derI _ ry dry) as dy.
specialize (gs x cx cy dx dy X).
apply gs ; clear gs a X ; intros. 
+ eapply ForallTD_forall in fpx. apply fpx. exact (in_nextup_concl_in X).
+ eapply ForallTD_forall in fpy. apply fpy. exact (in_nextup_concl_in X).
Qed.

Lemma gen_step2_tr_lem U W rulesa rulesb fty P A sub : AccT sub A ->
  (forall A dta dtb, @gen_step2_tr U W rulesa rulesb fty P A sub dta dtb) ->
  forall dta dtb, P A dta dtb.
Proof. intros acc gs. induction acc.
unfold gen_step2_tr in gs.  pose (fun dta dtb => gs x dta dtb X) as p.
intro. destruct dta. revert d. revert concl.
eapply (@derrec_rect_mut_all U rulesa emptyT 
  (fun ca (d : derrec rulesa emptyT ca) => forall dtb, P x (fcI d) dtb)).
- intros. destruct p0.
- intros * apd dtb. destruct dtb. revert d0. revert concl0.
eapply (derrec_rect_mut_all).
+ intros. destruct p0.
+ intros * apdb. apply p. unfold nextup.
intros dtna inda. destruct dtna.
exact (allP_all_in_d apd (in_trees_drs d (in_nextup_fc_nu inda)) _).
intros dtnb indb. destruct dtnb.
exact (allP_all_in_d apdb (in_trees_drs _ (in_nextup_fc_nu indb))). Qed.

Lemma gf_step2_tr_lem U W fty (P : fty -> U -> W -> Type) A sub gra grb :
  (forall A dta dtb, gf_step2_tr P A sub gra grb dta dtb) -> AccT sub A -> 
    (forall dta, AccT gra dta -> forall dtb, AccT grb dtb -> P A dta dtb).
Proof. intros gs acc. induction acc.
unfold gf_step2_tr in gs.
pose (fun y s dta dtb adg => X y s dta adg dtb) as X'.
pose (fun dta dtb => gs x dta dtb X').
intros dta aga.  induction aga.
intros dtb agb.  pose agb.  induction a1.
apply p.
intros dtp gad.  apply X0 ; assumption.
intros dtq gbd.  apply (X1 dtq gbd (a1 dtq gbd)).
Qed.

Check gen_step2_c_lem.  Check gen_step2_tr_lem.  Check gf_step2_tr_lem.

Definition measure {U} f (dtn dt : U) := f dtn < f dt.

Lemma AccT_measure' U f n : forall dt : U, f dt < n -> AccT (measure f) dt.
Proof.  induction n.
- intros.  apply Nat.nlt_0_r in H.  contradiction H.
- intros.  apply AccT_intro.  intros.  unfold measure in H0.  apply IHn.
apply Lt.lt_n_Sm_le in H.  eapply Lt.lt_le_trans ; eassumption.  Qed.

Definition AccT_measure U f dt := 
  @AccT_measure' U f _ dt (Nat.lt_succ_diag_r _).

Definition size_step2_tr U W fty rulesa rulesb P (A : fty) sub :=
    gf_step2_tr P A sub (measure (@derrec_fc_size U rulesa emptyT))
      (measure (@derrec_fc_size W rulesb emptyT)).

Definition height_step2_tr U W fty rulesa rulesb P (A : fty) sub :=
    gf_step2_tr P A sub (measure (@derrec_fc_height U rulesa emptyT))
      (measure (@derrec_fc_height W rulesb emptyT)).

Lemma size_step2_tr_lem U W fty (rulesa : rlsT U) (rulesb : rlsT W) 
  (P : fty -> derrec_fc rulesa emptyT -> derrec_fc rulesb emptyT -> Type)
  A sub dta dtb: AccT sub A -> 
  (forall A dta dtb, size_step2_tr P A sub dta dtb) -> P A dta dtb.
Proof. unfold size_step2_tr. intros acc fgf.
apply (gf_step2_tr_lem fgf acc) ; apply AccT_measure. Qed.

Lemma height_step2_tr_lem U W fty (rulesa : rlsT U) (rulesb : rlsT W) 
  (P : fty -> derrec_fc rulesa emptyT -> derrec_fc rulesb emptyT -> Type)
  A sub dta dtb: AccT sub A -> 
  (forall A dta dtb, height_step2_tr P A sub dta dtb) -> P A dta dtb.
Proof. unfold height_step2_tr. intros acc fgf.
apply (gf_step2_tr_lem fgf acc) ; apply AccT_measure. Qed.

Lemma nextup_size W rules prems (d dn : @derrec_fc W rules prems):
  InT dn (nextup d) -> derrec_fc_size dn < derrec_fc_size d.
Proof. destruct d. destruct dn.
unfold derrec_fc_size. unfold nextup.
destruct d. intro. inversion X.
intro idt. apply in_trees_drs in idt.
simpl. clear r. (* otherwise complicates induction *)
induction idt ; simpl.
+ apply Lt.le_lt_n_Sm. apply Nat.le_add_r.
+ eapply Lt.lt_le_trans. apply IHidt. apply le_n_S. apply Plus.le_plus_r. Qed.

Lemma nextup_height W rules prems (d dn : @derrec_fc W rules prems):
  InT dn (nextup d) -> derrec_fc_height dn < derrec_fc_height d.
Proof. destruct d. destruct dn.
unfold derrec_fc_height. unfold nextup.
destruct d. intro. inversion X.
intro idt. apply in_trees_drs in idt.
simpl. clear r. (* otherwise complicates induction *)
induction idt ; simpl.
+ apply Lt.le_lt_n_Sm. apply Nat.le_max_l.
+ eapply Lt.lt_le_trans. apply IHidt. apply le_n_S. apply Nat.le_max_r. Qed.

Definition in_nextup_size W rules prems d dn inn :=
  @nextup_size W rules prems d dn (in_nextup_fc_nu inn).
Definition in_nextup_height W rules prems d dn inn :=
  @nextup_height W rules prems d dn (in_nextup_fc_nu inn).

Lemma gs2_tr_size U W fty (rulesa : rlsT U) (rulesb : rlsT W)
  (P : fty -> derrec_fc rulesa emptyT -> derrec_fc rulesb emptyT -> Type)
  A sub dta dtb: 
  gen_step2_tr P A sub dta dtb -> size_step2_tr P A sub dta dtb.
Proof. unfold size_step2_tr. unfold gf_step2_tr.  unfold gen_step2_tr.
intros gs2 saa.
specialize (gs2 (fun A' s a b =>
  saa A' s a b (AccT_measure _ _) (AccT_measure _ _))).
clear saa. intros pb aq. apply gs2.
intros. apply (pb dtna). unfold measure.  apply (in_nextup_size X).
intros. apply (aq dtnb). unfold measure.  apply (in_nextup_size X). Qed.

Lemma gs2_tr_height U W fty (rulesa : rlsT U) (rulesb : rlsT W)
  (P : fty -> derrec_fc rulesa emptyT -> derrec_fc rulesb emptyT -> Type)
  A sub dta dtb: 
  gen_step2_tr P A sub dta dtb -> height_step2_tr P A sub dta dtb.
Proof. unfold height_step2_tr. unfold gf_step2_tr.  unfold gen_step2_tr.
intros gs2 saa.
specialize (gs2 (fun A' s a b =>
  saa A' s a b (AccT_measure _ _) (AccT_measure _ _))).
clear saa. intros pb aq. apply gs2.
intros. apply (pb dtna). unfold measure.  apply (in_nextup_height X).
intros. apply (aq dtnb). unfold measure.  apply (in_nextup_height X). Qed.

Lemma gs2_hs2 (U W fty : Type) rlsl rlsr (P : fty -> U -> W -> Type)
  A sub cl cr (dl : derrec rlsl emptyT cl) (dr : derrec rlsr emptyT cr)
  psl psr (brl : botRule_fc (fcI dl) psl cl) (brr : botRule_fc (fcI dr) psr cr):
  gen_step2 P A sub (derrec rlsl emptyT) (derrec rlsr emptyT) psl cl psr cr ->
  height_step2_tr (dt2fun P) A sub (fcI dl) (fcI dr).
Proof. intro gs2. apply gs2_tr_height.  apply gs2c_gs2tr. apply gs2_gs2c.
rewrite (snd (botRule_fc_prems brl)).  rewrite (snd (botRule_fc_prems brr)).
exact gs2. Qed.

Print Implicit gs2_tr_height.  Print Implicit gs2_hs2.
Check (gs2_hs2 (get_botrule _) (get_botrule _)).

Definition sumh_step2_tr U W fty (rulesa : rlsT U) (rulesb : rlsT W)
  (P : fty -> derrec_fc rulesa emptyT -> derrec_fc rulesb emptyT -> Type)
    A sub := 
      sum_step2_tr P A sub (@derrec_fc_height _ _ _) (@derrec_fc_height _ _ _).

Lemma sum_step2_tr_gf2 U W fty (P : fty -> U -> W -> Type) 
    A sub gsa gsb dta dtb :
  iffT (sum_step2_tr P A sub gsa gsb dta dtb) 
    (gf2_step_tr (fun fml ab => P fml (fst ab) (snd ab)) A sub
      (measure (fun ab => Nat.add (gsa (fst ab)) (gsb (snd ab)))) (dta, dtb)).
Proof. unfold sum_step2_tr. unfold gf2_step_tr.
unfold iffT. split.
- intros fsglp sp glpp.
simpl. apply fsglp.
+ intros A' saa a b.
apply (sp A' saa (a, b)). apply AccT_measure.
+ intros *. specialize (glpp (dta', dtb')).
unfold measure in glpp. simpl in glpp. exact glpp.
- intros sglpp sp glp.
simpl in sglpp. apply sglpp.
intros. destruct dts.  simpl. apply sp. apply X.
intros. destruct dts'. simpl. apply glp.
unfold measure in H. simpl in H. exact H.
Qed.

Definition sum_step2_tr_D_gf2 U W fty P A sub gsa gsb dta dtb :=
  iffT_D1 (@sum_step2_tr_gf2 U W fty P A sub gsa gsb dta dtb).

Lemma sum_step2_tr_lem U W fty (P : fty -> U -> W -> Type)
    A sub gsa gsb dta dtb : AccT sub A -> 
  (forall A dta dtb, sum_step2_tr P A sub gsa gsb dta dtb) -> P A dta dtb.
Proof. intros *. intros acc ss.
pose (fun fty UW => P fty (fst UW) (snd UW)) as Q.
assert (Q A (dta, dtb)).
eapply gf2_step_tr_lem.
intros.  apply sum_step2_tr_D_gf2.
all: cycle 1. exact acc. apply AccT_measure. 
subst Q. simpl in X. exact X.
destruct dts. apply ss. Qed.

Check sum_step2_tr_lem.

Lemma gf2_sum U W fty (P : fty -> U -> W -> Type) A sub gsa gsb dta dtb:
  gf_step2_tr P A sub (measure gsa) (measure gsb) dta dtb ->
    sum_step2_tr P A sub gsa gsb dta dtb.
Proof. unfold sum_step2_tr. unfold gf_step2_tr.
intros gf2 saa lgss.
require gf2. intros. exact (saa A' X a b).
apply gf2 ; intros ; apply lgss ; unfold measure in H.
apply Plus.plus_lt_compat_r. exact H.
apply Plus.plus_lt_compat_l. exact H. Qed.
   
Lemma sumh_step2_tr_lem U W fty (rulesa : rlsT U) (rulesb : rlsT W)
  (P : fty -> derrec_fc rulesa emptyT -> derrec_fc rulesb emptyT -> Type)
  (A : fty) sub dta dtb : AccT sub A ->
  (forall A dta dtb, sumh_step2_tr P A sub dta dtb) -> P A dta dtb.
Proof. unfold sumh_step2_tr.  apply sum_step2_tr_lem. Qed.

Lemma hs2_sumh U W fty rulesa rulesb P A sub dta dtb:
  @height_step2_tr U W fty rulesa rulesb P A sub dta dtb ->
  @sumh_step2_tr U W fty rulesa rulesb P A sub dta dtb.
Proof. unfold height_step2_tr. unfold sumh_step2_tr. apply gf2_sum. Qed.

(* TODO 

if possible, need to look at gen_step2sr
gs2_tr_sr
gs2_sr_tr

val _ = qed_goal_spec_mp "gs2_sr_tr" gentree.thy
  "valid rls dta --> valid rls dtb --> \
    \ gen_step2sr P A sub rls (botRule dta, botRule dtb) --> \
    \ gen_step2_tr (%A (dtl, dtr). P A (conclDT dtl, conclDT dtr)) \
        \ A sub (dta, dtb)"

first, link gen_step and gen_step_c
for gen_step, derivs needs to be derrec rules emptyT
gen_step has ps concl arg, gen_step_c has tree

*)
(* summary of some results for two trees *)
(*
Print gen_step2.
Print gen_step2_c.
Print gen_step2_tr.
Print gf_step2_tr.
Print height_step2_tr.
Check gen_step2_lemT.
Check gen_step2_tr_lem.
Check gf_step2_tr_lem.
Check height_step2_tr_lem.
Check gs2_gs2c.
Check gs2c_gs2tr.
Check gs2tr_gf2.
Check gs2_tr_height.
*)

