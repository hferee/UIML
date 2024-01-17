
(* derrec, derl, etc, other useful stuff *)

Require Export List.
Set Implicit Arguments.
Export ListNotations.

Require Import Coq.Program.Equality. (* for dependent induction/destruction *)

Require Import genT gen existsT.
Require Import PeanoNat.


(* note, this doesn't work Type replaced by Prop,
  although the actual version used allows prems : X -> Prop 
Reset derrec.

Inductive derrec X (rules : list X -> X -> Prop) :
  (X -> Type) -> X -> Prop := 
  | dpI : forall prems concl,
    prems concl -> derrec rules prems concl
  | derI : forall ps prems concl,
    rules ps concl -> dersrec rules prems ps -> derrec rules prems concl 
with dersrec X (rules : list X -> X -> Prop) :
  (X -> Type) -> list X -> Prop :=
  | dlNil : forall prems, dersrec rules prems []
  | dlCons : forall prems seq seqs, 
    derrec rules prems seq -> dersrec rules prems seqs ->
    dersrec rules prems (seq :: seqs)
    .
    *)


(* definition using Forall, seems equivalent *)
Inductive aderrec X (rules : list X -> X -> Prop) 
  (prems : X -> Prop) : X -> Prop := 
  | adpI : forall concl,
    prems concl -> aderrec rules prems concl
  | aderI : forall ps concl, rules ps concl ->
    Forall (aderrec rules prems) ps -> aderrec rules prems concl.
(* need type version of Forall, to change this to Type *)

(* derrec: type of derivation of a sequent ; dersrec: same idea but for
multiple sequents *)

Inductive derrec X (rules : list X -> X -> Type) (prems : X -> Type) :
  X -> Type := 
  | dpI : forall concl,
    prems concl -> derrec rules prems concl
  | derI : forall ps concl,
    rules ps concl -> dersrec rules prems ps -> derrec rules prems concl 
with dersrec X (rules : list X -> X -> Type) (prems : X -> Type) :
  list X -> Type :=
  | dlNil : dersrec rules prems []
  | dlCons : forall seq seqs, 
    derrec rules prems seq -> dersrec rules prems seqs ->
    dersrec rules prems (seq :: seqs)
    .

Scheme derrec_rect_mut := Induction for derrec Sort Type
with dersrec_rect_mut := Induction for dersrec Sort Type.
Scheme derrec_rec_mut := Induction for derrec Sort Set
with dersrec_rec_mut := Induction for dersrec Sort Set.
Scheme derrec_ind_mut := Induction for derrec Sort Prop
with dersrec_ind_mut := Induction for dersrec Sort Prop.
(*
Check derrec_ind_mut.
Check dersrec_ind_mut.
*)
(* combine the two inductive principles *)
Definition derrec_dersrec_rect_mut X rules prems P P0 dp der dln dlc :=
  pair (@derrec_rect_mut X rules prems P P0 dp der dln dlc)
    (@dersrec_rect_mut X rules prems P P0 dp der dln dlc).

Ltac solve_dersrec := repeat (apply dlCons || apply dlNil || assumption).

(* this should be a more useful induction principle for derrec *)
Definition dim_all X rules prems Q := 
  @derrec_ind_mut X rules prems (fun y => fun _ => Q y) 
  (fun ys => fun _ => Forall Q ys).

Definition dim_allT X rules (prems Q : X -> Type) := 
  @derrec_rect_mut X rules prems (fun y => fun _ => Q y) 
  (fun ys => fun _ => ForallT Q ys).

(* this doesn't work
Check (dim_all _ _ (Forall_nil X Q)).
*)
(* here is how to get the tautologies out of dim_all *)
Definition dim_all3 X rules prems Q h1 h2 := 
  @dim_all X rules prems Q h1 h2 (Forall_nil Q).

Definition fce3 X Q D Ds seq seqs (d : D seq) qs (ds : Ds seqs) qss :=
  @Forall_cons X Q seq seqs qs qss.

Definition dim_all4 X rules prems Q h1 h2 := 
  @dim_all3 X rules prems Q h1 h2 
  (@fce3 X Q (derrec rules prems) (dersrec rules prems)).

Definition dim_all8 X rules prems Q h1 h2 := 
  @dim_all3 X rules prems Q h1 h2 
  (fun seq seqs _ qs _ qss => @Forall_cons X Q seq seqs qs qss).
    
(* so dim_all4, or dim_all8 better, is the same as derrec_all_ind below *)

Lemma derrec_all_ind:
  forall X (rules : list X -> X -> Type) (prems Q : X -> Prop),
     (forall concl : X, prems concl -> Q concl) ->
     (forall (ps : list X) (concl : X),
      rules ps concl -> dersrec rules prems ps -> Forall Q ps -> Q concl) ->
     forall y : X, derrec rules prems y -> Q y.
Proof.  intros.
eapply dim_all. exact H. exact H0.
apply Forall_nil.
intros.  apply Forall_cons. assumption.  assumption.
assumption.  Qed.

Lemma derrec_all_indT:
  forall X (rules : list X -> X -> Type) (prems Q : X -> Type),
     (forall concl : X, prems concl -> Q concl) ->
     (forall (ps : list X) (concl : X),
      rules ps concl -> dersrec rules prems ps -> ForallT Q ps -> Q concl) ->
     forall y : X, derrec rules prems y -> Q y.
Proof.  intros X rules prems Q. intros H H0.
eapply dim_allT. exact H. exact H0.
apply ForallT_nil.
intros.  apply ForallT_cons. assumption.  assumption.
Qed.

Lemma derrec_all_rect:
  forall X (rules : list X -> X -> Type) (prems Q : X -> Type),
     (forall concl : X, prems concl -> Q concl) ->
     (forall (ps : list X) (concl : X),
      rules ps concl -> dersrec rules prems ps -> ForallT Q ps -> Q concl) ->
     forall y : X, derrec rules prems y -> Q y.
Proof.  intros.
eapply dim_allT. exact X0. exact X1.
apply ForallT_nil.
intros.  apply ForallT_cons. assumption.  assumption.
assumption.  Qed.

Lemma derrec_derrec' X rules prems:
  (forall c : X, derrec rules (derrec rules prems) c -> derrec rules prems c) *
  (forall cs, dersrec rules (derrec rules prems) cs -> dersrec rules prems cs).
Proof. apply derrec_dersrec_rect_mut.
- intros. assumption.
- intros. eapply derI ; eassumption.
- apply dlNil.
- intros. apply dlCons ; assumption. Qed.

Definition derrec_derrec X rules prems := fst (@derrec_derrec' X rules prems).
Definition dersrec_derrec X rules prems := snd (@derrec_derrec' X rules prems).

Inductive derl X (rules : list X -> X -> Type) : list X -> X -> Type := 
  | asmI : forall p, derl rules [p] p
  | dtderI : forall pss ps concl, rules ps concl ->
    dersl rules pss ps -> derl rules pss concl
with dersl X (rules : list X -> X -> Type) : list X -> list X -> Type := 
  | dtNil : dersl rules [] []
  | dtCons : forall ps c pss cs,
    derl rules ps c -> dersl rules pss cs -> dersl rules (ps ++ pss) (c :: cs)
  . 

Scheme derl_ind_mut := Induction for derl Sort Prop
with dersl_ind_mut := Induction for dersl Sort Prop.
Scheme derl_rec_mut := Induction for derl Sort Set
with dersl_rec_mut := Induction for dersl Sort Set.
Scheme derl_rect_mut := Induction for derl Sort Type
with dersl_rect_mut := Induction for dersl Sort Type.
(*
Check derl_ind_mut.
Check dersl_ind_mut.
*)
Lemma dtCons_eq X rules ps c pss cs psa: derl rules ps (c : X) ->
  dersl rules pss cs -> psa = ps ++ pss -> dersl rules psa (c :: cs). 
Proof. intros. subst. apply dtCons ; assumption. Qed.

Lemma derl_dersl_single X rules ps (c : X) :
  iffT (dersl rules ps [c]) (derl rules ps c).
Proof. split. 
intro. inversion X0. inversion X2. subst.  rewrite app_nil_r. assumption.
intro. eapply (dtCons_eq X0 (dtNil _)).  rewrite app_nil_r. reflexivity. Qed.

(* combine the two inductive principles *)
Definition derl_dersl_rect_mut X rules P P0 asm dtd dtn dtc :=
  pair (@derl_rect_mut X rules P P0 asm dtd dtn dtc)
    (@dersl_rect_mut X rules P P0 asm dtd dtn dtc).

Lemma asmsI X rules ps: @dersl X rules ps ps .
Proof. induction ps. apply dtNil. pose (asmI rules a).
pose (dtCons d IHps). simpl in d0. exact d0. Qed.

Lemma in_derl X rules ps c: rules ps c -> @derl X rules ps c.
Proof. intro. eapply dtderI. eassumption. apply asmsI. Qed.

Definition rsub_derl X rules := rsubI _ _ (@in_derl X rules).

Inductive dercl X (rules : list X -> X -> Type) :
  list X -> X -> Type := 
  | casmI : forall p, dercl rules [p] p
  | dtcderI : forall pss ps concl, rules ps concl ->
    dercsl rules pss ps -> dercl rules (concat pss) concl
with dercsl X (rules : list X -> X -> Type) :
  list (list X) -> list X -> Type := 
  | dtcNil : dercsl rules [] []
  | dtcCons : forall ps c pss cs, dercl rules ps c ->
      dercsl rules pss cs -> dercsl rules (ps :: pss) (c :: cs)
  . 

Scheme dercl_ind_mut := Induction for dercl Sort Prop
with dercsl_ind_mut := Induction for dercsl Sort Prop.
Scheme dercl_rec_mut := Induction for dercl Sort Set
with dercsl_rec_mut := Induction for dercsl Sort Set.
Scheme dercl_rect_mut := Induction for dercl Sort Type
with dercsl_rect_mut := Induction for dercsl Sort Type.
(*
Check dercl_ind_mut.
Check dercsl_ind_mut.
*)
(* combine the two inductive principles *)
Definition dercl_dercsl_rect_mut X rules P P0 asm dtd dtn dtc :=
  pair (@dercl_rect_mut X rules P P0 asm dtd dtn dtc)
    (@dercsl_rect_mut X rules P P0 asm dtd dtn dtc).

Inductive ccps X f (qs cs : list X) : Type :=
  | ccpsI : forall pss, f pss cs -> qs = concat pss -> ccps f qs cs.

Lemma ccpsD X f qs cs: ccps f qs cs ->
  {pss : list (list X) & qs = concat pss & f pss cs}.
Proof. intro cc. destruct cc. subst. exists pss ; tauto. Qed.

Definition drl_allT X (rules Q : list X -> X -> Type) R :=
  @derl_rect_mut X rules (fun ps => fun c => fun _ => Q ps c)
  (fun pss => fun cs => fun _ => R pss cs).

Definition drsl_allT X (rules Q : list X -> X -> Type) R :=
  @dersl_rect_mut X rules (fun ps => fun c => fun _ => Q ps c)
  (fun pss => fun cs => fun _ => R pss cs).

(* these may be too strong, have a condition that has to hold
  even if dersl and Forall2T Q hold for different partition of pss *)
Definition drl_allT' X (rules Q : list X -> X -> Type) :=
  @derl_rect_mut X rules (fun ps => fun c => fun _ => Q ps c)
  (fun ps => fun cs => fun _ => ccps (Forall2T Q) ps cs).

Definition drsl_allT' X (rules Q : list X -> X -> Type) :=
  @dersl_rect_mut X rules (fun ps => fun c => fun _ => Q ps c)
  (fun ps => fun cs => fun _ => ccps (Forall2T Q) ps cs).

Definition dcl_allT X (rules Q : list X -> X -> Type) :=
  @dercl_rect_mut X rules (fun ps => fun c => fun _ => Q ps c)
  (fun pss => fun cs => fun _ => Forall2T Q pss cs).

Definition dcsl_allT X (rules Q : list X -> X -> Type) :=
  @dercsl_rect_mut X rules (fun ps => fun c => fun _ => Q ps c)
  (fun pss => fun cs => fun _ => Forall2T Q pss cs).

Lemma dercl_all_rect: forall X (rules Q : list X -> X -> Type),
  (forall p : X, Q [p] p) ->
  (forall pss qs ps concl, rules ps concl -> dercsl rules pss ps ->
    Forall2T Q pss ps -> qs = concat pss -> Q qs concl) ->
  forall ps c, dercl rules ps c -> Q ps c.
Proof.  intros. eapply dcl_allT.  exact X0.
{ intros. eapply X1.  eassumption.
  eassumption.  eassumption. reflexivity. }
apply Forall2T_nil.
intros. apply Forall2T_cons ; assumption. assumption. Qed.

Lemma derscl_all_dercl: forall X (rules : list X -> X -> Type),
  forall pss cs, dercsl rules pss cs -> Forall2T (dercl rules) pss cs.
Proof. intros X rules. apply dcsl_allT. apply casmI.
intros. eapply dtcderI ; eassumption.
apply Forall2T_nil.  intros.  apply Forall2T_cons ; assumption. Qed.

Lemma all_dercl_derscl: forall X (rules : list X -> X -> Type),
  forall pss cs, Forall2T (dercl rules) pss cs -> dercsl rules pss cs.
Proof. induction pss.
intros. inversion X0. apply dtcNil.
intros. inversion X0. subst. apply dtcCons. assumption.
apply IHpss. assumption.  Qed.

Lemma all_derl_dersl: forall X (rules : list X -> X -> Type),
  forall pss cs, Forall2T (derl rules) pss cs -> dersl rules (concat pss) cs.
Proof. induction pss.
intros. inversion X0. simpl. apply dtNil.
intros. inversion X0. subst. simpl. apply dtCons. assumption.
apply IHpss. assumption.  Qed.

Lemma all_derl_dersl': forall X (rules : list X -> X -> Type),
  forall qs cs, ccps (Forall2T (derl rules)) qs cs -> dersl rules qs cs.
Proof. intros. destruct X0. subst. apply all_derl_dersl. exact f. Qed.

Lemma dersl_all_derl: forall X (rules : list X -> X -> Type),
  forall qs cs, dersl rules qs cs ->
  {pss : list (list X) & qs = concat pss & Forall2T (derl rules) pss cs}.
Proof. intros X rules. eapply drsl_allT. apply asmI.
intros. destruct X0. subst. eapply dtderI. apply r. apply d.
exists []. simpl. reflexivity.  apply Forall2T_nil.
intros. destruct X1. subst. exists (ps :: x).  simpl. reflexivity.
apply Forall2T_cons ; assumption. Qed.

Lemma dersl_all_derl': forall X (rules : list X -> X -> Type),
  forall qs cs, dersl rules qs cs -> ccps (Forall2T (derl rules)) qs cs.
Proof. intros X rules. eapply drsl_allT'. apply asmI.
intros. destruct X0. eapply dtderI ; eassumption.
eapply ccpsI. apply Forall2T_nil.  simpl. reflexivity.
intros. destruct X1. subst. eapply ccpsI.
apply Forall2T_cons ; eassumption.  simpl. reflexivity.  Qed.

Lemma dercl_derl': forall X (rules : list X -> X -> Type),
  prod (forall ps c, dercl rules ps c -> derl rules ps c)
    (forall pss cs, dercsl rules pss cs -> dersl rules (concat pss) cs).
Proof. intros.
eapply (dercl_dercsl_rect_mut (rules := rules)
  (fun ps : list X => fun c => fun _ => derl rules ps c)
  (fun pss cs => fun _ => dersl rules (concat pss) cs)).
apply asmI.
intros. eapply dtderI. eassumption.
subst. assumption.
simpl. apply dtNil.
intros. simpl. apply dtCons ; assumption.  Qed.

Definition dercl_derl X rules := fst (@dercl_derl' X rules).
Definition dercsl_dersl X rules := snd (@dercl_derl' X rules).

Lemma derl_dercl: forall X (rules : list X -> X -> Type),
  forall ps c, derl rules ps c -> dercl rules ps c.
Proof.  intros X rules.
eapply (drl_allT (dercl rules) (ccps (dercsl rules))).
apply casmI.
{ intros. destruct X0. subst.
eapply dtcderI. eassumption.  eassumption. }
{ eapply ccpsI. apply dtcNil. simpl. reflexivity. }
{ intros. destruct X1. subst.
eapply ccpsI. eapply dtcCons ; eassumption.
simpl. reflexivity. } Qed.

Lemma derl_all_rect: forall X (rules Q : list X -> X -> Type),
  (forall p : X, Q [p] p) ->
  (forall pss qs ps concl, rules ps concl -> dersl rules qs ps ->
    Forall2T Q pss ps -> qs = concat pss -> Q qs concl) ->
  forall ps c, derl rules ps c -> Q ps c.
Proof.  intros X rules Q asm dtd.
eapply (drl_allT Q (ccps (Forall2T Q))).
exact asm.
{ intros. destruct X0. subst.
eapply dtd. eassumption. eassumption. eassumption. reflexivity. }
{ eapply ccpsI. apply Forall2T_nil. simpl. reflexivity. }
{ intros. destruct X1. subst.
eapply ccpsI. eapply Forall2T_cons ; eassumption.
simpl. reflexivity. } Qed.
(*
Check derl_all_rect.  
Check derl_dercl. 
Check dercl_derl.
*)
(* no convenient way of expressing the corresponding result
  for dercsl except using sth like allrel *)

Lemma derrec_same: forall X rules prems (c c' : X),
  derrec rules prems c -> c = c' -> derrec rules prems c'.
Proof. intros. subst. assumption. Qed.

(* further detailed versions of derrec_same *)
Lemma derrec_same_nsL: forall Y X D rules prems G H unk0 d (unk1 unk1' : X),
  derrec rules prems (G ++ (unk1 : X, unk0 : Y, d : D) :: H) ->
    unk1 = unk1' -> derrec rules prems (G ++ (unk1', unk0, d) :: H).
Proof. intros. subst. assumption. Qed.

Lemma derrec_same_nsR: forall Y X D rules prems G H unk1 d (unk0 unk0' : X),
  derrec rules prems (G ++ (unk1 : Y, unk0 : X, d : D) :: H) ->
    unk0 = unk0' -> derrec rules prems (G ++ (unk1, unk0', d) :: H).
Proof. intros. subst. assumption. Qed.

Lemma dersrec_all: forall X rules prems (cs : list X),
  iffT (dersrec rules prems cs) (ForallT (derrec rules prems) cs).
Proof.  intros. 
induction cs ; unfold iffT ; apply pair ; intro.
apply ForallT_nil. apply dlNil.
inversion X0. apply ForallT_cons. assumption. 
unfold iffT in IHcs. destruct IHcs. tauto.
inversion X0. subst. apply dlCons.  assumption. 
unfold iffT in IHcs. destruct IHcs. tauto.
Qed.

Definition dersrecD_all X rs ps cs := iffT_D1 (@dersrec_all X rs ps cs).
Definition dersrecI_all X rs ps cs := iffT_D2 (@dersrec_all X rs ps cs).

Lemma prems_dersrec X rules prems cs:
  ForallT prems cs -> @dersrec X rules prems cs.
Proof. induction cs ; intros. apply dlNil.
inversion X0. subst. apply dlCons. apply dpI. assumption. tauto. Qed. 

Lemma dersrec_forall: forall X rules prems (cs : list X),
  iffT (dersrec rules prems cs) (forall c, InT c cs -> derrec rules prems c).
Proof. intros. rewrite dersrec_all. rewrite ForallT_forall. reflexivity. Qed.

Definition dersrecD_forall X rs ps cs := iffT_D1 (@dersrec_forall X rs ps cs).
Definition dersrecI_forall X rs ps cs := iffT_D2 (@dersrec_forall X rs ps cs).

Lemma dersrec_nil: forall X rules prems, dersrec rules prems ([] : list X).
Proof. apply dlNil. Qed.

(* this is very difficult for such an obvious result,
  better if we can rewrite based on iffT *)
Lemma dersrec_app: forall X rules prems cs ds,
  iffT (dersrec rules prems (cs ++ ds : list X)) 
    (prod (dersrec rules prems cs) (dersrec rules prems ds)).
Proof. intros. eapply iffT_trans. apply dersrec_forall.
unfold iffT. split ; intros. 
split ; apply dersrecI_forall ; intros ; apply X0.
apply InT_appL. assumption.  apply InT_appR. assumption. 
apply InT_appE in X1. sD.
eapply dersrecD_forall. 2 : eassumption. assumption. 
eapply dersrecD_forall. 2 : eassumption. assumption. Qed.

Definition dersrec_appD X rules prems cs ds := 
  iffT_D1 (@dersrec_app X rules prems cs ds).
Definition dersrec_appL X rules prems cs ds da := 
  fst (@dersrec_appD X rules prems cs ds da).
Definition dersrec_appR X rules prems cs ds da := 
  snd (@dersrec_appD X rules prems cs ds da).
Definition dersrec_appJ X rules prems cs ds := 
  iffT_D2 (@dersrec_app X rules prems cs ds).
Definition dersrec_appI X rules prems cs ds := 
  prod_uncurry (@dersrec_appJ X rules prems cs ds).

Lemma dersrec_single: forall X rules prems c,
  iffT (dersrec rules prems [c]) (derrec rules prems (c : X)).
Proof. intros.  rewrite dersrec_all. rewrite ForallT_single. reflexivity. Qed.

Definition dersrec_singleD X rs ps c := iffT_D1 (@dersrec_single X rs ps c).
Definition dersrec_singleI X rs ps c := iffT_D2 (@dersrec_single X rs ps c).

Lemma dersrec_map_single: forall X Y (f : X -> Y) rules prems c,
  iffT (dersrec rules prems (map f [c])) (derrec rules prems (f c)).
Proof. simpl. intros. apply dersrec_single. Qed.

Lemma dersrec_map_2: forall X Y (f : X -> Y) rules prems c d,
  iffT (dersrec rules prems (map f [c ; d]))
    (derrec rules prems (f c) * derrec rules prems (f d)).
Proof. intros. rewrite dersrec_all. rewrite ForallT_map_2. reflexivity. Qed.

(* try using the induction principle derrec_all_rect *)
Theorem derrec_trans_imp: forall X rules prems (concl : X),
  derrec rules (derrec rules prems) concl -> derrec rules prems concl.
Proof.  intros. revert X0.
eapply derrec_all_rect. tauto.
intros.  eapply derI. exact X0.
apply dersrecI_all. exact X2. Qed.

Lemma derrec_rmono_s: forall W (rulesa rulesb : rlsT W) prems,
  rsub rulesa rulesb -> 
  (forall concl, derrec rulesa prems concl -> derrec rulesb prems concl) *
  (forall cs, dersrec rulesa prems cs -> dersrec rulesb prems cs).
Proof. intros. apply derrec_dersrec_rect_mut ; intros.
- apply dpI. assumption.
- eapply derI. unfold rsub in X. apply X. eassumption. assumption.
- apply dlNil.
- apply dlCons ; assumption. Qed.

Definition derrec_rmono W rulesa rulesb prems concl rs := 
  fst (@derrec_rmono_s W rulesa rulesb prems rs) concl.
Definition dersrec_rmono W rulesa rulesb prems rs := 
  snd (@derrec_rmono_s W rulesa rulesb prems rs).

Theorem derl_derrec_trans': forall X rules prems,
  (forall rps (concl : X), derl rules rps concl ->
    dersrec rules prems rps -> derrec rules prems concl) *
  (forall rps cs, dersl rules rps cs ->
    dersrec rules prems rps -> dersrec rules prems cs).
Proof.  intros.
apply derl_dersl_rect_mut.
- intros.  inversion X0. assumption.
- intros. eapply derI. eassumption. tauto.
- tauto.
- intros ps c pss cs. intros dc dsdc dscs dspc dspps.
apply dersrecD_all in dspps.  apply dlCons.
+ apply dsdc.  apply ForallT_appendD1 in dspps.
apply dersrecI_all. exact dspps.  
+ apply dspc.  apply ForallT_appendD2 in dspps.
apply dersrecI_all. exact dspps. Qed.

Definition derl_derrec_trans X rules prems := 
  fst (@derl_derrec_trans' X rules prems).
Definition dersl_dersrec_trans X rules prems := 
  snd (@derl_derrec_trans' X rules prems).

Theorem derrec_derl_deriv': forall X rules prems,
  (forall (concl : X),
    derrec (derl rules) prems concl -> derrec rules prems concl) *
  (forall cs, dersrec (derl rules) prems cs -> dersrec rules prems cs).
Proof.  intros.
apply derrec_dersrec_rect_mut.
- apply dpI.
- intros. eapply derl_derrec_trans in r. eassumption.  assumption.
- apply dlNil.
- intros. apply dlCons ; assumption.  Qed.

Definition derrec_derl_deriv X rules prems :=
  fst (@derrec_derl_deriv' X rules prems).
Definition dersrec_derl_deriv X rules prems :=
  snd (@derrec_derl_deriv' X rules prems).

Definition derl_derrec X rules prems rps (concl : X) drrc prems_cond :=
  @derl_derrec_trans X rules prems rps (concl : X) drrc 
    (@prems_dersrec X rules prems rps prems_cond).

Definition derl_derrec_nil X rules prems (concl : X) drrc :=
  @derl_derrec_trans X rules prems [] (concl : X) drrc 
    (@dlNil X rules prems).

Lemma dersl_dersrec_nil X rules prems (cs : list X):
  dersl rules [] cs -> dersrec rules prems cs.
Proof. induction cs ; intros. apply dlNil.
inversion X0. destruct ps. simpl in H0. subst. 
apply dlCons. apply derl_derrec_nil. assumption. tauto.
simpl in H0. discriminate H0.  Qed.

Lemma dersl_cons: forall X rules qs p (ps : list X), 
  dersl rules qs (p :: ps) -> sigT (fun qsa => sigT (fun qsb =>
    prod (qs = qsa ++ qsb) (prod (derl rules qsa p) (dersl rules qsb ps)))).
Proof.  intros.  inversion X0. subst.
eapply existT.  eapply existT.  apply pair.  reflexivity. tauto. Qed.

Lemma dersl_app_eq: forall X rules (psa psb : list X) qs, 
  dersl rules qs (psa ++ psb) -> sigT (fun qsa => sigT (fun qsb =>
    prod (qs = qsa ++ qsb) (prod (dersl rules qsa psa) (dersl rules qsb psb)))).
Proof.  intro.  intro.  intro.  intro.  induction psa.  intros. 
apply existT with [].  apply existT with qs. simpl. simpl in X0.
apply pair. trivial.
apply pair. apply dtNil. apply X0.

simpl. intros. apply dersl_cons in X0.
cD.  pose (IHpsa _ X4).  cD. subst.
eapply existT.  eapply existT. 
apply pair.  apply app_assoc.  apply pair.
apply dtCons. assumption.  assumption.  assumption.
Qed.

Lemma derl_trans': forall X (rules : list X -> X -> Type),
  (forall (rps : list X) (concl : X), derl rules rps concl ->
  forall (pss : list X), dersl rules pss rps -> derl rules pss concl) *
  (forall (rps : list X) (cs : list X), dersl rules rps cs ->
  forall (pss : list X), dersl rules pss rps -> dersl rules pss cs).
Proof.  intros.
apply derl_dersl_rect_mut.
- intros. inversion_clear X0. inversion_clear X2.
rewrite app_nil_r.  assumption.
- intros pss ps concl. intros rps dsl dsds pss0 ds0. apply dsds in ds0.
eapply dtderI. eassumption. assumption.
- intros. assumption.
- intros ps c pss cs. intros d dsd dsl dsds pss0 dspps.
apply dersl_app_eq in dspps. cD. subst. apply dtCons.
apply dsd. assumption. apply dsds. assumption. Qed.

Definition derl_trans X rules pss rps concl d := 
  fst (@derl_trans' X rules) rps concl d pss.
Definition dersl_trans X rules pss rps cs ds := 
  snd (@derl_trans' X rules) rps cs ds pss.

(* alternatively, just induction on the list of conclusions *)
Lemma dersl_trans_alt: forall X (rules : list X -> X -> Type)
           (cs rps : list X), dersl rules rps cs ->
	 forall (pss : list X), dersl rules pss rps -> dersl rules pss cs.
Proof.  intro.  intro.  intro.  
induction cs.
intros. inversion X0. subst. assumption.
intros.  apply dersl_cons in X0. cD. subst.
apply dersl_app_eq in X1. cD. subst.
apply dtCons. eapply derl_trans. eassumption. assumption.
firstorder.  Qed.

Theorem derl_dersl_deriv': forall X rules,
  (forall prems (concl : X),
    derl (derl rules) prems concl -> derl rules prems concl) *
  (forall prems cs,
    dersl (derl rules) prems cs -> dersl rules prems cs).
Proof. intros.
apply derl_dersl_rect_mut.
- intro. apply asmI.
- intros. eapply derl_trans. eassumption.  assumption.
- apply dtNil.
- intros.  apply dtCons.  assumption.  assumption. Qed.

Definition derl_deriv' X rules := fst (@derl_dersl_deriv' X rules).
Definition dersl_deriv' X rules := snd (@derl_dersl_deriv' X rules).
Definition derl_deriv X rules := rsubI _ _ (@derl_deriv' X rules).
Definition dersl_deriv X rules := rsubI _ _ (@dersl_deriv' X rules).

Theorem derl_dersl_mono': forall X rulesa rulesb, rsub rulesa rulesb -> 
  (forall prems (concl : X),
    derl rulesa prems concl -> derl rulesb prems concl) *
  (forall prems cs,
    dersl rulesa prems cs -> dersl rulesb prems cs).
Proof. intros X rulesa rulesb rsab.
apply derl_dersl_rect_mut.
- apply asmI.
- intros. eapply dtderI. unfold rsub in rsab.
apply rsab.  eassumption.  assumption.
- apply dtNil.
- intros.  apply dtCons.  assumption.  assumption. Qed.

Definition derl_mono' X rulesa rulesb rsab := 
  fst (@derl_dersl_mono' X rulesa rulesb rsab).
Definition dersl_mono' X rulesa rulesb rsab := 
  snd (@derl_dersl_mono' X rulesa rulesb rsab).

Definition derl_mono X rulesa rulesb rsab :=
  rsubI _ _ (@derl_mono' X rulesa rulesb rsab).
Definition dersl_mono X rulesa rulesb rsab :=
  rsubI _ _ (@dersl_mono' X rulesa rulesb rsab).

Lemma derrec_nil_derl_s X rules: (forall concl, 
  derrec rules (@emptyT X) concl -> derl rules [] concl) *
  (forall cs, dersrec rules (@emptyT X) cs -> dersl rules [] cs).
Proof. 
apply derrec_dersrec_rect_mut ; intros.
- inversion p.
- eapply dtderI ; eassumption. 
- apply dtNil.
- eapply dtCons_eq. eassumption. eassumption. tauto. Qed.

Definition derrec_nil_derl X rules := fst (@derrec_nil_derl_s X rules).
Definition dersrec_nil_dersl X rules := snd (@derrec_nil_derl_s X rules).

Definition derI_rules_mono X rules rulesb prems ps concl rs fuv :=
  @derI X rulesb prems ps concl (@rsub_imp _ _ rules rulesb rs ps concl fuv).
(*
Check derrec_trans_imp.
Check derl_derrec_trans.
Check derrec_derl_deriv.
Check dersl_app_eq.
Check derl_trans.
Check dersl_trans.
Check derl_deriv.
*)

(** induction for two proof trees **)

Lemma derrec_all_rect2:
  forall X Y (rulesx : list X -> X -> Type) (rulesy : list Y -> Y -> Type) 
    (premsx : X -> Type) (premsy : Y -> Type) (Q : X -> Y -> Type),
    (forall px, premsx px -> forall cy, derrec rulesy premsy cy -> Q px cy) ->
    (forall py, premsy py -> forall cx, derrec rulesx premsx cx -> Q cx py) ->
    (forall psx cx psy cy, rulesx psx cx -> rulesy psy cy -> 
      dersrec rulesx premsx psx -> dersrec rulesy premsy psy -> 
      ForallT (fun px => Q px cy) psx -> ForallT (Q cx) psy -> Q cx cy) ->
    forall (conclx : X), derrec rulesx premsx conclx ->
    forall (concly : Y), derrec rulesy premsy concly ->
    Q conclx concly.
Proof.  intros until conclx. intro Dx.
eapply (derrec_all_rect (Q := fun conclx => 
  forall concly : Y, derrec rulesy premsy concly -> Q conclx concly)).
intros.  apply X0. exact X3. exact X4.
intros until concly. intro Dy.
eapply (derrec_all_rect (Q := Q concl)).
intros. apply X1. exact X6.  eapply derI ; eassumption.
intros. eapply X2. eassumption. eassumption. assumption. assumption. 
eapply ForallT_impl in X5. exact X5.
intros. simpl. apply X9. eapply derI ; eassumption.
assumption.  assumption.  assumption.  Qed.
(*
Check derrec_all_rect2.
*)
(* version with no premises *)
Definition derrec_all_rect2_nops X Y rulesx rulesy Q := 
  @derrec_all_rect2 X Y rulesx rulesy emptyT emptyT Q
  (@emptyT_any' X _) (@emptyT_any' Y _).
(*
Check derrec_all_rect2_nops.
*)
(** admissibility **)

Inductive adm X rules ps c : Type := 
  | admI : (dersrec rules (@emptyT X) ps -> derrec rules (@emptyT X) c) ->
    adm X rules ps c.

Definition admD X rules ps c (a : @adm X rules ps c) :=
  match a with | admI d => d end.
Definition admDs X rules p c a d := @admD X rules [p] c a (dersrec_singleI d).

Lemma derl_sub_adm X rules ps c : @derl X rules ps c -> adm rules ps c.
Proof. intro. apply admI.  apply derl_derrec_trans. assumption. Qed.

Definition rsub_derl_adm X rules := rsubI _ _ (@derl_sub_adm X rules).

Definition in_adm X rules ps c r := derl_sub_adm (@in_derl X rules ps c r).
Definition rsub_adm X rules := rsubI _ _ (@in_adm X rules).

Lemma derrec_adm' X rls:
  (forall c, derrec (adm rls) (@emptyT X) c -> derrec rls (@emptyT X) c) * 
  (forall cs, dersrec (adm rls) (@emptyT X) cs -> dersrec rls (@emptyT X) cs).
Proof. apply derrec_dersrec_rect_mut ; intros.
- inversion p.
- inversion r. apply X1. apply X0.
- apply dlNil.
- apply dlCons ; assumption. Qed.

Definition derrec_adm X rls := fst (@derrec_adm' X rls).
Definition dersrec_adm X rls := snd (@derrec_adm' X rls).

Lemma adm_adm X rules ps c : @adm X (adm rules) ps c -> adm rules ps c.
Proof. intros aa. inversion aa. apply admI. intros dps.
apply derrec_adm. apply X0. eapply dersrec_rmono.
apply rsubI. apply in_adm. assumption.  Qed.

Lemma derl_adm_s X rules : 
  (forall ps (c : X), derl (adm rules) ps c -> adm rules ps c) * 
  (forall ps cs, dersl (adm rules) ps cs -> ForallT (adm rules ps) cs). 
Proof. apply derl_dersl_rect_mut ; intros.
- apply admI. intro. inversion X0. assumption.  
- apply admI. destruct r. intros dpss. apply d0.
apply dersrecI_forall. intros c icp.
eapply ForallTD_forall in X0.
destruct X0. apply d1. apply dpss. apply icp.
- apply ForallT_nil.
- apply ForallT_cons. apply admI. inversion X0.
intro. apply X2. apply dersrec_appL in X3. assumption.
apply ForallTI_forall. intros x ixcs. 
apply admI. intros dsa.
eapply ForallTD_forall in X1.
inversion X1. apply X2. apply dersrec_appR in dsa.
exact dsa.  exact ixcs. Qed.

Definition derl_adm X rules := fst (@derl_adm_s X rules).
Definition dersl_adm X rules := snd (@derl_adm_s X rules).

(* also adm (derl rules) = adm rules *)

(* plug-in replacement for derl_derrec_trans *)
Lemma adm_derrec_trans X rules rps concl: @adm X rules rps concl -> 
  dersrec rules (@emptyT X) rps -> derrec rules (@emptyT X) concl.
Proof. intros a drs. destruct a. apply d. apply drs. Qed.

Lemma adm_single_trans X rules prems p c:
  adm rules prems p -> @adm X rules [p] c -> adm rules prems c.
Proof. split. destruct X0. inversion X1. 
intro dps. apply X0. right. apply (d dps). left. Qed.

Lemma derrec_eq_swap : forall (T : Type) rules prems G H
    (pf : (G : T) = H),
    derrec rules prems G ->
    derrec rules prems H.
Proof.  intros. subst. assumption. Qed.



Lemma dersrec_double: forall X rules prems c1 c2,
  iffT (dersrec rules prems [c1;c2]) ((derrec rules prems (c1 : X)) * (derrec rules prems (c2 : X))).
Proof.
  intros. split; intros H.
  split; (eapply dersrecD_forall; [apply H |]).
  constructor 1. reflexivity.
  constructor 2. constructor 1. reflexivity.
  eapply dersrecI_forall. intros c Hc.
  inversion Hc as [ | ? ? H2]; subst. apply H.
  inversion H2 as [ | ? ? H3]; subst. apply H.
  inversion H3.
Qed.

Definition dersrec_doubleD X rs ps c1 c2 := iffT_D1 (@dersrec_double X rs ps c1 c2).