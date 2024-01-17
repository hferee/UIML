
(* constructions for inductive proofs about derivations,
  part adapted from ~jeremy/isabelle/2005/seqms/gstep.{thy,ML}
  but can_trf_rules and friends are new *)

Set Implicit Arguments.

Require Import Init.Wf.  (* wfp called Acc, note Acc_intro, Acc_rect,
  or AccT for Type version *)

Require Import Coq.Program.Equality. (* for dependent induction/destruction *)
Require Import PeanoNat. (* for Nat *)

(* Add LoadPath "../tense-lns". *)
Require Import gen genT. 
Require Import ddT dd_fc. 
Require Import rtcT. 

(*
"gen_step ?P ?A ?sub ?derivs (?ps, ?concl) =
  ((ALL A'. (A', ?A) : ?sub --> Ball ?derivs (?P A')) -->
  (ALL p:set ?ps. p : ?derivs & ?P ?A p) -->
  ?concl : ?derivs --> ?P ?A ?concl)"
  *)

Definition gen_step (seq fml : Type) P A (sub : fml -> fml -> Type)
  derivs ps (concl : seq) := 
  (forall A', sub A' A -> (forall x, derivs x -> P A' x)) ->
  ForallT (fun p => prod (derivs p) (P A p)) ps -> derivs concl -> P A concl.

Lemma gen_step_sub_mono seq fml P A sub1 sub2 derivs ps c :
  rsub sub1 sub2 -> gen_step P A sub1 derivs ps c ->
  @gen_step seq fml P A sub2 derivs ps c.
Proof. unfold gen_step. intros rs gs saa. apply gs.
intros A' s1aa. exact (saa A' (rsubD rs _ _ s1aa)). Qed.

Lemma gen_step_def: forall (seq fml : Type) P A sub derivs ps (concl : seq), 
  @gen_step seq fml P A sub derivs ps concl =
  ((forall A', sub A' A -> (forall x, derivs x -> P A' x)) ->
  ForallT (fun p => prod (derivs p) (P A p)) ps -> derivs concl -> P A concl).
Proof.  intros. unfold gen_step. reflexivity. Qed.
    
Inductive gen_step' (seq fml : Type) P A (sub : fml -> fml -> Type)
  derivs ps (concl : seq) := 
  | gsI : ((forall A', sub A' A -> (forall x, derivs x -> P A' x)) ->
  ForallT (fun p => prod (derivs p) (P A p)) ps -> derivs concl -> P A concl) ->
  gen_step' P A (sub : fml -> fml -> Type) derivs ps (concl : seq).
                                             
Lemma gs_gs': forall (seq fml : Type) P A (sub : fml -> fml -> Type)
  derivs ps (concl : seq), 
  iffT (gen_step P A sub derivs ps concl) (gen_step' P A sub derivs ps concl).
Proof. intros. unfold gen_step. unfold iffT. split ; intros.
apply gsI. exact X.
destruct X. apply p ; assumption. Qed.  

(*
"gen_step2 ?P ?A ?sub (?dls, ?drs) ((?psl, ?cl), ?psr, ?cr) =
  ((ALL A'.
       (A', ?A) : ?sub --> (ALL dl:?dls. ALL dr:?drs. ?P A' (dl, dr))) -->
   (ALL pl:set ?psl. pl : ?dls & ?P ?A (pl, ?cr)) -->
   (ALL pr:set ?psr. pr : ?drs & ?P ?A (?cl, pr)) -->
   ?cl : ?dls --> ?cr : ?drs --> ?P ?A (?cl, ?cr))"
*)

Definition gen_step2 (seql seqr fml : Type) (P : fml -> seql -> seqr -> Type)
  A (sub : fml -> fml -> Type) dls drs psl cl psr cr :=
  (forall A', sub A' A -> 
    forall dl, dls dl -> forall dr, drs dr -> P A' dl dr) ->
  ForallT (fun pl => prod (dls pl) (P A pl cr)) psl -> 
  ForallT (fun pr => prod (drs pr) (P A cl pr)) psr -> 
  dls cl -> drs cr -> P A cl cr.

Lemma gen_step2_sub_mono seql seqr fml P A sub1 sub2 dls drs psl cl psr cr :
  rsub sub1 sub2 -> gen_step2 P A sub1 dls drs psl cl psr cr ->
  @gen_step2 seql seqr fml P A sub2 dls drs psl cl psr cr.
Proof. unfold gen_step2. intros rs gs saa. apply gs.
intros A' s1aa. exact (saa A' (rsubD rs _ _ s1aa)). Qed.

Definition gen_step2_empty seql seqr fml P A sub dls drs psl cl psr cr :=
  (@gen_step2_sub_mono seql seqr fml P A _ sub dls drs psl cl psr cr)
  (rsub_emptyT sub).

(* generalised version of inductive step proof *) 
Lemma gen_step_lem_psT: forall (sty fty : Type) (P : fty -> sty -> Type)
  A sub rules prems, AccT sub A ->
    (forall A ps concl, rules ps concl ->
      gen_step P A sub (derrec rules prems) ps concl) -> 
    (forall A prem, prems prem -> P A prem) -> 
    (forall seq, derrec rules prems seq -> P A seq).
Proof. intros until 0. intros acc gs prs. induction acc.
intros.  eapply derrec_all_rect. apply prs.
intros. unfold gen_step in gs. eapply gs. exact X1. exact X.
apply ForallTI_forall. intros. split. 
eapply dersrecD_forall in X2. exact X2. exact X4.
eapply ForallTD_forall in X3. exact X3. exact X4.
eapply derI ; eassumption. exact X0. Qed.

Lemma gen_step_lem_ps: forall (sty fty : Type) (P : fty -> sty -> Type)
  A sub rules prems, Acc sub A ->
    (forall A ps concl, rules ps concl ->
      gen_step P A sub (derrec rules prems) ps concl) -> 
    (forall A prem, prems prem -> P A prem) -> 
    (forall seq, derrec rules prems seq -> P A seq).
Proof. intros until 0. intros acc gs prs. induction acc.
intros.  eapply derrec_all_rect. apply prs.
intros. unfold gen_step in gs. eapply gs. exact X1. exact X.
apply ForallTI_forall. intros. split. 
eapply dersrecD_forall in X2. exact X2. exact X4.
eapply ForallTD_forall in X3. exact X3. exact X4.
eapply derI ; eassumption. exact X0. Qed.

Check gen_step_lem_ps.

Definition gen_step_lem sty fty P A sub rules acc gs :=
  @gen_step_lem_ps sty fty P A sub rules (@emptyT sty) acc gs 
  (fun A0 => @emptyT_any' sty (P A0)).

Definition gen_step_lemT sty fty P A sub rules acc gs :=
  @gen_step_lem_psT sty fty P A sub rules (@emptyT sty) acc gs 
  (fun A0 => @emptyT_any' sty (P A0)).

Check gen_step_lem.

(* this one does allow for premises *)
Lemma gen_step2_lem_ps: forall (stya styb fty : Type) P (A : fty) sub
  rlsa rlsb (premsa : stya -> Type) (premsb : styb -> Type),
  Acc sub A -> (forall A psa psb ca cb, rlsa psa ca -> rlsb psb cb -> 
  gen_step2 P A sub (derrec rlsa premsa) 
    (derrec rlsb premsb) psa ca psb cb) -> 
 (forall A pa, premsa pa -> forall cb, derrec rlsb premsb cb -> P A pa cb) -> 
 (forall A pb, premsb pb -> forall ca, derrec rlsa premsa ca -> P A ca pb) -> 
  forall seqa, derrec rlsa premsa seqa ->
  forall seqb, derrec rlsb premsb seqb -> P A seqa seqb.
Proof. intros until 0. intros acc gs prsa prsb. induction acc.
eapply derrec_all_rect2.
intros. eapply prsa in X0. exact X0. exact X1.
intros. eapply prsb in X0. exact X0. exact X1.
intros. unfold gen_step2 in gs. eapply gs. exact X0. exact X1. exact X.
apply ForallTI_forall. intros. split. 
eapply dersrecD_forall in X2. exact X2. exact X6.
eapply ForallTD_forall in X4. exact X4. exact X6.
apply ForallTI_forall. intros. split. 
eapply dersrecD_forall in X3. exact X3. exact X6.
eapply ForallTD_forall in X5. exact X5. exact X6.
eapply derI ; eassumption.  eapply derI ; eassumption. Qed.

Lemma gen_step2_lem_psT: forall (stya styb fty : Type) P (A : fty) sub
  rlsa rlsb (premsa : stya -> Type) (premsb : styb -> Type),
  AccT sub A -> (forall A psa psb ca cb, rlsa psa ca -> rlsb psb cb -> 
  gen_step2 P A sub (derrec rlsa premsa) 
    (derrec rlsb premsb) psa ca psb cb) -> 
 (forall A pa, premsa pa -> forall cb, derrec rlsb premsb cb -> P A pa cb) -> 
 (forall A pb, premsb pb -> forall ca, derrec rlsa premsa ca -> P A ca pb) -> 
  forall seqa, derrec rlsa premsa seqa ->
  forall seqb, derrec rlsb premsb seqb -> P A seqa seqb.
Proof. intros until 0. intros acc gs prsa prsb. induction acc.
eapply derrec_all_rect2.
intros. eapply prsa in X0. exact X0. exact X1.
intros. eapply prsb in X0. exact X0. exact X1.
intros. unfold gen_step2 in gs. eapply gs. exact X0. exact X1. exact X.
apply ForallTI_forall. intros. split. 
eapply dersrecD_forall in X2. exact X2. exact X6.
eapply ForallTD_forall in X4. exact X4. exact X6.
apply ForallTI_forall. intros. split. 
eapply dersrecD_forall in X3. exact X3. exact X6.
eapply ForallTD_forall in X5. exact X5. exact X6.
eapply derI ; eassumption.  eapply derI ; eassumption. Qed.

Check gen_step2_lem_ps.

(* this one doesn't allow for premises *)
Definition gen_step2_lem stya styb fty P A sub rlsa rlsb acc gs :=
  @gen_step2_lem_ps stya styb fty P A sub rlsa rlsb 
  (@emptyT stya) (@emptyT styb) acc gs
  (fun _ => @emptyT_any' stya _) (fun _ => @emptyT_any' styb _).

Definition gen_step2_lemT stya styb fty P A sub rlsa rlsb acc gs :=
  @gen_step2_lem_psT stya styb fty P A sub rlsa rlsb 
  (@emptyT stya) (@emptyT styb) acc gs
  (fun _ => @emptyT_any' stya _) (fun _ => @emptyT_any' styb _).

Check gen_step2_lem.

(* simplified versions, forget A, then derive version with A *)
Definition gen_steps (seq : Type) P derivs ps (concl : seq) := 
  ForallT (fun p => prod (derivs p) (P p)) ps -> derivs concl -> P concl.

Definition gen_step2s (seql seqr : Type) (P : seql -> seqr -> Type)
  dls drs psl cl psr cr :=
  ForallT (fun pl => prod (dls pl) (P pl cr)) psl -> 
  ForallT (fun pr => prod (drs pr) (P cl pr)) psr -> 
  dls cl -> drs cr -> P cl cr.

(* generalised version of inductive step proof *) 
Lemma gen_steps_lem_ps (sty : Type) (P : sty -> Type) rules prems: 
    (forall ps concl, rules ps concl ->
      gen_steps P (derrec rules prems) ps concl) -> 
    (forall prem, prems prem -> P prem) -> 
    (forall seq, derrec rules prems seq -> P seq).
Proof. intros until 0. intros gs prs. 
intros.  eapply derrec_all_rect. apply prs.
intros. unfold gen_steps in gs. eapply gs. exact X0.
apply ForallTI_forall. intros. split. 
eapply dersrecD_forall in X1 ; eassumption.
eapply ForallTD_forall in X2 ; eassumption.
eapply derI ; eassumption. exact X. Qed.

Definition gen_steps_lem sty P rules gs :=
  @gen_steps_lem_ps sty P rules (@emptyT sty) gs (@emptyT_any' sty P).

Lemma gen_step2s_lem_ps: forall (stya styb : Type) P
  rlsa rlsb (premsa : stya -> Type) (premsb : styb -> Type),
  (forall psa psb ca cb, rlsa psa ca -> rlsb psb cb -> 
  gen_step2s P (derrec rlsa premsa) (derrec rlsb premsb) psa ca psb cb) -> 
 (forall pa, premsa pa -> forall cb, derrec rlsb premsb cb -> P pa cb) -> 
 (forall pb, premsb pb -> forall ca, derrec rlsa premsa ca -> P ca pb) -> 
  forall seqa, derrec rlsa premsa seqa ->
  forall seqb, derrec rlsb premsb seqb -> P seqa seqb.
Proof. intros until 0. intros gs prsa prsb. 
eapply derrec_all_rect2.
- intros px ppx cy db. eapply prsa in db ; eassumption.
- intros py ppy cx da. eapply prsb in da ; eassumption.
- intros *. intros ra rb da db fx fy.
unfold gen_step2s in gs. eapply gs.
+ exact ra. + exact rb. 
+ apply ForallTI_forall. intros x inx. split. 
eapply dersrecD_forall in da ; eassumption.
eapply ForallTD_forall in fx ; eassumption.
+ apply ForallTI_forall. intros y iny. split. 
eapply dersrecD_forall in db ; eassumption.
eapply ForallTD_forall in fy ; eassumption.
+ eapply derI ; eassumption.
+ eapply derI ; eassumption. Qed.

Definition gen_step2s_lem stya styb P rlsa rlsb gs :=
  @gen_step2s_lem_ps stya styb P rlsa rlsb 
  (@emptyT stya) (@emptyT styb) gs
  (@emptyT_any' stya _) (@emptyT_any' styb _).

(* proof of version depending on formula A from versions not depending on A,
  showing this is possible, however, since this is difficult and
  proving (for example) gen_step2_lem_psT is not much harder
  than proving gen_step2s_lem_ps, might as welll use gen_step2_lem_psT *)
Lemma gen_step_lem' sty fty P (A : fty) sub rules:
  AccT sub A -> (forall A0 ps concl, rules ps concl ->
    gen_step P A0 sub (derrec rules (emptyT (X:=sty))) ps concl) ->
    forall seq : sty, derrec rules (emptyT (X:=sty)) seq -> P A seq.
Proof. intros acc gs. induction acc.
remember (fun s => (forall y, sub y x -> 
  forall seq, derrec rules (emptyT (X:=sty)) seq -> P y seq) -> P x s) as Q.
pose (@gen_steps_lem sty Q).
rewrite HeqQ in q. intros seq ds. eapply q. 2: apply ds.
all: cycle 1. intros y syx. eapply X. exact syx. 
clear q.  intros ps concl rpc.
eapply gs in rpc.  unfold gen_step in rpc.
unfold gen_steps.  intros ft drc sp. 
apply rpc. exact sp. 2: exact drc.
apply ForallTI_forall.  intros x0 inxp.
eapply ForallTD_forall in ft. 2: apply inxp. cD.
split. exact ft. apply ft0. exact sp. Qed.

(* alternative approach to admissibility, useful for swap in Box rule of K4,
  where single swap in conclusion requires two swaps in premises,
  which requires the _rtc;
  very easily extended to derl rules in def of can_trf_rules
  (though this doesn't give height preservation),
  can we extend this to reflexive transitive closure of R ?? *)

(* note - although we can't seem to be able to extend this to derl
  and reflexive transitive closure of R together,
  we do need reflexive closure of R together with
  a sort of reflexive closure of the rules, eg
  where R is that a certain rule can be inverted, 
  where the rule is that same rule, then we don't want a R step or
  a single rule application step; 
  for the K4 rule which allows weakening, where the formula to be
  inverted is among what is added, then the changed version is
  derived from the original premise, not from a related premise *)

Unset Universe Polymorphism.

Definition can_trf_rules (sty : Type) R rules (ps : list sty) (c : sty) :=
  forall c' : sty, R c c' -> 
  (sigT (fun ps' : list sty => prod (rules ps' c')
    (ForallT (fun p' => sigT (fun p => prod (InT p ps) (R p p'))) ps'))).

Definition can_trf_rules_rc (sty : Type) R rules (ps : list sty) (c : sty) :=
  forall c' : sty, R c c' -> 
  (sigT (fun ps' : list sty => prod (rules ps' c') (ForallT
    (fun p' => sigT (fun p => prod (InT p ps) (clos_reflT R p p'))) ps'))).

(* can_trf_rules_rc would be a bit pointless if we specified that
  ps to c is a rule, because then can_trf_rules R would imply
  can_trf_rules (clos_reflT R) *)

Lemma can_trf_rules_imp_rc sty R rules ps c:
  @can_trf_rules sty R rules ps c -> @can_trf_rules_rc sty R rules ps c.
Proof. unfold can_trf_rules. unfold can_trf_rules_rc.
intros. apply X in X0. cD. exists X0. split. assumption.
apply ForallTI_forall. intros.
eapply ForallTD_forall in X2. 2: eassumption. cD.
exists X2. split. assumption.
apply rT_step. assumption. Qed.

Lemma can_trf_rules_mono' sty R rulesa rulesb:
  rsub rulesa rulesb -> forall ps (c : sty), 
  can_trf_rules R rulesa ps c -> can_trf_rules R rulesb ps c.
Proof. unfold can_trf_rules.
intros. apply X0 in X1. clear X0. cD.
eexists.  split.  unfold rsub in X. apply X. apply X0. apply X2. Qed. 

Lemma can_trf_rules_rc_mono' sty R rulesa rulesb:
  rsub rulesa rulesb -> forall ps (c : sty), 
  can_trf_rules_rc R rulesa ps c -> can_trf_rules_rc R rulesb ps c.
Proof. unfold can_trf_rules_rc.
intros. apply X0 in X1. clear X0. cD.
eexists.  split.  unfold rsub in X. apply X. apply X0. apply X2. Qed. 

Definition can_trf_rules_mono sty R rulesa rulesb r :=
  rsubI _ _ (@can_trf_rules_mono' sty R rulesa rulesb r).
Definition can_trf_rules_rc_mono sty R rulesa rulesb r :=
  rsubI _ _ (@can_trf_rules_rc_mono' sty R rulesa rulesb r).

(* union of two relations *)
Polymorphic Inductive runion U V ra rb (ps : U) (c : V) : Type :=
  | run_l : ra ps c -> @runion U V ra rb ps c
  | run_r : rb ps c -> @runion U V ra rb ps c.

(* union of set of rule sets *)
Polymorphic Inductive rUnion U V rr (ps : U) (c : V) : Type :=
  | rUnI : forall r, rr r -> r ps c -> @rUnion U V rr ps c.

(* union property for R in can_trf_rules... *)
Lemma can_trf_rules_un sty R R' rules ps (c : sty):
  can_trf_rules R rules ps c -> can_trf_rules R' rules ps c ->
    can_trf_rules (runion R R') rules ps c.
Proof. unfold can_trf_rules. intros. destruct X1.
apply X in r. cD.  exists r. split. assumption.
apply ForallTI_forall.  intros. eapply ForallTD_forall in r1. cD.
exists r1.  split. assumption. apply run_l. eassumption. assumption.
apply X0 in r. cD.  exists r. split. assumption.
apply ForallTI_forall.  intros. eapply ForallTD_forall in r1. cD.
exists r1.  split. assumption. apply run_r. eassumption. assumption.
Qed.

(* Union property for R in can_trf_rules... *)
Lemma can_trf_rules_Un sty rr rules ps (c : sty):
  (forall r, rr r -> can_trf_rules r rules ps c) -> 
    can_trf_rules (rUnion rr) rules ps c.
Proof. unfold can_trf_rules. intros. destruct X0.
pose (X r r0 c' r1). cD. exists s. split. assumption.
apply ForallTI_forall.  intros. eapply ForallTD_forall in s1. cD.
exists s1. split. assumption.  eapply rUnI ; eassumption.  assumption. Qed.

Lemma can_trf_rules_req V R R' rules : req R R' -> forall ps c,
  @can_trf_rules V R rules ps c -> @can_trf_rules V R' rules ps c.
Proof. unfold can_trf_rules. unfold req. unfold rsub. 
intros ss ps c fri c' rcc. cD.
apply ss0 in rcc. apply fri in rcc. cD.
exists rcc. split. assumption. apply ForallTI_forall. intros.
eapply ForallTD_forall in rcc1. cD.
exists rcc1. split. assumption. apply ss. eassumption.  assumption. Qed.

Lemma der_trf_rc_adm: forall (sty : Type) R rules, 
  (forall ps c, rules ps c -> can_trf_rules_rc R (adm rules) ps c) ->
  forall concl, derrec rules (@emptyT sty) concl -> 
    forall concl', R concl concl' -> derrec rules (@emptyT sty) concl'.
Proof. intros until 0. intro. 
eapply (derrec_all_rect (Q := (fun concl => forall concl' : sty,
  R concl concl' -> derrec rules (emptyT (X:=sty)) concl'))).
intros. destruct H.
intros ps concl rpc dpss fall concl' Rcc.
apply X in rpc.  unfold can_trf_rules_rc in rpc.
apply rpc in Rcc. cD. clear rpc X.
(* here, weaker results by using derI or adm_derrec_trans
  instead of adm_derrec_trans *)
eapply adm_derrec_trans.  exact Rcc0.
apply dersrecI_forall. intros.
eapply ForallTD_forall in Rcc1. 2: eassumption.  cD.
inversion Rcc3. subst.
eapply ForallTD_forall in fall. 2: eassumption. 
apply fall. assumption.
subst.  eapply dersrecD_forall in dpss. exact dpss. assumption. Qed.

Check der_trf_rc_adm.

Lemma der_trf_rc_derl: forall (sty : Type) R rules, 
  (forall ps c, rules ps c -> can_trf_rules_rc R (derl rules) ps c) ->
  forall concl, derrec rules (@emptyT sty) concl -> 
    forall concl', R concl concl' -> derrec rules (@emptyT sty) concl'.
Proof. intros sty R rules rtc. apply der_trf_rc_adm.
intros ps c rpc. apply rtc in rpc.
eapply can_trf_rules_rc_mono'.
apply rsub_derl_adm. apply rpc. Qed.

Check der_trf_rc_derl.

Lemma der_trf_rc: forall (sty : Type) R rules, 
  (forall ps c, rules ps c -> can_trf_rules_rc R rules ps c) ->
  forall concl, derrec rules (@emptyT sty) concl -> 
    forall concl', R concl concl' -> derrec rules (@emptyT sty) concl'.
Proof. intros sty R rules rtc. apply der_trf_rc_adm.
intros ps c rpc. apply rtc in rpc.
eapply can_trf_rules_rc_mono'.
apply rsub_adm. apply rpc. Qed. 

Check der_trf_rc.  

Lemma der_trf_derl: forall (sty : Type) R rules, 
  (forall ps c, rules ps c -> can_trf_rules R (derl rules) ps c) ->
  forall concl, derrec rules (@emptyT sty) concl -> 
    forall concl', R concl concl' -> derrec rules (@emptyT sty) concl'.
Proof. intros until 0. intro. 
apply der_trf_rc_derl. intros. apply can_trf_rules_imp_rc.
exact (X ps c X0). Qed.

(* or can do the following *)
Definition der_trf_derl' sty R rules ct :=
  @der_trf_rc_derl sty R rules 
    (fun ps c rpc => can_trf_rules_imp_rc (ct ps c rpc)).
  
Check der_trf_derl.

Lemma can_trf_derl X rules R ps (c : X): can_trf_rules R rules ps c ->
    can_trf_rules R (derl rules) ps c.
Proof. unfold can_trf_rules. intros.
apply X0 in X1. cD. exists X1. split. apply in_derl. assumption. 
assumption. Qed.  

Lemma der_trf: forall (sty : Type) R rules, 
  (forall ps c, rules ps c -> can_trf_rules R rules ps c) ->
  forall concl, derrec rules (@emptyT sty) concl -> 
    forall concl', R concl concl' -> derrec rules (@emptyT sty) concl'.
Proof. intros until 0. intro rct. apply der_trf_derl.
intros. apply can_trf_derl. apply rct. assumption. Qed.

Check der_trf.  

Definition can_trf_rules_rtc (sty : Type) R rules (ps : list sty) (c : sty) :=
  forall c' : sty, R c c' -> 
  (sigT (fun ps' : list sty => prod (rules ps' c')
    (ForallT (fun p' => sigT (fun p => prod (InT p ps) 
      (clos_refl_transT_n1 R p p'))) ps'))).

Lemma can_trf_rules_imp_rtc sty R rules ps c:
  @can_trf_rules sty R rules ps c -> @can_trf_rules_rtc sty R rules ps c.
Proof. unfold can_trf_rules. unfold can_trf_rules_rtc.
intros. apply X in X0. cD. exists X0. split. assumption.
apply ForallTI_forall. intros.
eapply ForallTD_forall in X2. 2: eassumption. cD.
exists X2. split. assumption.
eapply rtn1T_trans. eassumption. apply rtn1T_refl. Qed.

Lemma can_trf_rules_rtc_mono' sty R rulesa rulesb ps c:
  rsub rulesa rulesb -> @can_trf_rules_rtc sty R rulesa ps c ->
  @can_trf_rules_rtc sty R rulesb ps c.
Proof. unfold rsub. unfold can_trf_rules_rtc. intros. 
apply X0 in X1. clear X0. cD. exists X1. split. firstorder.
exact X2. Qed.

Definition can_trf_rules_rtc_mono sty R rulesa rulesb r :=
  rsubI _ _ (@can_trf_rules_rtc_mono' sty R rulesa rulesb r).

Lemma trf_rules_rtc: forall (sty : Type) R rules (c : sty), 
  (forall ps' c', clos_refl_transT_n1 R c c' -> 
    rules ps' c' -> can_trf_rules_rtc R rules ps' c') ->
  forall ps, rules ps c -> can_trf_rules (clos_refl_transT_n1 R) rules ps c.
Proof. intros. unfold can_trf_rules. intro. intro rtc.
induction rtc. exists ps. split. assumption.
apply ForallTI_forall. intros. exists x. split. assumption.
apply rtn1T_refl.
cD. eapply X in rtc.
unfold can_trf_rules_rtc in rtc. apply rtc in r. clear rtc. cD.
eexists. split. eassumption.  
apply ForallTI_forall. intros.
eapply ForallTD_forall in r1. 2: eassumption. cD.
eapply ForallTD_forall in IHrtc1. 2: eassumption. cD.
eexists. split. eassumption.  
(* now need transitivity of clos_refl_transT_n1 *)
apply clos_rtn1_rtT in r3.
apply clos_rtn1_rtT in IHrtc3.
apply clos_rt_rtn1T.
eapply rtT_trans ; eassumption. assumption. Qed.

Check trf_rules_rtc.

(* try to adapt proof of trf_rules_derl to also do _rtc 
Lemma trf_rules_rtc_derl: forall (sty : Type) R (rules : rlsT sty), 
  (forall ps c, rules ps c -> can_trf_rules_rtc R (derl rules) ps c) ->
  (forall ps c, derl rules ps c -> 
    can_trf_rules (clos_refl_transT_n1 R) (derl rules) ps c).
NOT ACTUALLY SURE THIS IS VALID
Check trf_rules_rtc_derl.
*)

Lemma trf_rules_derl: forall (sty : Type) R (rules : rlsT sty), 
  (forall ps c, rules ps c -> can_trf_rules R (derl rules) ps c) ->
  (forall ps c, derl rules ps c -> can_trf_rules R (derl rules) ps c).
Proof. intros until 0.  intro rctd.
eapply derl_all_rect.
{ intro. unfold can_trf_rules. intros. exists [c'].
split. apply asmI. apply ForallTI_forall. intros.
exists p. split. apply InT_eq. inversion X0 ; subst. assumption.
eapply InT_nilE in X1. eassumption. }

{ intros until 0. intros rpc drsl fcd qcp.
apply rctd in rpc.  subst. clear rctd.
unfold can_trf_rules. intros c' Rcc.
unfold can_trf_rules in rpc. apply rpc in Rcc. cD. clear rpc. 

assert {cqss : list sty &
  (dersl rules cqss Rcc * ForallT (fun p' : sty =>
    {p : sty & InT p (concat pss) * R p p'}) cqss)%type}.

{ clear Rcc0. induction Rcc1.
exists []. simpl. split. apply dtNil. apply ForallT_nil.
cD.
eapply Forall2T_ex_r in fcd. 2: eassumption. destruct fcd.
unfold can_trf_rules in c. eapply c in p1. clear c.
destruct p1. cD. 
eexists. split.  eapply dtCons ; eassumption.
apply ForallTI_forall. simpl. intros.
apply InT_appE in X. sD.
eapply ForallTD_forall in p2. 2: eassumption. cD.
eexists. split. 2: eassumption. 
eapply InT_concat ; eassumption.
eapply ForallTD_forall in IHRcc2. 2: eassumption. assumption. }

{ cD. eexists. split. 2: eassumption.
eapply derl_trans ; eassumption.  } } Qed.

Check trf_rules_derl.

Lemma der_trf_rtc: forall (sty : Type) R rules, 
  (forall ps c, rules ps c -> can_trf_rules_rtc R rules ps c) ->
  forall concl, derrec rules (@emptyT sty) concl -> 
    forall concl', clos_refl_transT_n1 R concl concl' -> 
    derrec rules (@emptyT sty) concl'.
Proof. intros until 1.  apply der_trf.
intros until 0. apply trf_rules_rtc.
intros until 1. apply X. Qed.

Check der_trf_rtc.

(* how to do this - maybe need to try _rtc variant of trf_rules_derl 
Lemma der_trf_rtc_derl: forall (sty : Type) R rules, 
  (forall ps c, rules ps c -> can_trf_rules_rtc R (derl rules) ps c) ->
  forall concl, derrec rules (@emptyT sty) concl -> 
    forall concl', clos_refl_transT_n1 R concl concl' ->
      derrec rules (@emptyT sty) concl'.
*)

Lemma der_trf_ht: forall (sty : Type) R rules, 
  (forall ps c, rules ps c -> can_trf_rules R rules ps c) ->
  forall concl (D : derrec rules (@emptyT sty) concl), 
    forall concl', R concl concl' -> 
    sigT (fun D' : derrec rules (@emptyT sty) concl' => 
      derrec_height D' <= derrec_height D).
Proof. intros until 0. intros ctr.
eapply (derrec_rect_mut_all (Q := (fun concl D => forall concl' : sty,
  R concl concl' -> {D' : derrec rules (emptyT (X:=sty)) concl' &
  derrec_height D' <= derrec_height D}))).
intros c p. destruct p.
intros ps concl rpc dpss apd concl' Rcc.
pose (ctr ps concl rpc) as ctrr.
unfold can_trf_rules in ctrr.
apply ctrr in Rcc. cD. clear ctrr ctr.

assert { Ds' : dersrec rules (emptyT (X:=sty)) Rcc &
  dersrec_height Ds' <= dersrec_height dpss }.
assert (forall p, InT p Rcc -> { D' : derrec rules (emptyT (X:=sty)) p &
  derrec_height D' <= dersrec_height dpss }).

{ intros.
eapply ForallTD_forall in Rcc1.  2: eassumption.  cD. 
eapply allPderD_in in apd. 2: eassumption. destruct apd. (* cD doesn't work *)
apply s in Rcc3. cD. clear s.
eexists. (* shelves a goal *) 
eapply le_dersrec_height. eassumption. eassumption. }

{ clear apd concl' Rcc0 Rcc1 R rpc.
(* this may be a useful lemma *)
induction Rcc. eexists. Unshelve. 3: apply dlNil. simpl. apply le_0_n.
require IHRcc. intros. apply X. apply InT_cons. assumption. cD.
pose (X a (InT_eq a Rcc)). cD. 
exists (dlCons s IHRcc). simpl. apply Nat.max_lub ; assumption. }

cD.  exists (derI concl' Rcc0 X). simpl.  apply le_n_S. assumption. Qed.

Check der_trf_ht.

(* this proof gets quite unmanageable, need to use @dersrecI_forall' instead,
  which is a much simpler proof object 
Goal forall X rules prems seq seqs f,
  @dersrecI_forall X rules prems (seq :: seqs) f =
  @dlCons X rules prems seq seqs (f seq (InT_eq seq seqs))
    (@dersrecI_forall X rules prems seqs (fun c i => f c (InT_cons seq i))).
Proof. intros.  
unfold dersrecI_forall.  unfold dersrec_forall.
unfold iffT_D2.  unfold prod_rect.  unfold iffT_trans.
(etc, can do lots of unfolds)
*)

Lemma dlCons_inj: forall X rules prems seq seqs d ds d' ds',
  @dlCons X rules prems seq seqs d ds = dlCons d' ds' ->
  prod (d = d') (ds = ds').
(* shorter proof follows 
Proof. intros.  injection H. intros. inversion_sigma. 
unfold eq_rect in H3.  unfold eq_rect in H4. 
dependent destruction H2.  dependent destruction H1.
split ; assumption. Defined.
*)
Proof. intros. dependent destruction H. tauto. Defined.

Check dlCons_inj.

(* formerly managed to prove these
Lemma dersrecI_forall_alt_cons: forall X rules prems seq seqs f,
  @dersrecI_forall X rules prems (seq :: seqs) f =
  @dlCons X rules prems seq seqs (f seq (InT_eq seq seqs))
    (@dersrecI_forall X rules prems seqs (fun c i => f c (InT_cons seq i))).

Lemma dersrecI_forall_alt_nil: forall X rules prems f,
  @dersrecI_forall X rules prems [] f = @dlNil X rules prems.

Lemma dlc_drsf: forall X rules prems seq seqs d ds f,
  @dlCons X rules prems seq seqs d ds = 
    @dersrecI_forall X rules prems (seq :: seqs) f -> 
  prod (d = f seq (InT_eq seq seqs)) 
  (ds = @dersrecI_forall X rules prems seqs (fun c i => f c (InT_cons seq i))).
*)

Lemma existT_inj: forall A P (x : A) px px',
  existT P x px = existT P x px' -> (px = px').
Proof. intros. dependent destruction H. tauto. Defined.

Lemma existT_inj': forall A P (x x' : A) px px',
  existT P x px = existT P x' px' -> (x = x').
Proof. intros. dependent destruction H. tauto. Defined.

(* Print Assumptions existT_inj. 
Fetching opaque proofs from disk for Coq.Logic.EqdepFacts
Axioms:
Eqdep.Eq_rect_eq.eq_rect_eq : forall (U : Type) (p : U) 
                                (Q : U -> Type) (x : Q p) 
                                (h : p = p), x = eq_rect p Q x p h
JMeq_eq : forall (A : Type) (x y : A), x ~= y -> x = y
*)

(* soundness proofs *)

(* according to some semantics, if each rule preserves validity
  then a derivation preserves validity *)
(* note - proof doesn't work using derl instead of dercl *)
Lemma dercl_soundness W rules valid 
  (rules_sound : forall ps c, rules ps c -> ForallT valid ps -> valid c) :
  forall ps (c : W), dercl rules ps c -> ForallT valid ps -> valid c.
Proof. 
apply (@dercl_all_rect _ _ (fun ps c => ForallT valid ps -> valid c)).
- intros p fvps. exact (ForallT_singleD fvps).
- intros * rpsc dcsl fvv qseq fvqs. subst.
eapply rules_sound. exact rpsc.
clear rpsc dcsl. (* otherwise spoils induction *)
induction fvv. apply ForallT_nil.
simpl in fvqs.  apply ForallT_appendD in fvqs. destruct fvqs.
exact (ForallT_cons y (r f) (IHfvv f0)).
Qed.

Lemma derrec_soundness W rules prems valid 
  (rules_sound : forall ps (c : W), rules ps c -> ForallT valid ps -> valid c) :
  (forall p, prems p -> valid p) -> forall c, derrec rules prems c -> valid c.
Proof. intro pv.  apply (derrec_all_rect pv).
intros * rps drs. exact (rules_sound ps concl rps). Qed.
  
Unset Universe Polymorphism.

(* useful predicates for proving admissibility *)
(* extend the idea of admissibility to relations *)
Inductive radm X rules p c : Type :=
  | radmI : (derrec rules (@emptyT X) p -> derrec rules (@emptyT X) c) ->
    radm X rules p c.

Definition radmD X rules p c (r : @radm X rules p c) :=
  match r with | radmI d => d end.

(* admissibility for a relation *)
Inductive rel_adm X rules R : Type :=
  | rel_admI : (forall p c, R p c -> @radm X rules p c) -> rel_adm X rules R.

Definition rel_admD X rules R (r : @rel_adm X rules R) :=
  match r with | rel_admI _ r0 => r0 end.

(* similar to rel_adm, but useful for gen_step_lemT *)
Definition can_rel sty fty rules (R : fty -> sty -> sty -> Type)
  (fml : fty) (seq : sty) :=
  forall seq', R fml seq seq' -> derrec rules emptyT seq'.

Lemma rel_adm_rtc X rules R :
  @rel_adm X rules R -> rel_adm rules (clos_refl_transT R).
Proof. repeat split.  destruct X0.
induction X1.  exact (radmD (r x y r0)).  tauto. tauto. Qed.

(* lemma relating rel_adm to can_rel *)
Lemma crd_ra sty fty rules (R : fty -> sty -> sty -> Type) fml:
  iffT (rel_adm rules (R fml))
  (forall seq, derrec rules emptyT seq -> can_rel rules R fml seq).
Proof. split.
- intros ra seq ds seq' rf.
inversion ra. specialize (X seq seq' rf).
destruct X. exact (d ds).
- intro dc. repeat split. intro dp.
exact (dc p dp c X). Qed.


