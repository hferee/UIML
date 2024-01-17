
(** results relating to derivation trees (derrec, dersrec) as data structures,
  like Isabelle dertrees, rather than purely as properties of conclusions,
  including use of derrec_fc ie without the conclusion as part of the type **)

Require Export List.
Set Implicit Arguments.
Export ListNotations.

Require Import Coq.Program.Equality. (* for dependent induction/destruction *)

Require Import genT gen ddT existsT.
Require Import PeanoNat.
Require Import Lia.

(* tried to do an inductive property where property Q also involved the 
proof tree (as well as the endsequent): this created a problem that
the list of proof trees which are part of the dersrec object are not 
all of the same type - so one cannot go from 
ds : dersrec rules prems concls to ForallT (dersrec rules prems ??) ds'
instead need to define allPder and do the following *)

Inductive allPder X (rules : rlsT X) (prems : X -> Type) P : 
  forall concls : list X, dersrec rules prems concls -> Type :=
  | allPder_Nil : @allPder X rules prems P [] (dlNil rules prems)
  | allPder_Cons : forall seq seqs d, P seq d -> forall ds, 
    @allPder X rules prems P seqs ds -> 
    @allPder X rules prems P (seq :: seqs) (dlCons d ds)
  .

Lemma allPderD : forall X rules prems Q ps (dpss : dersrec rules prems ps) p,
  allPder Q dpss -> InT (p : X) ps -> {d : derrec rules prems p & Q p d}.
Proof. induction ps.
intros. inversion X1.
intros dpss p adp inp. inversion adp. subst. 
inversion inp ; subst.
exists d. assumption.
clear X0 inp adp. exact (IHps ds p X1 X2).  Qed.

(* destruct for allPder dlCons *)
Lemma allPder_dlConsD: forall X rules prems Q seq seqs d ds,
  @allPder X rules prems Q (seq :: seqs) (dlCons d ds) ->
    Q seq d * allPder Q ds.
Proof.
intros. (* inversion X0 produces existT equalities *)
(* induction X0 produces trivial subgoal 2, unsolvable subgoal 1 *)
(* dependent induction X0. OK, but irrelevant IHX0, trivial subgoal *)
dependent destruction X0. 
split ; assumption. Qed.

Definition derrec_rect_mut_all X (rules : rlsT X) prems Q cl1 cl2 :=
  derrec_rect_mut Q (@allPder X rules prems Q) cl1 cl2 
    (allPder_Nil Q) (@allPder_Cons X rules prems Q).
(*
Check derrec_rect_mut_all.
*)
Inductive in_dersrec X (rules : rlsT X) prems concl 
  (d : derrec rules prems concl) : 
  forall concls, dersrec rules prems concls -> Type :=
  | in_dersrec_hd : forall concls ds, in_dersrec d 
    (@dlCons X rules prems concl concls d ds)
  | in_dersrec_tl : forall concl' d' concls ds, in_dersrec d ds -> 
    in_dersrec d (@dlCons X rules prems concl' concls d' ds)
  .

Inductive is_nextup X (rules : rlsT X) prems (concl : X) (concls : list X)  
  (ds : dersrec rules prems concls) : derrec rules prems concl -> Type :=
  | is_nextupI : forall rps, is_nextup ds (derI concl rps ds) 
  (* can't make this next line work
  | is_nextup_nil : is_nextup (dlNil rules prems) (dpI _ _ _ _) 
  *)
  .

Inductive in_nextup X (rules : rlsT X) prems (concln concl : X) 
  (dn : derrec rules prems concln) (d : derrec rules prems concl) : Type :=
  | in_nextupI : forall concls (ds : dersrec rules prems concls),
      is_nextup ds d -> in_dersrec dn ds -> in_nextup dn d
  .

Lemma in_drs_concl_in W rules ps (cn : W) (drs : dersrec rules emptyT ps)
  (dtn : derrec rules emptyT cn) : in_dersrec dtn drs -> InT cn ps.
Proof. intro ind. induction ind. apply InT_eq.
apply InT_cons. assumption. Qed.

Lemma in_nextup_concl_in W rules ps (concl cn : W) rpc
  (drs : dersrec rules emptyT ps) (dtn : derrec rules emptyT cn) :
  in_nextup dtn (derI concl rpc drs) -> InT cn ps.
Proof. intro ind. inversion ind. inversion X. subst.
dependent destruction H2. clear H1 rps0 ind X.
exact (in_drs_concl_in X0). Qed.

Lemma all_in_d_allP: forall X rules prems Q ps (dpss : dersrec rules prems ps),
  (forall (p : X) (d : derrec rules prems p), in_dersrec d dpss -> Q p d) -> 
  allPder Q dpss.
Proof.  induction dpss. intros. apply allPder_Nil.
intros.  apply allPder_Cons.  apply X0. apply in_dersrec_hd.
apply IHdpss.  intros. apply X0. apply in_dersrec_tl. assumption. Qed.
(* alternative proof, longer, shows need to use dependent inversion 
Proof. induction ps. intros. dependent inversion dpss. apply allPder_Nil.
intro. dependent inversion dpss. subst. 
intros.  apply allPder_Cons. apply X0. apply in_dersrec_hd.
apply IHps. intros. apply X0. apply in_dersrec_tl. assumption. Qed.
*)

Lemma allP_all_in_d: forall X rules prems Q ps (dpss : dersrec rules prems ps),
  allPder Q dpss -> 
  forall (p : X) (d : derrec rules prems p), in_dersrec d dpss -> Q p d.  
Proof. induction ps. intro. dependent inversion dpss.
intros. inversion X1.
intro. dependent inversion dpss. subst.
intro. (* inversion X0 gives existT equalities *)
dependent destruction X0.
intros. (* inversion X1 gives existT equalities *) 
dependent destruction X1. assumption.
eapply IHps. eassumption. assumption. Qed.

Lemma allPderD_in :
  forall X rules prems Q ps (dpss : dersrec rules prems ps) p,
    allPder Q dpss -> InT (p : X) ps ->
      {d : derrec rules prems p & in_dersrec d dpss & Q p d}.
Proof. induction ps.
intros. inversion X1.
intros dpss p adp inp. dependent destruction adp.
inversion inp ; subst.
exists d.  apply in_dersrec_hd.  assumption.
pose (IHps ds p adp X0). destruct s. (* cD doesn't work here - why?? *)
exists x. apply in_dersrec_tl. assumption.  assumption. Qed.
(*
Check allPderD_in.
*)
Fixpoint derrec_height X rules prems concl 
  (der : @derrec X rules prems concl) :=
  match der with 
    | dpI _ _ _ _ => 0
    | derI _ _ ds => S (dersrec_height ds)
  end
with dersrec_height X rules prems concls
  (ders : @dersrec X rules prems concls) :=
  match ders with 
    | dlNil _ _ => 0
    | dlCons d ds => max (derrec_height d) (dersrec_height ds)
  end.

Print derI.

Fixpoint derrec_size X rules prems concl 
  (der : @derrec X rules prems concl) :=
  match der with 
    | dpI _ _ _ _ => 0
    | derI _ _ ds => S (dersrec_size ds)
  end
with dersrec_size X rules prems concls
  (ders : @dersrec X rules prems concls) :=
  match ders with 
    | dlNil _ _ => 0
    | dlCons d ds => (derrec_size d) + (dersrec_size ds)
  end.

Fixpoint derrec_concl X rules prems concl 
  (der : @derrec X rules prems concl) :=
  match der with 
    | dpI _ _ c _ => c
    | derI c _ _ => c
  end.

Fixpoint dersrec_concls X rules prems concls
  (ders : @dersrec X rules prems concls) :=
  match ders with 
    | dlNil _ _ => []
    | dlCons d ds => derrec_concl d :: dersrec_concls ds
  end.

Fixpoint der_botr_ps X rules prems concl 
  (der : @derrec X rules prems concl) :=
  match der with 
    | dpI _ _ _ _ => []
    | @derI _ _ _ ps _ _ _ => ps
  end.

(* see coq-club emails 25/4/20 *)
Fixpoint dersrec_hd X rules prems c cs
  (ders : @dersrec X rules prems (c :: cs)) {struct ders} :=
  match ders with 
    | dlCons d ds => d
  end.

Fixpoint dersrec_tl X rules prems c cs
  (ders : @dersrec X rules prems (c :: cs)) {struct ders} :=
  match ders with 
    | dlCons d ds => ds
  end.

Definition dersrec_singleD' X rules prems c 
  (ders : @dersrec X rules prems [c]) := dersrec_hd ders.

Definition dersrec_singleI' X rules prems c
  (d : @derrec X rules prems c) := dlCons d (@dlNil X rules prems).

Definition dersrec_single' X rules prems c := 
  (@dersrec_singleD' X rules prems c, @dersrec_singleI' X rules prems c).

(*
Lemma in_dersrec_single X rs ps c (ds : @dersrec X rs ps [c]) :
  in_dersrec (dersrec_singleD ds) ds.
Proof. dependent destruction ds.  (* dependent induction ds. also seems OK *)
HOW TO CONTINUE PROOF ?? NB works better for dersrec_singleD'
*)

Lemma botr_ps_der W rules prems c (d : derrec rules prems c) :
  @dersrec W rules prems (der_botr_ps d).
Proof. destruct d ; simpl. apply dlNil. apply d. Qed.

Lemma in_dersrec_single' X rs ps c (ds : @dersrec X rs ps [c]) :
  in_dersrec (dersrec_singleD' ds) ds.
Proof. dependent destruction ds.  (* dependent induction ds. also seems OK,
but dependent inversion gives a type error *)
unfold dersrec_singleD'.  simpl.  apply in_dersrec_hd.  Qed.

(* can't do this, gives The term "ds" has type "dersrec rules prems l"
  while it is expected to have type "dersrec rules prems []".  
Fixpoint derrec_nextup X rules prems concl
  (der : @derrec X rules prems concl) :=
  match der with 
    | dpI _ _ _ _ => dlNil rules prems 
    | derI _ _ ds => ds
  end.
*)

Lemma dersrec_hd_eq X rs ps c cs
  (d : @derrec X rs ps c) (ds : @dersrec X rs ps cs) :
  dersrec_hd (dlCons d ds) = d.
Proof. simpl. reflexivity.  Qed.

Lemma dersrec_tl_eq X rs ps c cs
  (d : @derrec X rs ps c) (ds : @dersrec X rs ps cs) :
  dersrec_tl (dlCons d ds) = ds.
Proof. simpl. reflexivity.  Qed.

Lemma in_drs_drs_hd X rs ps c cs (ds : @dersrec X rs ps (c :: cs)) :
  in_dersrec (dersrec_hd ds) ds.
Proof. dependent destruction ds.  (* dependent induction ds. also seems OK *)
simpl. apply in_dersrec_hd.  Qed.

Lemma dersrec_height_nil : forall X rules prems ps (ds : @dersrec X rules prems ps),
    ps = [] -> dersrec_height ds = 0.
Proof.
induction ds.
- simpl. reflexivity.
- intro. inversion H.
Qed.

Lemma dersrec_height_le: forall X rules prems n ps 
  (ds : dersrec rules prems ps),
  (forall (p : X) (d : derrec rules prems p),
  in_dersrec d ds -> derrec_height d <= n) -> dersrec_height ds <= n.
Proof. (* induction ps. 
intros. inversion ds.  this step seems to do nothing *)
induction ds. 
intros.  simpl. apply le_0_n. 
intros.  simpl.  apply Nat.max_lub.
apply H. apply in_dersrec_hd.
apply IHds.  intros. apply H.  apply in_dersrec_tl. assumption. Qed.

Lemma le_dersrec_height: forall X rules prems n ps 
  (ds : dersrec rules prems ps),
  forall (p : X) (d : derrec rules prems p),
  in_dersrec d ds -> n <= derrec_height d -> n <= dersrec_height ds.
Proof. (* induction ps. 
intros. inversion ds.  this step seems to do nothing *)
(* this doesn't work - why ??
induction ds ; intros ; inversion X0 ; subst ; simpl ; rewrite Nat.max_le_iff.
left. assumption.
right.  eapply IHds. 2: eassumption.
WHAT NOW ???
*)
intros. induction X0 ; simpl ; rewrite Nat.max_le_iff ; tauto. Qed.

(*
Fixpoint aderrec_height X 
  (rules : list X -> X -> Prop) (prems : X -> Prop) concl 
  (der : @aderrec X rules prems concl) :=
  match der with 
    | adpI _ _ _ _ => 0
    | aderI _ _ _ => 0
  end.
  *)

Fixpoint derl_height X 
  (rules : list X -> X -> Prop) (prems : list X) (concl : X) 
  (der : @derl X rules prems concl) :=
  match der with 
    | asmI _ _ => 0
    | dtderI _ _ ds => S (dersl_height ds)
  end
with dersl_height X (rules : list X -> X -> Prop) (prems concls : list X) 
  (ders : @dersl X rules prems concls) :=
  match ders with
    | dtNil _ => 0
    | dtCons d ds => max (derl_height d) (dersl_height ds)
  end.

Lemma der_concl_eq: forall X (rules : rlsT X) prems concl 
  (d : derrec rules prems concl), derrec_concl d = concl.
Proof. dependent inversion d ; simpl ; reflexivity. Qed.

Lemma ders_concls_eq: forall X (rules : rlsT X) prems concls 
  (ds : dersrec rules prems concls), dersrec_concls ds = concls.
Proof. induction ds ; simpl.  reflexivity.
rewrite -> (der_concl_eq d). rewrite IHds. reflexivity. Qed.

(** der(s)rec_fc(s) - trees without conclusion as part of the type **)

Inductive derrec_fc X rules (prems : X -> Type) : Type := 
  | fcI : forall concl, derrec rules prems concl -> derrec_fc rules prems.

Inductive dersrec_fcs X rules (prems : X -> Type) : Type := 
  | fcsI : forall concls, dersrec rules prems concls -> dersrec_fcs rules prems.

Inductive in_nextup_fc X (rules : rlsT X) prems :
    relationT (derrec_fc rules prems) :=
  | in_nextup_fcI : forall concln concl 
    (dn : derrec rules prems concln) (d : derrec rules prems concl),
    in_nextup dn d -> in_nextup_fc (fcI dn) (fcI d)
  .

Lemma AccT_in_nextup_fc X rules prems dt: AccT (@in_nextup_fc X rules prems) dt.
Proof. destruct dt. revert d. revert concl.
eapply derrec_rect_mut_all.
- intros. apply AccT_intro. intros y iny.
dependent destruction iny. inversion i.  inversion X0.
- intros * apd. apply AccT_intro.  intros y iny.
dependent destruction iny. inversion i. dependent destruction X0.
exact (allP_all_in_d apd X1). Qed.

Fixpoint dersrec_trees X rules prems concls
  (ders : @dersrec X rules prems concls) :=
  match ders with 
    | dlNil _ _ => []
    | dlCons d ds => fcI d :: dersrec_trees ds
  end.

Definition nextup W rules prems (dt : @derrec_fc W rules prems) :=
  match dt with 
    | fcI (dpI _ _ _ _) => []
    | fcI (derI _ _ ds) => dersrec_trees ds
  end.

Fixpoint derrec_fc_concl X rules prems 
  (der : @derrec_fc X rules prems) :=
  match der with 
    | fcI d => derrec_concl d
  end.

Fixpoint dersrec_fc_concls X rules prems 
  (ders : @dersrec_fcs X rules prems) :=
  match ders with 
    | fcsI ds => dersrec_concls ds
  end.

(* note, this includes case where the tree is simply a premise *)
Inductive botRule_fc X rules prems (der : @derrec_fc X rules prems) : rlsT X :=
  | botRule_fcI : botRule_fc der
    (map (@derrec_fc_concl _ _ _) (nextup der)) (derrec_fc_concl der).

(* this fails, d has type "derrec rules prems x", but x not in scope
Fixpoint derrec_of_fc X rules prems 
  (der : @derrec_fc X rules prems) :=
  match der with 
    | fcI d => d
  end.
  *)


(* while we can't get something of type derrec rules prems _
  from something of type derrec_fc ..., we can get it and then
  apply any function to it whose result type doesn't involve the conclusion *)
Fixpoint derrec_fc_size X rules prems 
  (der : @derrec_fc X rules prems) :=
  match der with 
    | fcI d => derrec_size d
  end.

Fixpoint dersrec_fc_size X rules prems 
  (ders : @dersrec_fcs X rules prems) :=
  match ders with 
    | fcsI ds => dersrec_size ds
  end.

Fixpoint derrec_fc_height X rules prems 
  (der : @derrec_fc X rules prems) :=
  match der with 
    | fcI d => derrec_height d
  end.

Fixpoint dersrec_fc_height X rules prems 
  (ders : @dersrec_fcs X rules prems) :=
  match ders with 
    | fcsI ds => dersrec_height ds
  end.

Lemma der_fc_concl_eq: forall X (rules : rlsT X) prems concl 
  (d : derrec rules prems concl), derrec_fc_concl (fcI d) = concl.
Proof. simpl. apply der_concl_eq. Qed.

Lemma dersrec_trees_concls_eq X rules prems ps (ds : dersrec rules prems ps) :
  map (@derrec_fc_concl X rules prems) (dersrec_trees ds) = ps.
Proof. induction ds.  simpl. reflexivity.
simpl. rewrite (der_concl_eq d). rewrite IHds. reflexivity. Qed.

Lemma der_botr_ps_eq X rules prems c (dt : derrec rules prems c) :
  map (@derrec_fc_concl X rules prems) (nextup (fcI dt)) = der_botr_ps dt.
Proof. destruct dt ; simpl.  reflexivity. apply dersrec_trees_concls_eq. Qed.

Lemma der_der_fc X rules prems (der : @derrec_fc X rules prems) :
  derrec rules prems (derrec_fc_concl der).
Proof. destruct der. simpl. rewrite der_concl_eq. exact d. Qed. 

Lemma ders_ders_fcs X rules prems (ders : @dersrec_fcs X rules prems) :
  dersrec rules prems (dersrec_fc_concls ders).
Proof. destruct ders. simpl. rewrite ders_concls_eq. exact d. Qed. 

Lemma in_drs_trees: forall X rules prems cs ds c (d : derrec rules prems c),
  in_dersrec d ds -> InT (fcI d) (@dersrec_trees X rules prems cs ds).
Proof. intros. induction X0 ; simpl. 
apply InT_eq.  apply InT_cons. assumption. Qed. 

Lemma in_trees_drs: forall X rules prems cs ds c (d : derrec rules prems c),
  InT (fcI d) (@dersrec_trees X rules prems cs ds) -> in_dersrec d ds.
Proof. induction cs ; intro ; dependent inversion ds ; simpl ; intros.
inversion X0.
(* inversion X0. injection H2. gives existT equality *)
subst.  dependent destruction X0. apply in_dersrec_hd.
apply in_dersrec_tl. apply IHcs. assumption. Qed.

Lemma der_botRule W rules (dt : derrec_fc rules emptyT) :
  {ps : list W & {c : W & rules ps c & botRule_fc dt ps c}}.
Proof. destruct dt. destruct d. destruct e.
exists ps. exists concl. exact r.
pose botRule_fcI.
specialize (b W rules emptyT (fcI (derI concl r d))).
simpl in b. rewrite dersrec_trees_concls_eq in b. exact b. Qed.

Lemma botRule_fc_concl W rules prems ps (c : W) (dt : derrec_fc rules prems) :
  botRule_fc dt ps c -> derrec_fc_concl dt = c.
Proof. intro br. destruct br. reflexivity. Qed.

Lemma botRule_fc_rules W rules ps (c : W) (dt : derrec_fc rules emptyT) :
  botRule_fc dt ps c -> rules ps c.
Proof. intro br. destruct br. destruct dt.
rewrite (der_fc_concl_eq d).
destruct d. destruct e. simpl.
rewrite (dersrec_trees_concls_eq d). exact r.  Qed.

Lemma botRule_fc_drs W rules prems ps (c : W) (dt : derrec_fc rules prems) :
  botRule_fc dt ps c -> dersrec rules prems ps.
Proof. intro br. destruct br. destruct dt.
destruct d.  simpl. apply dlNil.
simpl.  rewrite (dersrec_trees_concls_eq d). exact d.  Qed.

Lemma botRule_fc_ps W rules prems ps (c : W) (dt : derrec_fc rules prems) :
  botRule_fc dt ps c -> map (@derrec_fc_concl W rules prems) (nextup dt) = ps.
Proof. intro br. destruct br. destruct dt. reflexivity. Qed.

Lemma get_botrule W rules prems (c : W) (dt : derrec rules prems c) :
  botRule_fc (fcI dt) (der_botr_ps dt) c.
Proof. rewrite <- der_botr_ps_eq.
  eapply eq_rect. apply botRule_fcI.  apply der_fc_concl_eq. Qed.

Definition bot_is_rule W rules (c : W) (dt : derrec rules emptyT c) :=
  botRule_fc_rules (get_botrule dt).

Lemma botRule_fc_prems W rules prems (c : W) (dt : derrec rules prems c) ps c' :
  botRule_fc (fcI dt) ps c' -> (c = c') * (der_botr_ps dt = ps).
Proof. intro br. rewrite <- der_botr_ps_eq.  rewrite (botRule_fc_ps br).
split.  destruct br.  rewrite der_fc_concl_eq. reflexivity. reflexivity. Qed.

Lemma in_nextup_eqv W rules prems (concln concl : W) 
  (dtn : derrec rules prems concln) (dt : derrec rules prems concl) :
  iffT (in_nextup dtn dt) (InT (fcI dtn) (nextup (fcI dt))).
Proof. apply pair ; intros.
- destruct X. destruct i. simpl. exact (in_drs_trees i0).
- simpl in X. destruct dt. inversion X. 
  apply in_trees_drs in X.
  eapply in_nextupI. apply is_nextupI. exact X. Qed.

Definition in_nextup_nu W rules prems concln concl dtn dt :=
  iffT_D1 (@in_nextup_eqv W rules prems concln concl dtn dt).
Definition nextup_in_nu W rules prems concln concl dtn dt :=
  iffT_D2 (@in_nextup_eqv W rules prems concln concl dtn dt).

Lemma in_nextup_fc_eqv W rules prems (dtn dt : @derrec_fc W rules prems) :
  iffT (in_nextup_fc dtn dt) (InT dtn (nextup dt)).
Proof. apply pair ; intros.
- destruct X. exact (in_nextup_nu i).
- destruct dtn. destruct dt. apply in_nextup_fcI. exact (nextup_in_nu _ X).
Qed.

Definition in_nextup_fc_nu W rules prems dtn dt :=
  iffT_D1 (@in_nextup_fc_eqv W rules prems dtn dt).
Definition nextup_in_nu_fc W rules prems dtn dt :=
  iffT_D2 (@in_nextup_fc_eqv W rules prems dtn dt).

(* converse to this requires is_nextup (dlNil rules prems) (dpI _ _ _ _) *)
Lemma is_nextup_ndt W rules prems concls (concl : W) 
  (dts : dersrec rules prems concls) 
  (dt : derrec rules prems concl) :
  is_nextup dts dt -> nextup (fcI dt) = dersrec_trees dts.
Proof. unfold nextup. intros.  destruct X. reflexivity. Qed.

Lemma drs_trees_height W rules prems ps (ds : @dersrec W rules prems ps) dn: 
  InT dn (dersrec_trees ds) -> derrec_fc_height dn <= dersrec_height ds.
Proof. induction ds ; simpl ; intro inn ; inversion inn.
subst. simpl. apply PeanoNat.Nat.le_max_l.
apply (Le.le_trans _ _ _ (IHds X)).  apply PeanoNat.Nat.le_max_r. Qed.

Lemma nextup_height W rules prems dt dn: InT dn (nextup dt) ->
  (@derrec_fc_height W rules prems dn) < derrec_fc_height dt.
Proof. intro inn.  destruct dt. destruct d ; simpl in inn. inversion inn.
simpl.  exact (Lt.le_lt_n_Sm _ _ (drs_trees_height _ inn)). Qed.

Lemma fcI_inj: forall X rules prems concl (d1 : @derrec X rules prems concl) d2,
  fcI d1 = fcI d2 -> d1 = d2.
Proof. intros.  (* injection H gives existT equality *)
  dependent destruction H. reflexivity. Qed.

(* this doesn't work - type of Q 
Goal forall X rules prems Q cs (ds : @dersrec X rules prems cs),
  allPder Q ds -> Forall2T Q cs (dersrec_trees ds).
 *)

Open Scope type_scope.

Lemma dersrecD_forall_in_dersrec : forall (X : Type) (rs : list X -> X -> Type) (ps : X -> Type) (cs : list X) (ds : dersrec rs ps cs) (c : X),
    InT c cs -> (existsT2 d : derrec rs ps c, in_dersrec d ds).
Proof.
  induction ds; intros c Hin.
  inversion Hin.
  inversion Hin.
  + subst. exists d. constructor.
  + subst. eapply IHds in X0. destruct X0 as [d2 Hin2].
    exists d2. constructor 2. eapply Hin2.
Qed.

Lemma dersrec_double_verb: forall X rules prems c1 c2 (d : (dersrec rules prems [c1;c2])),
    existsT2 (d1 : (derrec rules prems (c1 : X))) (d2 : (derrec rules prems (c2 : X))),
      (in_dersrec d1 d) * (in_dersrec d2 d).
Proof.
  intros.
  assert (InT c1 [c1;c2]) as Hin1. constructor. reflexivity.
  assert (InT c2 [c1;c2]) as Hin2. constructor 2. constructor. reflexivity.
  eapply dersrecD_forall_in_dersrec in Hin1.
  destruct Hin1 as [d1 Hin1]. exists d1.
  eapply dersrecD_forall_in_dersrec in Hin2.
  destruct Hin2 as [d2 Hin2]. exists d2.
  split. apply Hin1. apply Hin2.
Qed.

Definition dp {X : Type} {rules : list X -> X -> Type} {prems : X -> Type}
  {concl : X} (der : derrec rules prems concl) := @derrec_height X rules prems concl der.
Lemma dersrec_derrec_height : forall n {X : Type} {rules prems G}
                                     (D2 : dersrec rules prems [G]),
    dersrec_height D2 = n ->
    existsT2 (D1 : derrec rules prems G),
      @derrec_height X _ _ _ D1 = n.
Proof.
  intros until 0.
  intros Ht.
  remember D2 as D2'.
  remember [G] as GG.
  destruct D2. discriminate.
  subst. simpl.
  inversion HeqGG. subst.
  exists d.
  remember [] as l.
  destruct D2. simpl.
  rewrite PeanoNat.Nat.max_0_r. reflexivity.
  discriminate.
Qed.

Lemma dersrec_derrec2_height : forall n {X : Type} {rules prems G1 G2}
                                     (D2 : dersrec rules prems [G1;G2]),
    dersrec_height D2 = n ->
    existsT2 (D1a : derrec rules prems G1) (D1b : derrec rules prems G2),
     n = max (@derrec_height X _ _ _ D1a) (@derrec_height X _ _ _ D1b).
Proof.
  intros until 0.
  intros Ht.
  remember D2 as D2'.
  remember [G1;G2] as GG.
  destruct D2. discriminate.
  destruct seqs. discriminate.
  destruct seqs. 2 : discriminate.
  edestruct (@dersrec_derrec_height (@dersrec_height _ _ _ _ D2)_ _ _ _ D2).
  reflexivity.  
  subst. simpl.
  inversion HeqGG. subst.
  exists d. exists x0.
  rewrite e. reflexivity.
Qed.

Lemma dersrec_derrec_dp : forall n {X : Type} {rules prems G}
                                     (D2 : dersrec rules prems [G]),
    dersrec_height D2 = n ->
    existsT2 (D1 : derrec rules prems G),
      @dp X _ _ _ D1 = n.
Proof. eapply dersrec_derrec_height. Qed.

Lemma dersrec_derrec2_dp : forall n {X : Type} {rules prems G1 G2}
                                     (D2 : dersrec rules prems [G1;G2]),
    dersrec_height D2 = n ->
    existsT2 (D1a : derrec rules prems G1) (D1b : derrec rules prems G2),
      n = max (@dp X _ _ _ D1a) (@dp X _ _ _ D1b).
Proof. eapply dersrec_derrec2_height. Qed.

Lemma dersrec_derrec_height_le : forall {T : Type} rules prems ps p 
    (ds : dersrec rules prems ps)
    (d  : derrec  rules prems p),
    in_dersrec d ds ->
    derrec_height d <= @dersrec_height T _ _ _ ds.
Proof.
  intros T rules prems ps p ds d Hin.
  eapply le_dersrec_height.
  2 : eapply le_n.
  assumption.
Qed.

Lemma dp_same : forall {T : Type} {rules prems} (l1 l2 : list T)
     (D1 : derrec rules prems l1)
    (Heq : l1 = l2),
    dp (eq_rect _ (fun l => derrec rules prems l) D1 l2 Heq) = dp D1.
Proof. induction D1; intros Heq; subst; reflexivity. Qed.


Lemma dp_same_fun : forall {T T2 : Type} {rules prems} (l1 l2 : list T) (f : list T -> T2)
     (D1 : derrec rules prems (f l1))
    (Heq : l1 = l2),
    dp (eq_rect _ (fun l => derrec rules prems (f l)) D1 l2 Heq) = dp D1.
Proof.  intros; inversion D1; subst; reflexivity. Qed.


Lemma derrec_dp_same :
  forall {X : Type} rules (prems : X -> Type) G H (D1 : derrec rules prems G),
    G = H ->
    existsT2 (D2 : derrec rules prems H), dp D1 = dp D2.
Proof. intros. subst. exists D1. reflexivity. Qed.

Lemma derrec_dp_same2 :
  forall {X : Type} rules (prems : X -> Type) G (D1 : derrec rules prems G) H,
    G = H ->
    existsT2 (D2 : derrec rules prems H), dp D1 = dp D2.
Proof. intros. subst. exists D1. reflexivity. Qed.

Definition get_D {X} rules prems G H D pf :=
(let (D', HD') := (fun (X : Type) (rules : list X -> X -> Type) (prems : X -> Type) 
  (G H : X) (D1 : derrec rules prems G) (H0 : G = H) =>
eq_rect_r
  (fun G0 : X =>
   forall D2 : derrec rules prems G0,
   existsT2 D3 : derrec rules prems H, dp D2 = dp D3)
  (fun D2 : derrec rules prems H =>
     existT (fun D3 : derrec rules prems H => dp D2 = dp D3) D2 eq_refl) H0 D1)
              X rules prems
G H D pf in D').
Check get_D.
Print get_D.
(*
Parameter (X : Type) (rules : list X -> X -> Type) (prems : X -> Type) 
  (G H : X) (D : derrec rules prems G) (pf : G = H).
Compute (get_D rules prems G H D pf).
*)
Lemma dp_get_D : forall (X : Type) (rules : list X -> X -> Type) (prems : X -> Type) 
                      (G H : X) (D : derrec rules prems G) (pf : G = H),
    dp D = dp (get_D D pf).
Proof. intros. subst. reflexivity. Qed.

Definition get_dpD {X : Type} (rules : list X -> X -> Type) (prems : X -> Type) (G H : X) 
  (D : derrec rules prems G) (pf : G = H) :=
 EqdepFacts.internal_eq_rew_r_dep
   (fun (G0 : X) (pf0 : G0 = H) =>
    forall D0 : derrec rules prems G0, dp D0 = dp (get_D D0 pf0))
   (fun D0 : derrec rules prems H => eq_refl) pf D.

Check get_dpD.

Ltac tfm_dersrec_derrec_dp D2s D2 Hdp HdpD2 Hdp'' Hdp' :=  
  destruct (dersrec_derrec_dp D2s eq_refl) as [D2 HdpD2];
  match goal with
  | [ H : dp ?D1 + S (dersrec_height D2s) <= ?m |- _ ] =>
    assert (dp D1 + (S (dp D2)) <= m) as Hdp'';
    [rewrite HdpD2; assumption | ];
    assert (dp D1 + dp D2 <= m - 1) as Hdp';
    [lia | ]; clear HdpD2 D2s Hdp
  end.

Ltac tfm_dersrec_derrec2_dp D2s D2 Hdp HdpD2 Hdpa'' Hdpb'' Hdpa' Hdpb' HeqD2s Hmax1 Hmax2 :=  
  assert (dersrec_height D2s = dersrec_height D2s) as HeqD2s;
  [reflexivity |];
  destruct (dersrec_derrec2_dp D2s HeqD2s) as [D2a [D2b HdpD2]];
  clear HeqD2s;
  epose proof (Max.le_max_r _ _) as Hmax1;
  epose proof (Max.le_max_l _ _) as Hmax2;
  rewrite <- HdpD2 in Hmax1;
  rewrite <- HdpD2 in Hmax2;
  match goal with
  | [ H : dp ?D1 + S (dersrec_height D2s) <= ?m |- _ ] =>
  assert (dp D1 + (S (dp D2a)) <= m) as Hdpa'';
  [lia | ];
  assert (dp D1 + (S (dp D2b)) <= m) as Hdpb'';
  [lia | ];
  assert (dp D1 + (dp D2a) <= m - 1) as Hdpa';
  [lia | ];
  assert (dp D1 + (dp D2b) <= m - 1) as Hdpb';
  [lia | ];
  clear HdpD2 D2s Hdp Hmax1 Hmax2
  end.

(*
Print botRule_fc.
Print Implicit der_concl_eq.
Print Implicit der_fc_concl_eq.
Print Implicit der_botRule.
Print Implicit botRule_fc_concl.
Print Implicit botRule_fc_rules.
Print Implicit botRule_fc_drs.
Print Implicit botRule_fc_ps.
Print Implicit botRule_fc_prems.
*)
