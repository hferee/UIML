Require Import GL.Interpolation.UIGL_braga.
Require Import GLS_export.
Require Import ExtrOcamlBasic ExtrOcamlString.


Require Import K.Interpolation.UIK_braga.
Require Import KS_export.
Require Import ISL.PropQuantifiers ISL.DecisionProcedure.
Require ISL.Simp_env.

(* Simplified propositional quantifiers *)
Module Import S := Simp_env.S.
Module Import SPQr := PropQuant S.

Program Fixpoint MPropF_of_form (f : Formulas.form) : MPropF  :=
match f with
| Formulas.Var n => Var n
| Formulas.Bot => Bot
| Formulas.Implies f1 f2 => Imp (MPropF_of_form f1) (MPropF_of_form f2)
| Formulas.And f1 f2 => Imp (Imp (MPropF_of_form f1) (Imp (MPropF_of_form f2) Bot)) Bot
| Formulas.Or f1 f2 => Imp (Imp (MPropF_of_form f1) Bot) (MPropF_of_form f2)
| Formulas.Box f => Box (MPropF_of_form f)
end.

Fixpoint form_of_MPropF (f : MPropF) : Formulas.form :=
match f with
| Var n => Formulas.Var n
| Bot => Formulas.Bot
| Imp f1 f2 => Formulas.Implies (form_of_MPropF f1) (form_of_MPropF f2)
| Box f => Formulas.Box (form_of_MPropF f)
end.


Definition gl_UI p s := form_of_MPropF (proj1_sig (GL.Interpolation.UIGL_braga.GUI_tot p ([],[MPropF_of_form s]))).
Definition k_UI p s := form_of_MPropF(proj1_sig (K.Interpolation.UIK_braga.GUI_tot p ([],[MPropF_of_form s]))).

Definition isl_E v f := @Ef v Formulas.Modal f.
Definition isl_A v f := @Af v Formulas.Modal f.

(* simp_form seems to improve over simp in most cases.
  Notable exception: (a ∨b) → c *)
Definition isl_simp f := @simp_form Formulas.Modal f.

(* For backward compatibility only *)
Definition isl_simplified_E := isl_E.
Definition isl_simplified_A := isl_A.

Set Extraction Output Directory "extraction".

Separate Extraction Provable_dec gl_UI k_UI isl_E isl_A isl_simplified_E isl_simplified_A Formulas.weight isl_simp.

