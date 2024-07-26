(*
  if subject expansion holds, weak normalization implies strong normalization:

  Context (step' : term -> term -> Prop).
  Context (subject_expansion : forall M N, step' M N -> typable N -> typable M).

  Theorem wn_step'_sn_step (M N : term) : steps' M N -> normal_form N -> sn M.
*)

Require Import BetaPrime.CD.
Require Import BetaPrime.Util.CD_facts.
Require BetaPrime.Util.CD_sn.
Require Import BetaPrime.Util.term_facts.

Require Import PeanoNat Relations List Lia.
Import ListNotations TermNotations.
Import Lambda.

Require Import ssreflect.

Set Default Goal Selector "!".

Unset Implicit Arguments.

Fixpoint merge (Gamma1 Gamma2 : list ty) :=
  match Gamma1 with
  | nil => Gamma2
  | (s1, phi1) :: Gamma1 =>
    match Gamma2 with
    | nil => (s1, phi1) :: Gamma1
    | (s2, phi2) :: Gamma2 => (s1, phi1 ++ (s2 :: phi2)) :: merge Gamma1 Gamma2
    end
  end.

Lemma type_assignment_mergeL Delta Gamma M t :
  type_assignment Gamma M t -> type_assignment (merge Delta Gamma) M t.
Proof.
  apply: type_assignment_weaken.
  elim: Delta Gamma.
  - move=> /= > -> ?. by do 3 econstructor.
  - move=> [??] > IH [|[??] ?] /=.
    + by case.
    + move=> [|?] /=.
      * move=> > [] *. subst. do 3 econstructor; [done|].
        right. apply /in_app_iff. by right.
      * by apply: IH.
Qed.

Lemma typable_lam M : typable M -> typable (lam M).
Proof.
  move=> [] [|[??] ?] ?.
  + move=> /(type_assignment_mergeL [(atom 0, nil)]) ?.
    do 2 econstructor. by eassumption.
  + move=> *. do 2 econstructor. by eassumption.
Qed.

Lemma type_assignment_mergeR Delta Gamma M t :
  type_assignment Gamma M t -> type_assignment (merge Gamma Delta) M t.
Proof.
  apply: type_assignment_weaken.
  elim: Gamma Delta.
  - by move=> ? [|].
  - move=> [??] > IH [|[??] ?] /=.
    + move=> [|?] /=.
      * move=> > [] *. subst. by do 3 econstructor.
      * move=> *. by do 3 econstructor; eassumption.
    + move=> [|?] /=.
      * move=> > [] *. subst. do 3 econstructor; [done|].
        rewrite in_app_iff. tauto.
      * by apply: IH.
Qed.

Lemma neutral_typableE M : neutral typable M -> forall t, exists Gamma, type_assignment Gamma M t.
Proof.
  elim.
  - move=> x t. exists (repeat (t, nil) (S x)). econstructor.
    + apply: nth_error_repeat. lia.
    + by left.
  - move=> > _ IH [] Gamma s ? t.
    move: (IH (arr s nil t)) => - [Gamma'] ?.
    exists (merge Gamma Gamma'). econstructor.
    + apply: type_assignment_mergeL. by eassumption.
    + by apply: type_assignment_mergeR.
    + done.
Qed.

Lemma neutral_typableI P M : neutral P M -> typable M -> neutral typable M.
Proof.
  elim.
  - by constructor.
  - move=> > _ IH _ [] > /type_assignmentE [] *.
    constructor; [apply: IH|]; apply: typable_intro; eassumption.
Qed.

Lemma nf_typable M : normal_form M -> typable M.
Proof.
  elim.
  - move=> x. apply: (typable_intro _ (repeat ((atom 0), nil) (S x)) (atom 0)).
    econstructor; [|by left]. apply: nth_error_repeat. lia.
  - move=> > ?. by apply: typable_lam.
  - move=> x N ??.
    have /neutral_typableE : neutral typable (app (var x) N) by do ? constructor.
    move=> /(_ (atom 0)) [?] ?. econstructor. by eassumption.
  - move=> > /normal_form_app_neutral /neutral_typableI /[apply].
    move=> /neutral_typableE H _ [] Gamma t ?.
    move: (H (arr t nil (atom 0))) => [Gamma'] ?.
    apply: typable_intro. econstructor.
    + apply: (type_assignment_mergeL Gamma Gamma'). by eassumption.
    + by apply: type_assignment_mergeR.
    + done.
Qed.

Section WN_SN.

Context (step' : term -> term -> Prop).
Context (subject_expansion : forall M N, step' M N -> typable N -> typable M).

#[local] Notation steps' M N := (clos_refl_trans term (fun M N => step' M N) M N).

(* if subject expansion holds, weak normalization implies strong normalization *)
Theorem wn_step'_sn_step (M N : term) : steps' M N -> normal_form N -> sn M.
Proof.
  move=> /clos_rt_rt1n_iff HMN HN.
  suff: typable M.
  { move=> [] >. by apply: CD_sn.strong_normalization. }
  elim: HMN HN.
  - by apply: nf_typable.
  - move=> > /subject_expansion. by auto.
Qed.

End WN_SN.
