Require Import List Bool sets.
Include ListNotations.


(* NFA component constructors *)
Inductive nfa_comp {A B} :=
  | state (q:A)
  | symbol (a:B)
  | start (q:A)
  | accept (q:A)
  | trans (q:A) (a:B) (q':A).

(* NFA as a list of these components *)
Definition nfa A B := list (@nfa_comp A B).

(* An actual NFA must have equality decidability over its types *)
Inductive actual_nfa {A B} : nfa A B -> Prop :=
  | actual_nfa_cons (g: nfa A B) (eqA:A->A->bool) (eqB:B->B->bool) :
      (forall q1 q2, q1=q2 <-> eqA q1 q2=true) ->
      (forall a b, a=b <-> eqB a b=true) ->
      actual_nfa g.

(* Set of states *)
Fixpoint states {A B} (g:nfa A B) :=
  match g with
  | nil => nil
  | state q::g => q::states g
  | start q::g => q::states g
  | accept q::g => q::states g
  | trans q a q'::g => q::q'::states g
  | _::g => states g
  end.

(* Alphabet *)
Fixpoint alphabet {A B} (g:nfa A B) :=
  match g with
  | nil => nil
  | symbol a::g => a::alphabet g
  | trans q a q'::g => a::alphabet g
  | _::g => alphabet g
  end.

(* Start states *)
Fixpoint start_states {A B} (g:nfa A B) :=
  match g with
  | nil => nil
  | start q::g => q::start_states g
  | _::g => start_states g
  end.

(* Accept states *)
Fixpoint accept_states {A B} (g:nfa A B) :=
  match g with
  | nil => nil
  | accept q::g => q::accept_states g
  | _::g => accept_states g
  end.

(* Transition function *)
Fixpoint transition {A B} (eqA:A->A->bool) (eqB:B->B->bool) (g:nfa A B) q a :=
  match g with
  | nil => nil
  | trans q1 b q2::g =>
    if (eqA q q1 && eqB a b) then
      q2::transition eqA eqB g q a
    else
      transition eqA eqB g q a
  | _::g => transition eqA eqB g q a
  end.

(* Its extended version *)
Fixpoint ext_transition {A B} eqA eqB (g:nfa A B) Q w :=
  match w with
  | nil => Q
  | a::w => ext_transition eqA eqB g (
              (fix f Q :=
                match Q with
                | nil => nil
                | q::Q => transition eqA eqB g q a ++ f Q
                end) Q
            ) w
  end.


(** Proofs on states **)

(* We can separate the states of concatenated NFAs *)
Lemma in_app_states_or {A B} (g1 g2:nfa A B) q :
  In q (states (g1 ++ g2)) <-> In q (states g1) \/ In q (states g2).
Proof.
  intros; induction g1.
  - split; intros.
    2: destruct H.
    2: inversion H.
    1,2: intuition.
  - destruct a; split; intros.
    + destruct H; subst.
      left; left; intuition.
      simpl; apply or_assoc; right; intuition.
    + simpl in H; apply or_assoc in H; destruct H; subst.
      left; intuition.
      right; intuition.
    + intuition.
    + intuition.
    + destruct H; subst.
      left; left; intuition.
      simpl; apply or_assoc; right; intuition.
    + simpl in H; apply or_assoc in H; destruct H; subst.
      left; intuition.
      right; intuition.
    + destruct H; subst.
      left; left; intuition.
      simpl; apply or_assoc; right; intuition.
    + simpl in H; apply or_assoc in H; destruct H; subst.
      left; intuition.
      right; intuition.
    + destruct H; subst.
      left; left; intuition.
      destruct H; subst.
      left; right; intuition.
      simpl; apply or_assoc; right; intuition.
    + simpl in H; apply or_assoc in H; destruct H; subst.
      left; intuition.
      apply or_assoc in H; destruct H; subst; right; intuition.
Qed.

(* The possibilities of a state *)
Lemma states_in {A B} (g:nfa A B) q :
  In q (states g) -> In (state q) g \/ In (start q) g \/ In (accept q) g \/
  exists q' a, In (trans q a q') g \/ In (trans q' a q) g.
Proof.
  intros; induction g.
  destruct H.
  destruct a.
  - destruct H; subst.
    intuition.
    apply IHg in H; destruct H as [H|[H|[H|[q' [a [H|H]]]]]].
    1-3: intuition.
    1-2: right; right; right; exists q', a; intuition.
  - apply IHg in H; destruct H as [H|[H|[H|[q' [b [H|H]]]]]].
    1-3: intuition.
    1-2: right; right; right; exists q', b; intuition.
  - destruct H; subst.
    intuition.
    apply IHg in H; destruct H as [H|[H|[H|[q' [a [H|H]]]]]].
    1-3: intuition.
    1-2: right; right; right; exists q', a; intuition.
  - destruct H; subst.
    intuition.
    apply IHg in H; destruct H as [H|[H|[H|[q' [a [H|H]]]]]].
    1-3: intuition.
    1-2: right; right; right; exists q', a; intuition.
  - destruct H; subst.
    right; right; right; exists q', a; intuition.
    destruct H; subst.
    right; right; right; exists q0, a; intuition.
    apply IHg in H; destruct H as [H|[H|[H|[q'' [b [H|H]]]]]].
    1-3: intuition.
    1-2: right; right; right; exists q'', b; intuition.
Qed.

(* A component constructed by trans defines states and symbol *)
Lemma trans_in_states {A B} (g:nfa A B) q a q' :
  In (trans q a q') g -> In q (states g).
Proof.
  intros; induction g; destruct H; subst.
  left; intuition.
  destruct a0; try right; try right; intuition.
Qed.

Lemma trans_in_states_r {A B} (g:nfa A B) q a q' :
  In (trans q' a q) g -> In q (states g).
Proof.
  intros; induction g; destruct H; subst.
  right; intuition.
  destruct a0; try right; try right; intuition.
Qed.

Lemma trans_in_alphabet {A B} (g:nfa A B) q a q' :
  In (trans q a q') g -> In a (alphabet g).
Proof.
  intros.
  induction g; destruct H.
  subst; left; auto.
  destruct a0; simpl; try right; intuition.
Qed.


(** Proofs on start states **)

(* Start states is subset of states *)
Lemma start_states_subset {A B} (g:nfa A B) :
  subset (start_states g) (states g).
Proof.
  induction g; intros q H.
  destruct H.
  simpl in H; destruct a.
  1,2,4,5: try right; intuition.
  destruct H; subst.
  left; auto.
  right; intuition.
Qed.

(* We can separate the start states of concatenated NFAs *)
Lemma in_app_start_states_or {A B} (g1 g2:nfa A B) q :
  In q (start_states (g1 ++ g2)) <-> In q (start_states g1) \/ In q (start_states g2).
Proof.
  intros; induction g1.
  {
    split; intros.
    2: destruct H.
    2: destruct H.
    1,2: intuition.
  }
  destruct a.
  1,2,4,5: auto.
  simpl; split; intros.
  - destruct H; subst.
    left; left; auto.
    apply or_assoc; right; intuition.
  - apply or_assoc in H; destruct H; subst.
    left; auto.
    right; apply IHg1; auto.
Qed.

(* The start states of a NFA concatenated to another without start states is the former's set  *)
Lemma app_start_states_nil {A B} (g1 g2:nfa A B) :
  start_states g2 = [] ->
  start_states (g1++g2) = start_states g1.
Proof.
  intros; induction g1.
  auto.
  destruct a.
  1,2,4,5: auto.
  simpl; rewrite IHg1; auto.
Qed.

(* The start states of concatenated NFAs without start states is nil *)
Lemma start_states_app_nil {A B} (g1 g2:nfa A B) :
  start_states g1 = nil -> start_states g2 = nil ->
  start_states (g1 ++ g2) = nil.
Proof.
  intros; rewrite app_start_states_nil; auto.
Qed.

(* A given q is in start states iff it is constructed by start and is in the NFA *)
Lemma start_states_in {A B} (g:nfa A B) q :
  In q (start_states g) <-> In (start q) g.
Proof.
  intros; induction g.
  split; intros; destruct H.
  destruct a; split; intros.
  1,3,7,9: intuition.
  1,2,5,6: destruct H; try discriminate; intuition.
  destruct H; subst; intuition.
  destruct H.
  injection H; intros; subst; left; auto.
  right; intuition.
Qed.


(** Proofs on accept states **)

(* Accept states is subset of states *)
Lemma accept_states_subset {A B} (g:nfa A B) :
  subset (accept_states g) (states g).
Proof.
  induction g; intros q H.
  destruct H.
  simpl in H; destruct a.
  1,2,3,5: try right; intuition.
  destruct H; subst.
  left; auto.
  right; intuition.
Qed.

(* A given q is in accept states iff it is constructed by accept and is in the NFA *)
Lemma accept_states_in {A B} (g:nfa A B) q :
  In q (accept_states g) <-> In (accept q) g.
Proof.
  intros; induction g.
  split; intros; destruct H.
  destruct a; split; intros.
  1,3,5,9: intuition.
  1-3,6: destruct H; try discriminate; intuition.
  destruct H; subst; intuition.
  destruct H.
  injection H; intros; subst; left; auto.
  right; intuition.
Qed.


(** Proofs on transitions **)

(* A given q' is returned by transition iff it is constructed by trans and is in the NFA *)
Lemma transition_in {A B} (eqA:A->A->bool) (eqB:B->B->bool) (g:nfa A B) q a q' :
  (forall q1 q2, q1=q2 <-> eqA q1 q2=true) ->
  (forall a b, a=b <-> eqB a b=true) ->
  In q' (transition eqA eqB g q a) <-> In (trans q a q') g.
Proof.
  intros.
  assert (forall q, eqA q q = true).
    intros; apply H; intuition.
  assert (forall a, eqB a a = true).
    intros; apply H0; intuition.
  intros; induction g.
  - split; intros; destruct H3.
  - split; intros.
    + destruct a0.
      1-4: right; intuition.
      simpl in H3; destruct (eqA q q0 && eqB a a0) eqn:H4.
      destruct H3.
      2,3: right; intuition.
      subst; left;
      apply andb_true_iff in H4; destruct H4;
      apply H in H3; apply H0 in H4; subst;
      auto.
    + destruct H3.
      * subst; simpl; rewrite H1, H2; left; auto.
      * apply IHg in H3; destruct a0; simpl.
        1-4: auto.
        destruct (eqA q q0 && eqB a a0);
        try right; auto.
Qed.

Lemma transition_in_ext {A B} (eqA:A->A->bool) (eqB:B->B->bool) (g:nfa A B) Q q a q' :
  (forall q1 q2, q1=q2 <-> eqA q1 q2=true) ->
  (forall a b, a=b <-> eqB a b=true) ->
  In q Q -> In (trans q a q') g ->
  In q' (ext_transition eqA eqB g Q [a]).
Proof.
  intros; induction Q; destruct H1.
  subst; apply in_or_app; left; apply transition_in; auto.
  apply in_or_app; right; intuition.
Qed.

Lemma in_transition_ext {A B} (eqA:A->A->bool) (eqB:B->B->bool) (g:nfa A B) Q q' a :
  (forall q1 q2, q1=q2 <-> eqA q1 q2=true) ->
  (forall a b, a=b <-> eqB a b=true) ->
  In q' (ext_transition eqA eqB g Q [a]) ->
  exists q, In q Q /\ In (trans q a q') g.
Proof.
  intros.
  induction Q as [|q Q IH].
  destruct H1.
  apply in_app_or in H1; destruct H1.
  - apply transition_in in H1.
    2,3: auto.
    exists q; intuition.
  - apply IH in H1; destruct H1 as [q0 H1]; exists q0; intuition.
Qed.

(* The transition over a concatenated string may be applied to the first and then the second *)
Lemma ext_transition_app {A B} eqA eqB (g:nfa A B) Q w1 w2 :
  ext_transition eqA eqB g Q (w1 ++ w2) = ext_transition eqA eqB g (ext_transition eqA eqB g Q w1) w2.
Proof.
  generalize dependent Q.
  induction w1.
  - auto.
  - intros; apply IHw1.
Qed.

(* The transition over an empty set of states is empty *)
Lemma ext_transition_nil {A B} eqA eqB (g:nfa A B) w :
  ext_transition eqA eqB g nil w = nil.
Proof.
  intros; induction w; auto.
Qed.

(* The extended transition is subset of states *)
Lemma ext_transition_subset {A B} eqA eqB (g:nfa A B) q w :
  subset q (states g) ->
  subset (ext_transition eqA eqB g q w) (states g).
Proof.
  intros H q' H0; generalize dependent q; induction w; intros.
  apply H; auto.
  replace (a::w) with ([a]++w) in H0.
  rewrite ext_transition_app in H0.
  apply IHw with (ext_transition eqA eqB g q [a]).
  clear IHw H0 q'; intros q' H0; induction q.
  1,3,4: auto.
  simpl in H0; apply in_app_or in H0; destruct H0.
  - clear H IHq; induction g.
    destruct H0.
    destruct a1.
    1-4: try right; intuition.
    simpl in H0; destruct (eqA a0 q0 && eqB a a1).
    2: right; intuition.
    destruct H0.
    subst; right; left; auto.
    right; intuition.
  - apply IHq.
    2: auto.
    try intros q'' H1; apply H; intuition.
Qed.

(* If a transition over a concatenated string is not empty, then it applied to the first string
is either *)
Lemma ext_transition_app_not_nill {A B} eqA eqB (g:nfa A B) Q w1 w2 :
  ext_transition eqA eqB g Q (w1 ++ w2) <> nil ->
  ext_transition eqA eqB g Q w1 <> nil.
Proof.
  intros H H0.
  rewrite ext_transition_app, H0 in H.
  induction w2; intuition.
Qed.

(* Distributive property of extended transition *)
Lemma ext_transition_states_app {A B} eqA eqB (g:nfa A B) Q1 Q2 w :
  ext_transition eqA eqB g (Q1 ++ Q2) w = ext_transition eqA eqB g Q1 w ++ ext_transition eqA eqB g Q2 w.
Proof.
  induction w using rev_ind.
  auto.
  repeat rewrite ext_transition_app; rewrite IHw;
  clear IHw; remember (ext_transition eqA eqB g Q1 w) as Q3; clear HeqQ3;
  remember (ext_transition eqA eqB g Q2 w) as Q4; clear HeqQ4 Q1 Q2;
  simpl; induction Q3.
  auto.
  simpl; rewrite IHQ3, app_assoc; auto.
Qed.

(* We can always extend the set states to be transitioned *)
Lemma ext_transition_single {A B} eqA eqB (g:nfa A B) Q q q' w :
  In q Q /\ In q' (ext_transition eqA eqB g [q] w) -> In q' (ext_transition eqA eqB g Q w).
Proof.
  intros; destruct H as [H H0]; induction Q.
  destruct H.
  destruct w.
  - destruct H0 as [H0|[]]; subst; auto.
  - destruct H.
    subst; simpl; simpl in H0; rewrite app_nil_r in H0.
    1,2: simpl; rewrite ext_transition_states_app; apply in_or_app; intuition.
Qed.

(* The inverse can be done too *)
Lemma ext_transition_list {A B} eqA eqB (g:nfa A B) Q q' w :
  In q' (ext_transition eqA eqB g Q w) -> exists q, In q Q /\ In q' (ext_transition eqA eqB g [q] w).
Proof.
  intros;
  generalize dependent q';
  induction w using rev_ind; intros.
  - simpl in *; exists q'; split; intuition.
  - rewrite ext_transition_app in H;
    assert (exists q'', In q'' (ext_transition eqA eqB g Q w) /\ In q' (ext_transition eqA eqB g [q''] [x])). {
      clear IHw;
      induction (ext_transition eqA eqB g Q w).
      destruct H.
      apply in_app_or in H; destruct H.
      - exists a; simpl; split.
        auto.
        rewrite app_nil_r; auto.
      - apply IHl in H; destruct H as [q'' [H H0]]; exists q''; intuition.
    }
    destruct H0 as [q'' [H0 H1]];
    apply IHw in H0;
    destruct H0 as [q [H0 H2]]; exists q; split.
    auto.
    rewrite ext_transition_app;
    apply ext_transition_single with q''; intuition.
Qed.

(* The extended transition over a set of states returns a set of states *)
Lemma ext_transition_in_states {A B} eqA eqB (g:nfa A B) Q q' w :
  (forall q, In q Q -> In q (states g)) ->
  In q' (ext_transition eqA eqB g Q w) -> In q' (states g).
Proof.
  intros;
  generalize dependent Q;
  induction w; intros.
  auto.
  replace (a::w) with ([a]++w) in H0.
  rewrite ext_transition_app in H0;
  apply IHw with (ext_transition eqA eqB g Q [a]).
  2,3: auto.
  clear IHw H0; intros;
  induction Q.
  destruct H0.
  replace (a0::Q) with ([a0] ++ Q) in H0.
  2: auto.
  rewrite ext_transition_states_app in H0;
  apply in_app_or in H0; destruct H0.
  2: apply IHQ; intros; try (apply H; right); auto.
  simpl in H0; rewrite app_nil_r in H0;
  clear IHQ H; induction g.
  destruct H0.
  destruct a1.
  1-4: try right; auto.
  simpl in H0; destruct (eqA a0 q0 && eqB a a1).
  2: right; right; auto.
  destruct H0.
  subst; right; left; auto.
  right; right; auto.
Qed.

(* The extended transition over a set of states is equivalent to it applied to an equivalent set *)
Lemma ext_transition_eq_sets {A B} eqA eqB (g: nfa A B) w :
  forall Q1 Q2, eq_sets Q1 Q2 ->
  eq_sets (ext_transition eqA eqB g Q1 w) (ext_transition eqA eqB g Q2 w).
Proof.
  induction w; intros.
  2: replace (a::w) with ([a] ++ w).
  1,3: auto.
  rewrite ext_transition_app, ext_transition_app;
  apply IHw; clear IHw.
  assert (forall s1 s2, (forall x, In x s1 -> In x s2) -> forall x, In x (ext_transition eqA eqB g s1 [a]) -> In x (ext_transition eqA eqB g s2 [a])). {
    clear H Q1 Q2; intros; induction s1.
    destruct H0.
    replace (ext_transition eqA eqB g (a0 :: s1) [a]) with (transition eqA eqB g a0 a ++ ext_transition eqA eqB g s1 [a]) in H0.
    2: auto.
    apply in_app_or in H0.
    destruct H0.
    - clear IHs1; specialize (H a0); induction s2.
      destruct H; intuition.
      assert (In a0 (a1::s2)).
        apply H; intuition.
      destruct H1.
      1,2: simpl; apply in_or_app.
      subst; intuition.
      right; apply IHs2; intuition.
    - apply IHs1.
      intros; apply H; intuition.
      auto.
  }
  split; intros.
  - apply H0 with Q1.
    2: auto.
    intros; apply H; auto.
  - apply H0 with Q2.
    2: auto.
    intros; apply H; auto.
Qed.

(* The sets equivalence extends to the extended transition *)
Lemma eq_setsb_ext_transition {A B} eqA eqB (g:nfa A B) Q1 Q2 Q3 Q4 w :
  (forall x x', x=x' <-> eqA x x'=true) ->
  eq_setsb eqA Q1 Q2 = true ->
  eq_setsb eqA Q3 Q4 = true ->
  eq_setsb eqA Q3 (ext_transition eqA eqB g Q1 w) = eq_setsb eqA Q4 (ext_transition eqA eqB g Q2 w).
Proof.
  intros.
  destruct (eq_setsb eqA Q3 (ext_transition eqA eqB g Q1 w)) eqn:H2;
  destruct (eq_setsb eqA Q4 (ext_transition eqA eqB g Q2 w)) eqn:H3.
  1,4: auto.
  - apply eq_setsb_correct in H0;
    apply eq_setsb_correct in H1;
    apply eq_setsb_correct in H2.
    2-8: auto.
    assert (eq_setsb eqA Q4 (ext_transition eqA eqB g Q2 w) = true).
    2: rewrite H4 in H3; discriminate.
    apply eq_setsb_correct.
    auto.
    apply eq_sets_transitive with (ext_transition eqA eqB g Q1 w).
    2: apply ext_transition_eq_sets; auto.
    apply eq_sets_transitive with Q3; auto.
  - apply eq_setsb_correct in H0;
    apply eq_setsb_correct in H1;
    apply eq_setsb_correct in H3.
    2-8: auto.
    assert (eq_setsb eqA Q3 (ext_transition eqA eqB g Q1 w) = true).
    2: rewrite H4 in H2; discriminate.
    apply eq_setsb_correct.
    auto.
    apply eq_sets_transitive with (ext_transition eqA eqB g Q2 w).
    2: apply ext_transition_eq_sets, eq_sets_comm; auto.
    apply eq_sets_transitive with Q4.
    2: apply eq_sets_comm.
    1,2: auto.
Qed.


(** Languages **)

Definition has_accept_state {A B} (g:nfa A B) Q :=
  exists q, In q Q /\ In q (accept_states g).

(* Checks if Q has accept states *)
Fixpoint has_accept_stateb {A B} eqA (g:nfa A B) Q :=
  match Q with
  | nil => false
  | q::Q => inb eqA q (accept_states g) || has_accept_stateb eqA g Q
  end.

Lemma has_accept_stateb_correct {A B} eqA (g:nfa A B) Q :
  (forall q1 q2, q1=q2 <-> eqA q1 q2=true) ->
  has_accept_stateb eqA g Q = true <-> has_accept_state g Q.
Proof.
  unfold has_accept_state; intros;
  induction Q.
  - split; intros.
    + destruct g; discriminate.
    + destruct H0; destruct H0; inversion H0.
  - simpl; split; intros.
    + apply orb_prop in H0; destruct H0.
      * apply inb_correct in H0.
        -- exists a; split; auto.
        -- auto.
      * apply IHQ in H0; destruct H0; exists x; intuition.
    + apply orb_true_intro; destruct H0; destruct H0; destruct H0.
      * subst; left; apply inb_correct; auto.
      * right; apply IHQ; exists x; intuition.
Qed.

(* Language: all the words accepted by the NFA *)
Definition lang {A B} eqA eqB (g:nfa A B) w :=
  has_accept_state g (ext_transition eqA eqB g (start_states g) w).

(* Autômatos equivalentes *)
Definition equivalent_nfas {A B C} eqA eqB eqC (g1:nfa A B) (g2:nfa C B) :=
  forall w, lang eqA eqB g1 w <-> lang eqC eqB g2 w.


(** Reachable states **)
(* The states that we can reach from the start states through a transition *)

Definition reachable_state {A B} eqA eqB (g:nfa A B) q :=
  exists w, In q (ext_transition eqA eqB g (start_states g) w).


(** Paths **)
(*
   A path exists:
   - from a state to itself through the empty word
   - from an already existing path extended by a transition starting in
     the last state of it
*)

Inductive path {A B} (g:nfa A B) : A->A->list B->Prop :=
  | path_nil (q:A) : path g q q nil
  | path_next q1 q2 q3 w a : path g q1 q2 w -> In (trans q2 a q3) g -> path g q1 q3 (w ++ [a]).

(* Path can be left-inductive defined *)
Lemma path_left {A B} (g:nfa A B) q1 q3 a w :
  (forall q2, In (trans q1 a q2) g -> path g q2 q3 w -> path g q1 q3 (a::w)) /\
  (path g q1 q3 (a::w) -> exists q2, In (trans q1 a q2) g /\ path g q2 q3 w).
Proof.
  split; intros.
  - induction H0.
    + replace [a] with ([] ++ [a]).
      2: auto.
      apply path_next with q1.
      constructor.
      auto.
    + replace (a::w ++ [a0]) with ((a::w) ++ [a0]).
      2: auto.
      apply path_next with q2.
      2: auto.
      intuition.
  - generalize dependent q3.
    induction w using rev_ind; intros.
    + exists q3; split.
      2: constructor.
      inversion H.
      assert (w = nil /\ a0 = a).
        replace [a] with (nil ++ [a]) in H0;
        try apply app_inj_tail in H0; auto.
      destruct H5; subst.
      inversion H1; subst.
      auto.
      destruct w; discriminate.
    + inversion H; subst.
      assert (w0 = a::w).
        replace (a::w ++ [x]) with ((a::w) ++ [x]) in H0;
        try apply app_inj_tail in H0; intuition.
      subst; apply IHw in H1; destruct H1 as [q5 H1];
      exists q5; split.
      intuition.
      apply path_next with q2.
      intuition.
      injection H0; intros; apply app_inj_tail in H2; destruct H2;
      subst; intuition.
Qed.

(* Path is equivalent to the extended transition *)
Lemma path_ext_transition {A B} eqA eqB (g:nfa A B) q q' w :
  (forall q1 q2, q1=q2 <-> eqA q1 q2=true) ->
  (forall a b, a=b <-> eqB a b=true) ->
  In q' (ext_transition eqA eqB g [q] w) <-> path g q q' w.
Proof.
  intros; split; intros.
  - generalize dependent q'; induction w using rev_ind; intros.
    + destruct H1.
      2: destruct H1.
      subst; constructor.
    + rewrite ext_transition_app in H1.
      assert (exists q'', In q'' (ext_transition eqA eqB g [q] w) /\ In q' (ext_transition eqA eqB g [q''] [x])). {
        clear IHw.
        induction (ext_transition eqA eqB g [q] w).
        - destruct H1.
        - apply in_app_or in H1; destruct H1.
          + exists a; simpl; split.
            auto.
            rewrite app_nil_r; auto.
          + apply IHl in H1; destruct H1 as [q'' [H1 H2]]; exists q''; intuition.
      }
      destruct H2 as [q'' [H2 H3]].
      apply path_next with q''.
      intuition.
      simpl in H3; rewrite app_nil_r in H3; apply transition_in in H3; auto.
  - induction H1.
    + left; auto.
    + rewrite ext_transition_app; apply ext_transition_single with q2; split.
      auto.
      simpl; rewrite app_nil_r; apply (transition_in eqA eqB g q2 a q3 H H0); auto.
Qed.

(* If a path exists in a NFA, then it exists in any concatenation of it *)
Lemma path_app {A B} (g1 g2:nfa A B) q q' w :
  path g1 q q' w \/ path g2 q q' w -> path (g1 ++ g2) q q' w.
Proof.
  intros.
  destruct H; induction H.
  1,3: constructor.
  1,2: apply path_next with q2;
    try apply in_or_app; intuition.
Qed.

(* The constructor start is useless for paths *)
Lemma app_start_path {A B} (g:nfa A B) q0 q q' w :
  path (start q0::g) q q' w <-> path g q q' w.
Proof.
  split; intros.
  - induction H.
    apply path_nil.
    apply path_next with q2.
    auto.
    destruct H0; try discriminate; auto.
  - induction H.
    constructor.
    apply path_next with q2.
    auto.
    right; auto.
Qed.

(* The same is true for accept *)
Lemma path_app_accept {A B} (g:nfa A B) l q q' w :
  (forall c, In c l -> exists q, c = accept q) ->
  path (g ++ l) q q' w -> path g q q' w.
Proof.
  intros.
  induction H0.
  constructor.
  apply path_next with q2.
  auto.
  apply in_app_or in H1; destruct H1.
  auto.
  apply H in H1; destruct H1 as [q H1]; discriminate.
Qed.

(* Path existence is transitive *)
Lemma path_transitive {A B} (g:nfa A B) q1 q2 q3 w1 w2 :
  path g q1 q2 w1 -> path g q2 q3 w2 -> path g q1 q3 (w1 ++ w2).
Proof.
  intros.
  induction H0.
  rewrite app_nil_r; auto.
  replace (w1 ++ w ++ [a]) with ((w1 ++ w) ++ [a]).
  2: rewrite app_assoc; auto.
  apply path_next with q2; auto.
Qed.












