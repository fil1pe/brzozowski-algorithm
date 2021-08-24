Require Import List Bool Lia utils nfa dfa normalizing.
Include ListNotations.


(* The foreach loop that will apply the transitions determinization recursively *)
Fixpoint foreach {A B} eqA eqB (g:nfa A B) f Q l :=
  match l with
  | nil => nil
  | a::l => match (ext_transition eqA eqB g Q [a]) with
            | nil => foreach eqA eqB g f Q l
            | Q' => trans Q a Q'::f Q' ++ foreach eqA eqB g f Q l
            end
  end.

(* The transitions are constructed *)
Lemma foreach_in {A B} eqA eqB (g:nfa A B) f Q l a :
  In a l -> ext_transition eqA eqB g Q [a] <> nil ->
  In (trans Q a (ext_transition eqA eqB g Q [a])) (foreach eqA eqB g f Q l).
Proof.
  intros; induction l.
  destruct H.
  Opaque ext_transition.
  simpl; destruct (ext_transition eqA eqB g Q [a]) eqn:H1.
  destruct H0; auto.
  destruct H.
  - subst; destruct (ext_transition eqA eqB g Q [a]).
    discriminate.
    injection H1; intros; subst; intuition.
  - apply IHl in H.
    destruct (ext_transition eqA eqB g Q [a0]).
    2: right; apply in_or_app; right.
    1,2: auto.
  Transparent ext_transition.
Qed.

(* A transition is in the loop if it is constructed by the loop or the
the function this applies *)
Lemma in_foreach {A B} eqA eqB (g:nfa A B) f Q l c :
  In c (foreach eqA eqB g f Q l) ->
  exists Q' a, In a l /\ Q' <> nil /\ Q' = ext_transition eqA eqB g Q [a] /\
  In c (trans Q a Q'::f Q').
Proof.
  Opaque ext_transition.
  intros.
  induction l as [|b l].
  destruct H.
  simpl in H; destruct (ext_transition eqA eqB g Q [b]) eqn:H0.
  apply IHl in H; destruct H as [Q' [a H]]; exists Q', a; intuition.
  replace (In c (trans Q b (a :: l0) :: f (a :: l0) ++ foreach eqA eqB g f Q l)) with
  (In c ((trans Q b (a :: l0) :: f (a :: l0)) ++ foreach eqA eqB g f Q l)) in H.
  2: auto.
  apply in_app_or in H; destruct H.
  - exists (a::l0), b; repeat split.
    1,3,4: intuition.
    intros contra; discriminate.
  - apply IHl in H; destruct H as [Q' [d H]]; exists Q', d; intuition.
  Transparent ext_transition.
Qed.

(* If a component is constructed by a function f, then it is in the foreach loop
applied to f *)
Lemma next_in_foreach {A B} eqA eqB (g:nfa A B) f Q l a c :
  ext_transition eqA eqB g Q [a] <> nil ->
  In a l ->
  In c (f (ext_transition eqA eqB g Q [a])) ->
  In c (foreach eqA eqB g f Q l).
Proof.
  Opaque ext_transition.
  intros; induction l; destruct H0.
  - subst.
    simpl; destruct (ext_transition eqA eqB g Q [a]).
    destruct H; auto.
    right; apply in_or_app; intuition.
  - simpl; destruct (ext_transition eqA eqB g Q [a0]).
    intuition.
    right; apply in_or_app; intuition.
  Transparent ext_transition.
Qed.

(* The paths are maintained by the foreach *)
Lemma path_foreach {A B} eqA eqB (g:nfa A B) f Q l a Q1 Q2 w :
  ext_transition eqA eqB g Q [a] <> nil ->
  In a l ->
  path (f (ext_transition eqA eqB g Q [a])) Q1 Q2 w ->
  path (foreach eqA eqB g f Q l) Q1 Q2 w.
Proof.
  intros.
  induction H1.
  constructor.
  apply path_next with q2.
  auto.
  apply next_in_foreach with a; auto.
Qed.


(** Transitions determinization **)

(* Constructs the deterministic transitions through a search from
a given set of states (the start states). The fuel is needed for
the halting requirement *)
Fixpoint det_trans {A B} eqA eqB (g:nfa A B) fuel Q :=
  match fuel with
  | O => nil
  | S fuel =>
    foreach eqA eqB g (det_trans eqA eqB g fuel) Q (alphabet g)
  end.

(* A transition is made by the non-empty extended transition applied recursively *)
Lemma trans_in_det_trans {A B} eqA eqB (g:nfa A B) Q0 Q Q' n a :
  (forall q1 q2, q1=q2 <-> eqA q1 q2=true) ->
  In (trans Q a Q') (det_trans eqA eqB g n Q0) ->
  In a (alphabet g) /\ Q' <> nil /\ Q' = ext_transition eqA eqB g Q [a].
Proof.
  intros;
  generalize dependent Q0;
  induction n; intros.
  destruct H0.
  simpl in H0; apply in_foreach in H0; destruct H0 as [Q0' [b [H0 [H1 [H2 [H3|H3]]]]]].
  2: apply IHn in H3; clear IHn; auto.
  clear IHn; injection H3; intros; subst; split.
  2: split.
  1,2: auto.
  split; auto.
Qed.

Lemma trans_in_det_trans_eq {A B} eqA eqB (g:nfa A B) Q0 Q Q' n a :
  (forall q1 q2, q1=q2 <-> eqA q1 q2=true) ->
  In (trans Q a Q') (det_trans eqA eqB g n Q0) ->
  In a (alphabet g) /\ Q' <> nil /\ eq_sets Q' (ext_transition eqA eqB g Q [a]).
Proof.
  intros; apply trans_in_det_trans in H0.
  2: auto.
  destruct H0 as [H0 [H1 H2]]; subst; split.
  2: split.
  1,2: auto.
  apply eq_sets_self.
Qed.

(* If a path from Q to Q' through w exists in the determinized NFA such that q' in Q',
then there exists q in Q such that a original path from q to q' through w exists *)
Lemma det_trans_old_path {A B} eqA eqB (g:nfa A B) n w Q0' Q0 Q Q' q' :
  (forall q1 q2, q1=q2 <-> eqA q1 q2=true) -> (forall a b, a=b <-> eqB a b=true) ->
  let start_and_trans := start Q0'::det_trans eqA eqB g n Q0 in
  In q' Q' -> path (normalize eqA (start_and_trans) (start_and_trans)) Q Q' w ->
  exists q, In q Q /\ path g q q' w.
Proof.
  intros; simpl in H2; apply app_start_path in H2;
  generalize dependent q';
  induction H2; intros.
  exists q'; intuition; constructor.
  apply in_normalize_eq_trans in H1.
  2: auto.
  destruct H1 as [Q1 [Q2 [H1 [H4 H5]]]].
  apply trans_in_det_trans_eq in H5.
  2: auto.
  destruct H5 as [H5 [_ H6]].
  assert (In q' (ext_transition eqA eqB g  q2 [a])). {
    assert (eq_sets q3 (ext_transition eqA eqB g q2 [a])).
    2: apply H7; auto.
    apply eq_sets_transitive with Q2.
    apply eq_sets_comm; auto.
    apply eq_sets_transitive with (ext_transition eqA eqB g Q1 [a]).
    apply eq_sets_comm; auto.
    apply ext_transition_eq_sets, eq_sets_comm; auto.
  }
  apply in_transition_ext in H7.
  2,3: auto.
  destruct H7 as [q'' [H7 H8]].
  apply IHpath in H7; destruct H7 as [q H7].
  exists q; split.
  2: apply path_next with q''.
  1-3: intuition.
Qed.

(* If a path from q to q' through w exists in the original NFA such that q in Q, Q is the search root
and w's length is less or equal to the fuel, then there exists Q' such that q' in Q' and a new path
from Q to Q' through w *)
Lemma det_trans_new_path {A B} eqA eqB (g:nfa A B) n w Q0 Q q q' :
  (forall q1 q2, q1=q2 <-> eqA q1 q2=true) -> (forall a b, a=b <-> eqB a b=true) ->
  let start_and_trans := start Q0::det_trans eqA eqB g n Q in
  length w <= n -> In q Q -> path g q q' w ->
  exists Q', In q' Q' /\ path (normalize eqA start_and_trans start_and_trans) (normalize_state eqA start_and_trans Q) Q' w.
Proof.
  intros. assert (exists Q', In q' Q' /\ path start_and_trans Q Q' w).
  2: {
    destruct H4 as [Q' [H4 H5]].
    apply (normalize_path eqA start_and_trans start_and_trans) in H5.
    2: auto.
    destruct H5 as [Q'' [H5 H6]]; exists Q''; split.
    apply H5; auto.
    auto.
  }
  assert (exists Q' : list A, In q' Q' /\ path (det_trans eqA eqB g n Q) Q Q' w).
  2: {
    destruct H4 as [Q' H4]; exists Q'; split.
    intuition.
    apply app_start_path; intuition.
  }
  clear start_and_trans Q0;
  generalize dependent w;
  generalize dependent q;
  generalize dependent Q.
  induction n; intros.
  - assert (w = []).
      destruct w; inversion H1; auto.
    subst.
    inversion H3; subst.
    2: destruct w; discriminate.
    exists Q; split.
    2: constructor.
    auto.
  - destruct w as [|a w].
    + inversion H3; subst.
      2: destruct w; discriminate.
      exists Q; split.
      2: constructor.
      auto.
    + assert (exists q'', In (trans q a q'') g /\ path g q'' q' w).
        apply path_left; auto.
      destruct H4 as [q'' H4].
      destruct IHn with (ext_transition eqA eqB g Q [a]) q'' w.
      3: intuition.
      2: simpl in H1; lia.
      {
        induction Q.
        destruct H2.
        destruct H2; simpl.
        subst; apply in_or_app; left; apply transition_in; intuition.
        apply in_or_app; right; intuition.
      }
      Opaque ext_transition.
      simpl det_trans.
      assert (In a (alphabet g)).
        apply trans_in_alphabet with q q''; intuition.
      clear IHn; exists x; split.
      intuition.
      assert (ext_transition eqA eqB g Q [a] <> nil). {
        assert (In q'' (ext_transition eqA eqB g Q [a])).
          apply transition_in_ext with q; intuition.
        destruct (ext_transition eqA eqB g Q [a]).
        destruct H7.
        intros contra; discriminate.
      }
      apply path_left with (ext_transition eqA eqB g Q [a]).
      apply foreach_in; auto.
      subst; induction (alphabet g).
      destruct H6.
      simpl foreach; subst.
      destruct H6.
      * subst; clear IHl; destruct (ext_transition eqA eqB g Q [a]) eqn:H8.
        destruct H7; auto.
        replace (trans Q a (a0 :: l0) :: det_trans eqA eqB g n (a0 :: l0) ++ foreach eqA eqB g (det_trans eqA eqB g n) Q l)
        with ([trans Q a (a0 :: l0)] ++ det_trans eqA eqB g n (a0 :: l0) ++ foreach eqA eqB g (det_trans eqA eqB g n) Q l).
        2: auto.
        apply path_app; right; apply path_app; left; intuition.
      * destruct (ext_transition eqA eqB g Q [a0]).
        intuition.
        replace (trans Q a0 (a1 :: l0) :: det_trans eqA eqB g n (a1 :: l0) ++ foreach eqA eqB g (det_trans eqA eqB g n) Q l)
        with ([trans Q a0 (a1 :: l0)] ++ det_trans eqA eqB g n (a1 :: l0) ++ foreach eqA eqB g (det_trans eqA eqB g n) Q l).
        2: auto.
        apply path_app; right; apply path_app; right; intuition.
      Transparent ext_transition.
Qed.

(* Every component in the transition determinization is a transition *)
Lemma in_det_trans {A B} eqA eqB (g:nfa A B) n :
  (forall q1 q2, q1=q2 <-> eqA q1 q2=true) ->
  forall Q c, In c (det_trans eqA eqB g n Q) ->
  exists Q1 a Q2, c = trans Q1 a Q2.
Proof.
  intros H10 Q c H0; generalize dependent Q;
  induction n; intros.
  destruct H0.
  simpl in H0; apply in_foreach in H0; destruct H0 as [Q' [a [H0 [H1 [H2 [H3|H3]]]]]].
  exists Q, a, Q'; symmetry; auto.
  apply IHn with Q'; auto.
Qed.

Lemma det_trans_in_states {A B} eqA eqB (g:nfa A B) Q Q1 n :
  (forall q1 q2, q1=q2 <-> eqA q1 q2=true) ->
  let g' := det_trans eqA eqB g n Q in
  In Q1 (states g') ->
  exists Q2 a, In (trans Q1 a Q2) g' \/ In (trans Q2 a Q1) g'.
Proof.
  intros;
  pose proof (in_det_trans eqA eqB g n H Q) as H2;
  apply states_in in H0; destruct H0 as [H1|[H1|[H1|[Q' [a [H1|H1]]]]]].
  - apply (H2 (state Q1)) in H1; destruct H1 as [Q2 [b [Q3 H1]]]; discriminate.
  - apply (H2 (start Q1)) in H1; destruct H1 as [Q2 [b [Q3 H1]]]; discriminate.
  - apply (H2 (accept Q1)) in H1; destruct H1 as [Q2 [b [Q3 H1]]]; discriminate.
  - exists Q', a; left; auto.
  - exists Q', a; right; auto.
Qed.

(* Every state in the transition determinization is a subset of the original states *)
Lemma in_det_trans_subset {A B} eqA eqB (g:nfa A B) n :
  (forall q1 q2, q1=q2 <-> eqA q1 q2=true) ->
  forall Q c, subset Q (states g) -> In c (det_trans eqA eqB g n Q) ->
  exists Q1 a Q2, c = trans Q1 a Q2 /\ subset Q1 (states g) /\ subset Q2 (states g).
Proof.
  intros H10;
  induction n; intros.
  destruct H0.
  simpl in H0; apply in_foreach in H0; destruct H0 as [Q' [a [H0 [H1 [H2 [H3|H3]]]]]].
  - exists Q, a, Q'; split.
    2: split.
    symmetry; auto.
    auto.
    rewrite H2; apply ext_transition_subset; auto.
  - apply IHn with Q'.
    2: auto.
    rewrite H2; apply ext_transition_subset; auto.
Qed.


(** The fuel **)

Require Import Nat pumping.

Definition pumping_length {A B} eq H (g:nfa A B) : nat := (2^length (nodup (eq_dec eq H) (states g))).


(** The accept states **)

(* Marks as accept states the ones that has an original start state *)
Fixpoint det_accept_mark {A B} eqA (g:nfa A B) states : nfa (list A) B :=
  match states with
  | nil => nil
  | Q::states =>
    if has_accept_stateb eqA g Q then
      accept Q::det_accept_mark eqA g states
    else
      det_accept_mark eqA g states
  end.

(* Every state marked is in the input set *)
Lemma state_in_det_accept_mark {A B} eqA (g:nfa A B) Q l :
  In Q (states (det_accept_mark eqA g l)) -> In Q l.
Proof.
  intros; induction l.
  destruct H.
  simpl in H; destruct (has_accept_stateb eqA g a).
  2: intuition.
  destruct H; subst; intuition.
Qed.

(* Every component in the state marking is constructed by accept *)
Lemma in_det_accept_mark {A B} eqA (g:nfa A B) l :
  forall c, In c (det_accept_mark eqA g l) -> exists q, c = accept q.
Proof.
  intros; induction l.
  destruct H.
  simpl in H; destruct (has_accept_stateb eqA g a).
  2: auto.
  destruct H.
  exists a; symmetry; auto.
  auto.
Qed.

(* The marking does not change the determinism *)
Lemma dfa_app_det_accept_mark {A B} eqA (g:nfa A B) l :
  dfa l ->
  dfa (l ++ det_accept_mark eqA g (states l)).
Proof.
  intros; apply app_accept_dfa.
  auto.
  intros.
  apply in_det_accept_mark with eqA g (states l); auto.
Qed.


(** NFA determinization **)

(* Constructs the DFA using the above functions *)
Definition det {A B} eqA eqB HeqA (g:nfa A B) :=
  let start_and_trans := start (start_states g)::det_trans eqA eqB g (pumping_length eqA HeqA g) (start_states g) in
  let normalized := normalize eqA (start_and_trans) (start_and_trans) in
  match accept_states g with
  | nil => nil
  | _ => normalized ++ det_accept_mark eqA g (states (normalized))
  end.

(* If the original NFA does not have any accept state, then it returns an empty DFA *)
Lemma det_nil {A B} eqA eqB HeqA {g:nfa A B} :
  accept_states g = [] -> det eqA eqB HeqA g = [].
Proof.
  intros; unfold det; rewrite H; auto.
Qed.


(* The states are subsets of the original states *)
Lemma det_states {A B eqA eqB} HeqA {g:nfa A B} Q :
  (forall q1 q2, q1=q2 <-> eqA q1 q2=true) ->
  In Q (states (det eqA eqB HeqA g)) ->
  forall q, In q Q -> In q (states g).
Proof.
  intros H10; unfold det; intros; destruct (accept_states g) eqn:H1.
  destruct H.
  clear H1 a l; destruct H.
  {
    assert (eq_sets Q (start_states g)).
    2: apply H1 in H0; apply start_states_subset; auto.
    rewrite <- H; apply eq_sets_comm, get_set_eq; auto.
  }
  assert (forall q Q, In q Q -> In Q (states (det_trans eqA eqB g (pumping_length eqA HeqA g) (start_states g))) -> In q (states g)). {
    clear H H0 Q q; intros q Q H0 H1.
    assert (subset (start_states g) (states g)).
      apply start_states_subset.
    apply det_trans_in_states in H1.
    2: auto.
    destruct H1 as [Q2 [a [H1|H1]]].
    - apply in_det_trans_subset in H1.
      2,3: auto.
      destruct H1 as [Q3 [b [Q5 [H1 H3]]]].
      injection H1; intros; subst.
      intuition.
    - apply in_det_trans_subset in H1.
      2,3: auto.
      destruct H1 as [Q3 [b [Q5 [H1 H3]]]].
      injection H1; intros; subst.
      intuition.
  }
  apply in_app_states_or in H; destruct H.
  - apply state_in_normalize in H.
    2: auto.
    destruct H as [Q' [H H2]]; apply H1 with Q'.
    2: auto.
    assert (eq_sets Q Q'). {
      apply eq_sets_transitive with (normalize_state eqA (start (start_states g) :: det_trans eqA eqB g (pumping_length eqA HeqA g) (start_states g)) Q').
      2: apply eq_sets_comm, get_set_eq; auto.
      rewrite H; apply eq_sets_self.
    }
    apply H3; auto.
  - apply state_in_det_accept_mark in H; destruct H.
    {
      assert (eq_sets Q (start_states g)).
      2: apply H2 in H0; apply start_states_subset; auto.
      rewrite <- H; apply eq_sets_comm, get_set_eq; auto.
    }
    apply state_in_normalize in H.
    destruct H as [Q' [H H2]]; apply H1 with Q'.
    2,3: auto.
    assert (eq_sets Q Q'). {
      apply eq_sets_transitive with (normalize_state eqA (start (start_states g) :: det_trans eqA eqB g (pumping_length eqA HeqA g) (start_states g)) Q').
      2: apply eq_sets_comm, get_set_eq; auto.
      rewrite H; apply eq_sets_self.
    }
    apply H3; auto.
Qed.

(* The equivalent states are equal *)
Lemma det_eq_states {A B} eqA eqB HeqA (g:nfa A B) Q1 Q2 :
  (forall q1 q2, q1=q2 <-> eqA q1 q2=true) ->
  let g' := (det eqA eqB HeqA g) in
  In Q1 (states g') -> In Q2 (states g') ->
  eq_sets Q1 Q2 -> Q1 = Q2.
Proof.
  unfold det; intros; destruct (accept_states g).
  destruct H0.
  apply in_app_states_or in H0; apply in_app_states_or in H1;
  destruct H0, H1.
  2,4: apply state_in_det_accept_mark in H1.
  3,4: apply state_in_det_accept_mark in H0.
  1-4: apply normalize_eq_sets with eqA (start (start_states g) :: det_trans eqA eqB g (pumping_length eqA HeqA g) (start_states g)); auto.
Qed.

(* The determinization result is a DFA *)
Lemma det_trans_dfa {A B} eqA eqB (g:nfa A B) n Q0' Q0 :
  (forall q1 q2, q1=q2 <-> eqA q1 q2=true) -> (forall a b, a=b <-> eqB a b=true) ->
  subset Q0 (states g) ->
  let start_and_trans := start Q0'::det_trans eqA eqB g n Q0 in
  dfa (normalize eqA start_and_trans start_and_trans).
Proof.
  intros H H0 H20; apply normalize_dfa.
  auto.
  intros c; intuition.
  {
    intros; destruct H2, H3; try discriminate.
    apply trans_in_det_trans_eq in H2; apply trans_in_det_trans_eq in H3.
    2-4: auto.
    apply eq_sets_transitive with (ext_transition eqA eqB g q1 [a]).
    apply eq_sets_comm; intuition.
    apply eq_sets_transitive with (ext_transition eqA eqB g q3 [a]).
    2: apply eq_sets_comm; intuition.
    apply ext_transition_eq_sets, eq_sets_comm; auto.
  }
  apply cons_dfa_start.
  2: {
    assert (forall A (l:list A), (forall x, ~ In x l) -> l = []). {
      intros; destruct l.
      auto.
      specialize (H1 a); destruct H1; intuition.
    }
    apply H1; clear H1; intros q H1; apply start_states_in in H1;
    apply in_det_trans_subset in H1.
    2,3: auto.
    destruct H1 as [Q1 [a [Q2 [H1 _]]]]; discriminate.
  }
  assert (forall (g':nfa (list A) B),
  (forall c, In c g' -> exists q a, c = trans q a (ext_transition eqA eqB g q [a])) ->
  dfa g').
  2: {
    apply H1; clear H1; intros; pose proof H1; apply in_det_trans_subset in H1.
    2,3: auto.
    destruct H1 as [Q1 [a [Q2 [H1 _]]]]; subst; apply trans_in_det_trans in H2.
    2: auto.
    exists Q1, a; destruct H2 as [H2 [H3 H4]]; subst; auto.
  }
  intros; induction g'.
  apply cons_empty_dfa, (actual_nfa_cons [] (lists_eq eqA) eqB (lists_eq_correct H) H0).
  pose proof H1; destruct H2 with a.
  left; auto.
  destruct H3 as [b H3]; subst.
  destruct (nfa_ex_trans_dec g' (actual_nfa_cons g' (lists_eq eqA) eqB (lists_eq_correct H) H0) x b).
  Opaque ext_transition.
  + destruct H3 as [y H3].
    destruct H2 with (trans x b y).
    intuition.
    destruct H4 as [b' H4]; injection H4; intros; subst.
    apply cons_dfa_trans_repeat.
    2: auto.
    apply IHg'; intros; apply H1; intuition.
  + apply cons_dfa_trans.
    2: auto.
    apply IHg'; intros; apply H1; intuition.
Qed.

Lemma det_dfa {A B eqA eqB} H {g:nfa A B} :
  (forall a b, a=b <-> eqB a b=true) ->
  dfa (det eqA eqB H g).
Proof.
  intros; unfold det; destruct (accept_states g).
  - apply cons_empty_dfa.
    apply (actual_nfa_cons [] (lists_eq eqA) eqB (lists_eq_correct H) H0).
  - apply dfa_app_det_accept_mark;
    apply det_trans_dfa.
    1,2: auto.
    apply start_states_subset.
Qed.

(* The accept states are the ones that have an original accept state *)
Lemma det_accept {A B eqA eqB} H {g:nfa A B} {Q} :
  let g' := det eqA eqB H g in
  In Q (states g') ->
  In Q (accept_states g') <-> exists q, In q Q /\ In q (accept_states g).
Proof.
  unfold det; intros.
  destruct (accept_states g) eqn:H2.
  destruct H0.
  rewrite <- H2; clear H2 a l;
  pose proof (start_states_subset g) as H10;
  remember (start_states g) as Q0 eqn:H1; clear H1;
  remember (pumping_length eqA H g) as n eqn:H1; clear H1;
  split; intros.
  - clear H0; apply accept_states_in in H1.
    destruct H1.
    discriminate.
    apply in_app_or in H0; destruct H0.
    {
      apply accept_in_normalize in H0.
      2: auto.
      destruct H0 as [Q' [_ H0]].
      apply in_det_trans_subset in H0.
      2,3: auto.
      destruct H0 as [Q1 [b [Q2 [H0 _]]]]; discriminate.
    }
    remember (states (normalize eqA (start Q0 :: det_trans eqA eqB g n Q0) (start Q0 :: det_trans eqA eqB g n Q0))) as l eqn:H1; clear H1.
    induction l.
    destruct H0.
    simpl in H0.
    destruct (has_accept_stateb eqA g a) eqn:H1.
    2: intuition.
    destruct H0.
    2: intuition.
    injection H0; intros; subst.
    apply has_accept_stateb_correct in H1; auto.
  - assert (In Q (states (normalize eqA (start Q0 :: det_trans eqA eqB g n Q0) (start Q0 :: det_trans eqA eqB g n Q0)))). {
      apply in_app_states_or in H0; destruct H0.
      auto.
      apply state_in_det_accept_mark in H0; auto.
    }
    clear H0;
    remember (normalize eqA (start Q0 :: det_trans eqA eqB g n Q0) (start Q0 :: det_trans eqA eqB g n Q0)) as l eqn:H0; clear H0.
    apply accept_states_in; apply in_or_app; right;
    induction l.
    destruct H2.
    destruct a.
    + destruct H2; subst.
      * assert (has_accept_stateb eqA g Q = true).
          apply has_accept_stateb_correct; auto.
        simpl; rewrite H0; left; auto.
      * simpl; destruct (has_accept_stateb eqA g q).
        right.
        1,2: intuition.
    + intuition.
    + destruct H2; subst.
      * assert (has_accept_stateb eqA g Q = true).
          apply has_accept_stateb_correct; auto.
        simpl; rewrite H0; left; auto.
      * simpl; destruct (has_accept_stateb eqA g q).
        right.
        1,2: intuition.
    + destruct H2; subst.
      * assert (has_accept_stateb eqA g Q = true).
          apply has_accept_stateb_correct; auto.
        simpl; rewrite H0; left; auto.
      * simpl; destruct (has_accept_stateb eqA g q).
        right.
        1,2: intuition.
    + destruct H2; subst.
      2: destruct H0; subst.
      * assert (has_accept_stateb eqA g Q = true).
          apply has_accept_stateb_correct; auto.
        simpl; rewrite H0; left; auto.
      * assert (has_accept_stateb eqA g Q = true).
          apply has_accept_stateb_correct; auto.
        simpl; destruct (has_accept_stateb eqA g q).
        right.
        1,2: simpl; rewrite H0; left; auto.
      * simpl; destruct (has_accept_stateb eqA g q), (has_accept_stateb eqA g q'); try right; try right.
        1-4: intuition.
Qed.

(* All states are reachable *)
Lemma normalized_det_trans_reach {A B} eqA eqB (g:nfa A B) Q Q0 n l :
  (forall q1 q2, q1=q2 <-> eqA q1 q2=true) -> (forall a b, a=b <-> eqB a b=true) ->
  let g' := normalize eqA (det_trans eqA eqB g n Q0) l in
  In Q (states g') -> exists w, path g' (normalize_state eqA l Q0) Q w.
Proof.
  intros.
  apply normalize_ext_transition.
  1,3: auto.
  clear H1 g' Q l; intros;
  apply det_trans_in_states in H1.
  2: auto.
  destruct H1 as [Q' [a [H1|H1]]].
  - generalize dependent Q0; induction n; intros.
    destruct H1.
    simpl in H1; apply in_foreach in H1; destruct H1 as [Q1 [b [H1 [H2 [H3 [H4|H4]]]]]].
    + injection H4; intros; subst.
      exists nil; constructor.
    + apply IHn in H4; clear IHn; destruct H4 as [w H4]; exists (b::w).
      apply path_left with Q1; subst.
      simpl; apply foreach_in; auto.
      simpl; apply path_foreach with b; subst; intuition.
  - generalize dependent Q0; induction n; intros.
    destruct H1.
    simpl in H1; apply in_foreach in H1; destruct H1 as [Q1 [b [H1 [H2 [H3 [H4|H4]]]]]].
    + injection H4; intros; subst; clear IHn; exists (nil ++ [a]);
      apply path_next with Q'.
      constructor.
      apply foreach_in; auto.
    + apply IHn in H4; clear IHn; destruct H4 as [w H4]; exists (b::w).
      apply path_left with Q1; subst.
      simpl; apply foreach_in; auto.
      simpl; apply path_foreach with b; subst; intuition.
Qed.

Lemma det_reach {A B} eqA eqB H (g:nfa A B) Q :
  (forall a b, a=b <-> eqB a b=true) ->
  let g' := det eqA eqB H g in
  In Q (states g') -> exists w, path g' (start_states g) Q w.
Proof.
  intros; unfold det in g'; destruct (accept_states g).
  destruct H1.
  assert (forall Q0 n l, In Q (states (normalize eqA (start Q0::det_trans eqA eqB g n Q0) (start Q0::l))) ->
  exists w1, path (normalize eqA (start Q0::det_trans eqA eqB g n Q0) (start Q0::l)) Q0 Q w1).
  2: {
    apply in_app_states_or in H1; destruct H1.
    apply H2 in H1; destruct H1 as [w H1]; exists w; apply path_app; intuition.
    apply state_in_det_accept_mark in H1; apply H2 in H1; destruct H1 as [w H1]; exists w; apply path_app; intuition.
  }
  clear H1 g'; intros; simpl in H1; destruct H1; subst.
  {
    unfold normalize_state; simpl; assert (eq_setsb eqA Q0 Q0 = true).
    apply eq_setsb_correct; try apply eq_sets_self; auto.
    rewrite H1; exists nil; constructor.
  }
  assert (normalize_state eqA (start Q0 :: l0) Q0 = Q0). {
    unfold normalize_state; simpl; assert (eq_setsb eqA Q0 Q0 = true).
      apply eq_setsb_correct; try apply eq_sets_self; auto.
    rewrite H2; auto.
  }
  clear l; remember (start Q0::l0) as l eqn:H3; clear H3.
  assert (exists w, path  (normalize eqA (det_trans eqA eqB g n Q0) l) Q0 Q w).
  2: {
    destruct H3 as [w H3]; exists w; simpl; replace (start (normalize_state eqA l Q0) :: normalize eqA (det_trans eqA eqB g n Q0) l) with
    ([start (normalize_state eqA l Q0)] ++ normalize eqA (det_trans eqA eqB g n Q0) l).
    2: auto.
    apply path_app; right; auto.
  }
  apply normalized_det_trans_reach in H1.
  2,3: auto.
  rewrite H2 in H1; destruct H1 as [w H1]; exists w; auto.
Qed.

(* Now we extend det_trans_new_path for any word *)
Lemma det_path {A B} eqA eqB H (g:nfa A B) q' w :
  (forall a b, a=b <-> eqB a b=true) ->
  let g' := (det eqA eqB H g) in
  (forall Q Q', path g' Q Q' w /\ In q' Q' -> exists q, path g q q' w /\ In q Q) /\
  (accept_states g <> nil -> forall q, path g q q' w /\ In q (start_states g) -> exists Q', path g' (start_states g) Q' w /\ In q' Q').
Proof.
  intros; split; intros.
  {
    destruct H1 as [H1 H2].
    unfold det in g'; destruct (accept_states g).
    + inversion H1; subst.
      exists q'; split; try constructor; auto.
      destruct H4.
    + apply path_app_accept in H1.
      2: apply in_det_accept_mark.
      apply (det_trans_old_path eqA eqB g (pumping_length eqA H g) w (start_states g) (start_states g) Q Q' q') in H1.
      2-4: auto.
      destruct H1 as [q H1]; exists q; split; intuition.
  }
  unfold det in g'; destruct (accept_states g).
  destruct H1; auto.
  assert (exists Q', path (normalize eqA (start (start_states g) :: det_trans eqA eqB g (pumping_length eqA H g) (start_states g))
    (start (start_states g) :: det_trans eqA eqB g (pumping_length eqA H g) (start_states g))) (start_states g) Q' w /\ In q' Q').
  2: destruct H3 as [Q' H3]; exists Q'; split; try (apply path_app; left); intuition.
  clear g'; remember (start (start_states g) :: det_trans eqA eqB g (pumping_length eqA H g) (start_states g)) as start_and_trans eqn:H3.
  replace (start_states g) with (normalize_state eqA start_and_trans (start_states g)).
  2: {
    unfold normalize_state; rewrite H3; simpl; assert (eq_setsb eqA (start_states g) (start_states g) = true).
      apply eq_setsb_correct; try apply eq_sets_self; auto.
    rewrite H4; auto.
  }
  assert (exists Q', In q' Q' /\ path (normalize eqA start_and_trans start_and_trans) (normalize_state eqA start_and_trans (start_states g)) Q' w).
  2: destruct H4 as [Q' H4]; exists Q'; intuition.
  pose proof (det_trans_new_path eqA eqB g (length w) w (start_states g) (start_states g) q q' H H0).
  assert (length w <= length w).
    nia.
  apply H4 in H5; clear H4.
  2,3: intuition.
  destruct H5 as [Q' [H4 H5]].
  remember (start (start_states g) :: det_trans eqA eqB g (length w) (start_states g)) as start_and_trans' eqn:H6.
  assert ((normalize_state eqA start_and_trans (start_states g)) = start_states g). {
    rewrite H3; unfold normalize_state; simpl.
    assert (eq_setsb eqA (start_states g) (start_states g) = true).
      apply eq_setsb_correct; try apply eq_sets_self; auto.
    rewrite H7; auto.
  }
  assert ((normalize_state eqA start_and_trans' (start_states g)) = start_states g). {
    rewrite H6; unfold normalize_state; simpl.
    assert (eq_setsb eqA (start_states g) (start_states g) = true).
      apply eq_setsb_correct; try apply eq_sets_self; auto.
    rewrite H8; auto.
  }
  assert (exists Q'', eq_sets Q' Q'' /\ path  (normalize eqA start_and_trans start_and_trans) (start_states g) Q'' w).
  2: destruct H9 as [Q'' [H9 H10]]; exists Q''; split.
  2: apply H9; auto.
  2: rewrite H7; auto.
  apply pumping_language_eq with (lists_eq eqA) (lists_eq_correct H) (normalize eqA start_and_trans' start_and_trans') (start_states g).
  2: apply eq_sets_self.
  4: rewrite <- H8; auto.
  3: intros; apply normalize_eq_sets with eqA (start_and_trans); auto.
  rewrite H3; apply det_trans_dfa; try apply start_states_subset; auto.
  intros.
Admitted.

(* Basically a generalization on the last lemma for any path *)
Lemma det_path_reach {A B eqA eqB} H {g:nfa A B} {Q q' w} :
  (forall a b, a=b <-> eqB a b=true) ->
  let g' := (det eqA eqB H g) in
  (forall Q', path g' Q Q' w /\ In q' Q' -> exists q, path g q q' w /\ In q Q) /\
  (forall q, In Q (states g') ->
  path g q q' w /\ In q Q -> exists Q', path g' Q Q' w /\ In q' Q').
Proof.
  revert w; intro w2; intros; split.
  apply det_path; auto.
  intros; assert (accept_states g <> nil). {
    unfold det in g'; destruct (accept_states g).
    destruct H1.
    intros contra; discriminate.
  }
  intros; assert (exists w1, path g' (start_states g) Q w1).
    apply det_reach; auto.
  destruct H4 as [w1 H4].
  assert (exists q0, path g q0 q w1 /\ In q0 (start_states g)). {
    destruct (det_path eqA eqB H g q w1 H0) as [H5 _]; destruct H5 with (start_states g) Q.
    split; intuition.
    exists x; auto.
  }
  destruct H5 as [q0 H5]; assert (path g q0 q' (w1++w2) /\ In q0 (start_states g)).
    split; try apply path_transitive with q; intuition.
  pose proof (det_path eqA eqB H g q' (w1++w2) H0) as [_ H7];
  apply H7 with q0 in H3; clear H7.
  2: auto.
  destruct H3 as [Q' H3]; exists Q'; split.
  2: intuition.
  destruct H3 as [H3 _]; clear H1 H2 H5 H6 q0.
  replace (det eqA eqB H g) with g' in H3.
  2: auto.
  assert (dfa g').
    apply det_dfa; auto.
  generalize dependent g';
  generalize dependent (start_states g);
  induction w1; intros Q0; intros.
  {
    inversion H4; subst.
    intuition.
    destruct w; discriminate.
  }
  assert (exists Q1, In (trans Q0 a Q1) g' /\ path g' Q1 Q w1 /\ path g' Q1 Q' (w1 ++ w2)).
  2: destruct H2 as [Q1 H2]; apply IHw1 with Q1; intuition.
  clear IHw1; generalize dependent Q'; induction w2 using rev_ind; intros.
  - rewrite app_nil_r; rewrite app_nil_r in H3.
    assert (Q = Q').
      apply dfa_path with g' Q0 (a::w1); auto.
    subst; clear H3; apply path_left in H4; destruct H4 as [Q1 H4]; exists Q1.
    split.
    2: split.
    1-3: intuition.
  - inversion H3; subst.
    replace (a :: w1 ++ w2 ++ [x]) with (((a :: w1) ++ w2) ++ [x]) in H2.
    2: rewrite <- app_assoc; simpl; auto.
    apply app_inj_tail in H2; destruct H2; subst.
    apply IHw2 in H5; destruct H5 as [Q1 H5]; exists Q1; split.
    2: split.
    1,2: intuition.
    replace (w1 ++ w2 ++ [x]) with ((w1 ++ w2) ++ [x]).
    2: rewrite app_assoc; auto.
    apply path_next with q2; intuition.
Qed.

(* The start state is the set of the original start states *)
Lemma det_start_states {A B} eqA eqB H (g:nfa A B) :
  det eqA eqB H g <> nil ->
  start_states (det eqA eqB H g) = [start_states g].
Proof.
  unfold det; intros; destruct (accept_states g).
  destruct H0; auto.
  clear H0 l.
  rewrite app_start_states_nil.
  2: {
    remember (states (normalize eqA (start (start_states g) :: det_trans eqA eqB g (pumping_length eqA H g) (start_states g))
     (start (start_states g) :: det_trans eqA eqB g (pumping_length eqA H g) (start_states g)))) as l eqn:H0; clear H0.
    induction l.
    auto.
    simpl; destruct (has_accept_stateb eqA g a0); auto.
  }
  simpl; unfold normalize_state; simpl.
  assert (eq_setsb eqA (start_states g) (start_states g) = true).
    apply eq_setsb_correct; auto; split; auto.
  rewrite H0.
  assert (start_states (normalize eqA (det_trans eqA eqB g (pumping_length eqA H g) (start_states g))
    (start (start_states g) :: det_trans eqA eqB g (pumping_length eqA H g) (start_states g))) = nil).
  2: rewrite H1; auto.
  apply normalize_start_states_nil.
  clear H0 a;
  generalize dependent (start_states g);
  induction (pumping_length eqA H g); intros.
  auto.
  simpl; induction (alphabet g).
  auto.
  Opaque ext_transition.
  simpl; destruct (ext_transition eqA eqB g l [a]) eqn:H0.
  auto.
  simpl; rewrite <- (IHn (a0::l1)); apply app_start_states_nil.
  auto.
  Transparent ext_transition.
Qed.

(* The language maintains *)
Lemma det_language {A B} eqA eqB H (g:nfa A B) :
  (forall a b, a=b <-> eqB a b=true) ->
  equivalent_nfas eqA eqB (lists_eq eqA) g (det eqA eqB H g).
Proof.
  unfold equivalent_nfas; intros;
  unfold lang; intros; split; intros.
  - destruct H1 as [q [H1 H2]].
    apply ext_transition_list in H1; destruct H1 as [q0 [H1 H3]].
    apply path_ext_transition in H3.
    2,3: auto.
    assert (accept_states g <> nil). {
      destruct (accept_states g).
      destruct H2.
      intros contra; discriminate.
    }
    destruct (det_path eqA eqB H g q w H0) as [_ H5].
    destruct (H5 H4) with q0.
    intuition.
    clear H4; destruct H6 as [H4 H6].
    exists x; split.
    + rewrite det_start_states.
      2: auto.
      2: {
        assert (In x (ext_transition (lists_eq eqA) eqB (det eqA eqB H g) [start_states g] w)).
          apply path_ext_transition; try apply lists_eq_correct; auto.
        assert (In (start_states g) (start_states (det eqA eqB H g))). {
          rewrite det_start_states.
          1,2: try left; auto.
          unfold det; destruct (accept_states g).
          destruct H2.
          simpl; discriminate.
        }
        clear H1 H2 H3 H4 H5 H6; destruct (det eqA eqB H g).
        2: intros contra; discriminate.
        generalize dependent [start_states g]; induction w; intros.
        2: simpl in H7; apply IHw in H7; auto.
        destruct H8.
      }
      apply path_ext_transition.
      1-3: try apply lists_eq_correct; auto.
    + apply (det_accept H).
      2: exists q; intuition.
      assert (In x (ext_transition (lists_eq eqA) eqB (det eqA eqB H g) [start_states g] w)).
        apply path_ext_transition; try apply lists_eq_correct; auto.
      apply ext_transition_in_states in H7.
      auto.
      intros; destruct H8; subst.
      2: destruct H8.
      apply start_states_subset.
      rewrite det_start_states.
      1,2: try left; auto.
      unfold det; destruct (accept_states g).
      destruct H2.
      simpl; discriminate.
  - destruct H1 as [Q' [H1 H2]].
    rewrite det_start_states in H1.
    2: auto.
    2: {
      unfold det; unfold det in H2; destruct (accept_states g).
      destruct H2.
      simpl; intros contra; discriminate.
    }
    apply path_ext_transition in H1.
    2,3: try apply lists_eq_correct; auto.
    assert (exists q, In q Q' /\ In q (accept_states g)). {
      assert (In Q' (states (det eqA eqB H g))).
        apply accept_states_subset; auto.
      apply (det_accept H H3); auto.
    }
    destruct H3 as [q' H4].
    destruct (det_path eqA eqB H g q' w H0) as [H5 _].
    destruct H5 with (start_states g) Q'.
    intuition.
    destruct H3 as [H3 H7].
    exists q'; split.
    2: intuition.
    apply ext_transition_single with x; split.
    auto.
    apply path_ext_transition; auto.
Qed.













