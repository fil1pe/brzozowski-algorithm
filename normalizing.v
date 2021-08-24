Require Import List Bool Lia utils nfa.
Include ListNotations.


(* Normalize a state means replacing it with an equivalent in the NFA *)
Definition normalize_state {A B} eq (g:nfa (list A) B) Q :=
  get_set eq Q (states g).

(* The normalized state is an equivalent in the NFA or itself *)
Lemma normalize_state_or {A B} eq (g:nfa (list A) B) Q :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  normalize_state eq g Q = Q \/ In (normalize_state eq g Q) (states g).
Proof.
  unfold normalize_state; intros; generalize dependent (states g); intros; induction l.
  left; intuition.
  simpl; destruct (eq_setsb eq Q a).
  right; left; auto.
  destruct IHl; intuition.
Qed.

(* The state normalization is equal for equivalent states that has equivalent in the NFA *)
Lemma normalize_state_eq_sets {A B} eq (g:nfa (list A) B) Q1 Q2 :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  (exists Q1', eq_sets Q1 Q1' /\ In Q1' (states g)) ->
  (exists Q2', eq_sets Q2 Q2' /\ In Q2' (states g)) ->
  eq_sets Q1 Q2 ->
  normalize_state eq g Q1 = normalize_state eq g Q2.
Proof.
  unfold normalize_state; intros; generalize dependent (states g); intros; induction l.
  destruct H0 as [Q1' [_ []]].
  simpl; assert (eq_setsb eq Q1 a = eq_setsb eq Q2 a). {
    destruct (eq_setsb eq Q1 a) eqn:H3, (eq_setsb eq Q2 a) eqn:H4.
    1,4: auto.
    - apply eq_setsb_correct in H3.
      2: auto.
      assert (eq_setsb eq Q2 a = true).
      2: rewrite H4 in H5; discriminate.
      apply eq_setsb_correct.
      auto.
      apply eq_sets_transitive with Q1; auto.
    - apply eq_setsb_correct in H4.
      2: auto.
      assert (eq_setsb eq Q1 a = true).
      2: rewrite H3 in H5; discriminate.
      apply eq_setsb_correct.
      auto.
      apply eq_sets_transitive with Q2.
      apply eq_sets_comm.
      1,2: auto.
  }
  destruct (eq_setsb eq Q2 a) eqn:H4; rewrite H3.
  auto.
  apply IHl.
  - clear H1; destruct H0 as [Q1' [H0 [H1|H1]]]; subst.
    + assert (eq_setsb eq Q1 Q1' = true).
        apply eq_setsb_correct; auto.
      rewrite H1 in H3; discriminate.
    + exists Q1'; intuition.
  - clear H0; destruct H1 as [Q2' [H0 [H1|H1]]]; subst.
    + assert (eq_setsb eq Q2 Q2' = true).
        apply eq_setsb_correct; auto.
      rewrite H1 in H4; discriminate.
    + exists Q2'; intuition.
Qed.


(** NFA normalization **)

(* Applies the state normalization recursively *)
Fixpoint normalize {A B} eq (g g':nfa (list A) B) :=
  match g with
  | nil => nil
  | state Q::g => state (normalize_state eq g' Q)::normalize eq g g'
  | symbol a::g => symbol a::normalize eq g g'
  | start Q::g => start (normalize_state eq g' Q)::normalize eq g g'
  | accept Q::g => accept (normalize_state eq g' Q)::normalize eq g g'
  | trans Q a Q'::g => trans (normalize_state eq g' Q) a (normalize_state eq g' Q')::normalize eq g g'
  end.

(* Every state is the result of a state normalization *)
Lemma in_normalize {A B} eq (g g':nfa (list A) B) Q :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  In Q (states (normalize eq g g')) ->
  exists Q', Q = normalize_state eq g' Q' /\ eq_sets Q Q'.
Proof.
  intros; generalize dependent g'; induction g; intros.
  destruct H0.
  destruct a.
  - simpl in H0; destruct H0.
    2: apply IHg; auto.
    exists q; split.
    symmetry; auto.
    rewrite <- H0; apply eq_sets_comm, get_set_eq; auto.
  - apply IHg; auto.
  - simpl in H0; destruct H0.
    2: apply IHg; auto.
    exists q; split.
    symmetry; auto.
    rewrite <- H0; apply eq_sets_comm, get_set_eq; auto.
  - simpl in H0; destruct H0.
    2: apply IHg; auto.
    exists q; split.
    symmetry; auto.
    rewrite <- H0; apply eq_sets_comm, get_set_eq; auto.
  - simpl in H0; destruct H0.
    2: simpl in H0; destruct H0.
    3: apply IHg; auto.
    exists q; split.
    symmetry; auto.
    rewrite <- H0; apply eq_sets_comm, get_set_eq; auto.
    exists q'; split.
    symmetry; auto.
    rewrite <- H0; apply eq_sets_comm, get_set_eq; auto.
Qed.

(* The normalization whose inputs are equal NFAs is complete:
all equivalent states are equal *)
Lemma normalize_eq_sets_generic {A B} eq (g g':nfa (list A) B) Q1 Q2 :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  In Q1 (states (normalize eq g g')) -> In Q1 (states g') ->
  In Q2 (states (normalize eq g g')) -> In Q2 (states g') ->
  eq_sets Q1 Q2 ->
  Q1 = Q2.
Proof.
  intros.
  apply in_normalize in H0; apply in_normalize in H2.
  2-4: auto.
  destruct H0 as [Q1' [H0 H5]]; destruct H2 as [Q2' [H2 H6]]; subst.
  apply normalize_state_eq_sets.
  auto.
  - exists (normalize_state eq g' Q1'); split.
    apply eq_sets_comm.
    1,2: auto.
  - exists (normalize_state eq g' Q2'); split.
    apply eq_sets_comm.
    1,2: auto.
  - apply eq_sets_transitive with (normalize_state eq g' Q1').
    auto.
    apply eq_sets_transitive with (normalize_state eq g' Q2').
    apply eq_sets_comm; auto.
    auto.
Qed.

Lemma normalize_eq_sets {A B} eq (g:nfa (list A) B) Q1 Q2 :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  In Q1 (states (normalize eq g g)) ->
  In Q2 (states (normalize eq g g)) ->
  eq_sets Q1 Q2 ->
  Q1 = Q2.
Proof.
  intros H.
  assert (forall Q g', In Q (states (normalize eq g g')) -> In Q (states g') \/ In Q (states g)). {
    intros; generalize dependent g'; induction g; intros.
    destruct H0.
    destruct a.
    - destruct H0.
      + simpl; destruct (normalize_state_or eq g' q H).
        right; left; rewrite <- H1; auto.
        left; rewrite <- H0; auto.
      + apply IHg in H0; destruct H0.
        left; auto.
        right; right; auto.
    - apply IHg; auto.
    - destruct H0.
      + simpl; destruct (normalize_state_or eq g' q H).
        right; left; rewrite <- H1; auto.
        left; rewrite <- H0; auto.
      + apply IHg in H0; destruct H0.
        left; auto.
        right; right; auto.
    - destruct H0.
      + simpl; destruct (normalize_state_or eq g' q H).
        right; left; rewrite <- H1; auto.
        left; rewrite <- H0; auto.
      + apply IHg in H0; destruct H0.
        left; auto.
        right; right; auto.
    - destruct H0.
      2: destruct H0.
      + simpl; destruct (normalize_state_or eq g' q H).
        right; left; rewrite <- H1; auto.
        left; rewrite <- H0; auto.
      + simpl; destruct (normalize_state_or eq g' q' H).
        right; right; left; rewrite <- H1; auto.
        left; rewrite <- H0; auto.
      + apply IHg in H0; destruct H0.
        left; auto.
        right; right; intuition.
  }
  intros; apply normalize_eq_sets_generic with eq g g.
  1,2,4,6: auto.
  - apply H0 in H1; destruct H1; auto.
  - apply H0 in H2; destruct H2; auto.
Qed.

(* The normalized accept state is equivalent to another in the original NFA *)
Lemma accept_in_normalize {A B} eq (g:nfa (list A) B) l Q :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  In (accept Q) (normalize eq g l) -> exists Q', eq_sets Q Q' /\ In (accept Q') g.
Proof.
  intros;
  generalize dependent l;
  induction g; intros.
  destruct H0.
  destruct a.
  - destruct H0.
    discriminate.
    apply IHg in H0; destruct H0 as [Q' H0]; exists Q'; split.
    intuition.
    right; intuition.
  - destruct H0.
    discriminate.
    apply IHg in H0; destruct H0 as [Q' H0]; exists Q'; split.
    intuition.
    right; intuition.
  - destruct H0.
    discriminate.
    apply IHg in H0; destruct H0 as [Q' H0]; exists Q'; split.
    intuition.
    right; intuition.
  - destruct H0.
    + injection H0; intros; subst; exists q; split.
      2: intuition.
      apply eq_sets_comm, get_set_eq; auto.
    + apply IHg in H0; destruct H0 as [Q' H0]; exists Q'; split.
      intuition.
      right; intuition.
  - destruct H0.
    discriminate.
    apply IHg in H0; destruct H0 as [Q' H0]; exists Q'; split.
    intuition.
    right; intuition.
Qed.

(* Indeed any normalized state is equivalent to another in the original NFA *)
Lemma state_in_normalize {A B} eq (g:nfa (list A) B) l Q :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  In Q (states (normalize eq g l)) -> exists Q', Q = normalize_state eq l Q' /\ In Q' (states g).
Proof.
  intros;
  generalize dependent l;
  induction g; intros.
  destruct H0.
  destruct a.
  - destruct H0.
    + exists q; split.
      symmetry; auto.
      left; auto.
    + apply IHg in H0; destruct H0 as [Q' H0]; exists Q'; split.
      intuition.
      right; intuition.
  - apply IHg in H0; auto.
  - destruct H0.
    + exists q; split.
      symmetry; auto.
      left; auto.
    + apply IHg in H0; destruct H0 as [Q' H0]; exists Q'; split.
      intuition.
      right; intuition.
  - destruct H0.
    + exists q; split.
      symmetry; auto.
      left; auto.
    + apply IHg in H0; destruct H0 as [Q' H0]; exists Q'; split.
      intuition.
      right; intuition.
  - destruct H0.
    2: destruct H0.
    + exists q; split.
      symmetry; auto.
      left; auto.
    + exists q'; split.
      symmetry; auto.
      right; left; auto.
    + apply IHg in H0; destruct H0 as [Q' H0]; exists Q'; split.
      intuition.
      right; intuition.
Qed.

(* If the NFA does not have start states, its normalization will either *)
Lemma normalize_start_states_nil {A B} eq (g:nfa (list A) B) l :
  start_states g = nil -> start_states (normalize eq g l) = nil.
Proof.
  intros; generalize dependent l; induction g; intros.
  auto.
  destruct a.
  1,2,4,5: apply IHg, H.
  discriminate.
Qed.

(* The normalized start state is in the normalization *)
Lemma normalize_in_start_states {A B} eq (g:nfa (list A) B) l q :
  In q (start_states g) ->
  In (normalize_state eq l q) (start_states (normalize eq g l)).
Proof.
  intros;
  generalize dependent l;
  induction g; intros.
  destruct H.
  destruct a.
  1,2,4,5: simpl in *; intuition.
  simpl in *; destruct H; subst; intuition.
Qed.

(* The same is true for the normalized transitions *)
Lemma normalize_trans_in {A B} eq (g:nfa (list A) B) l q a q' :
  In (trans q a q') g ->
  In (trans (normalize_state eq l q) a (normalize_state eq l q')) (normalize eq g l).
Proof.
  intros;
  generalize dependent l;
  induction g; intros.
  destruct H.
  destruct a0.
  1-4: simpl in *; destruct H; try discriminate; intuition.
  simpl in H; destruct H.
  injection H; intros; subst; simpl; intuition.
  simpl in *; intuition.
Qed.

(* A normalized transition is equivalent to another in the original NFA *)
Lemma in_normalize_eq_trans {A B} eq (g:nfa (list A) B) l q a q' :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  In (trans q a q') (normalize eq g l) -> exists q0 q0', eq_sets q q0 /\ eq_sets q' q0' /\ In (trans q0 a q0') g.
Proof.
  intros H10; generalize dependent l; induction g; intros.
  intros; destruct H.
  destruct a0.
  1-4: destruct H; try discriminate; apply IHg in H; destruct H as [q1 [q2 H]]; exists q1, q2; intuition.
  destruct H.
  2: apply IHg in H; destruct H as [q1 [q2 H]]; exists q1, q2; intuition.
  injection H; intros; subst; clear IHg; exists q0, q'0; split.
  2: split.
  1,2: apply eq_sets_comm, get_set_eq; auto.
  intuition.
Qed.

(* We can apply the state normalization to equivalent transitions in the original NFA,
such that the NFA normalization will have the normalized transition *)
Lemma normalize_eq_trans_in {A B} eq (g:nfa (list A) B) l q1 q2 a q3 q4 :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  subset g l ->
  eq_sets q1 q3 ->
  eq_sets q2 q4 ->
  In (trans q1 a q2) g ->
  In (trans (normalize_state eq l q3) a (normalize_state eq l q4)) (normalize eq g l).
Proof.
  intros H10; intros; generalize dependent l; induction g; intros.
  destruct H2.
  destruct a0.
  - simpl; right; apply IHg.
    destruct H2; try discriminate; auto.
    intros Q H3; apply H; intuition.
  - simpl; right; apply IHg.
    destruct H2; try discriminate; auto.
    intros Q H3; apply H; intuition.
  - simpl; right; apply IHg.
    destruct H2; try discriminate; auto.
    intros Q H3; apply H; intuition.
  - simpl; right; apply IHg.
    destruct H2; try discriminate; auto.
    intros Q H3; apply H; intuition.
  - destruct H2.
    + simpl; injection H2; intros; subst; clear IHg; left.
      assert (In (trans q1 a q2) l).
        apply H; intuition.
      clear H2 H g; unfold normalize_state; induction l.
      destruct H3.
      assert (forall q, eq_setsb eq q q = true).
        intros; apply eq_setsb_correct; try apply eq_sets_self; auto.
      assert (eq_setsb eq q1 q3 = true).
        apply eq_setsb_correct; auto.
      assert (eq_setsb eq q2 q4 = true).
        apply eq_setsb_correct; auto.
      assert (eq_setsb eq q3 q1 = true).
        rewrite eq_setsb_comm; auto.
      assert (eq_setsb eq q4 q2 = true).
        rewrite eq_setsb_comm; auto.
      destruct H3; subst.
      * simpl; repeat rewrite H; rewrite H5, H6.
        rewrite (eq_setsb_equals eq q2 q4 q1).
        2,3: auto.
        destruct (eq_setsb eq q4 q1); auto.
      * apply IHl in H3; clear IHl.
        injection H3; intros; subst.
        destruct a0.
        -- simpl; rewrite (eq_setsb_equals eq q1 q3 q), (eq_setsb_equals eq q2 q4 q).
          2-5: auto.
          destruct (eq_setsb eq q3 q), (eq_setsb eq q4 q);
          try rewrite H7; try rewrite H8; auto.
        -- simpl; rewrite H7, H8; auto.
        -- simpl; rewrite (eq_setsb_equals eq q1 q3 q), (eq_setsb_equals eq q2 q4 q).
          2-5: auto.
          destruct (eq_setsb eq q3 q), (eq_setsb eq q4 q);
          try rewrite H7; try rewrite H8; auto.
        -- simpl; rewrite (eq_setsb_equals eq q1 q3 q), (eq_setsb_equals eq q2 q4 q).
          2-5: auto.
          destruct (eq_setsb eq q3 q), (eq_setsb eq q4 q);
          try rewrite H7; try rewrite H8; auto.
        -- simpl. rewrite (eq_setsb_equals eq q1 q3 q), (eq_setsb_equals eq q2 q4 q),
          (eq_setsb_equals eq q1 q3 q'), (eq_setsb_equals eq q2 q4 q').
          2-9: auto.
          destruct (eq_setsb eq q3 q), (eq_setsb eq q3 q'), (eq_setsb eq q4 q), (eq_setsb eq q4 q');
          try rewrite H7; try rewrite H8; auto.
    + right; apply IHg.
      auto.
      intros Q H3; apply H; intuition.
Qed.

(* The original paths maintain *)
Lemma normalize_path  {A B} eq (g:nfa (list A) B) l q q' w :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  path g q q' w ->
  exists q'', eq_sets q' q'' /\ path (normalize eq g l) (normalize_state eq l q) q'' w.
Proof.
  intros H10; intros.
  generalize dependent q;
  induction w; intros.
  - inversion H; subst.
    2: destruct w; discriminate.
    exists (normalize_state eq l q'); split.
    2: constructor.
    apply get_set_eq; auto.
  - apply path_left in H; destruct H as [q1 [H H0]].
    apply IHw in H0; destruct H0 as [q'' [H0 H1]].
    exists q''; split.
    auto.
    apply path_left with (normalize_state eq l q1).
    2: auto.
    apply normalize_trans_in; auto.
Qed.

(* If all the original states are reachable from Q0, then are the new states reachable from
Q0 normalized *)
Lemma normalize_ext_transition {A B} eq (g l:nfa (list A) B) Q0 :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  (forall Q, In Q (states g) -> exists w, path g Q0 Q w) ->
  forall Q, In Q (states (normalize eq g l)) -> exists w, path (normalize eq g l) (normalize_state eq l Q0) Q w.
Proof.
  intros.
  apply state_in_normalize in H1.
  2: auto.
  destruct H1 as [Q' [H1 H3]]; subst.
  apply H0 in H3; destruct H3 as [w H3]; clear H0.
  exists w; induction H3.
  constructor.
  apply path_next with (normalize_state eq l q2).
  auto.
  apply normalize_trans_in; auto.
Qed.


(** DFA normalization **)

Require Import dfa.


(* We can decide whether a transition from a given state and through a given symbol exists *)
Lemma nfa_ex_trans_dec {A B} (g:nfa A B) :
  actual_nfa g ->
  forall q a, (exists q', In (trans q a q') g) \/ (forall q', ~ In (trans q a q') g).
Proof.
  intros; inversion H; subst.
  induction g.
  intuition.
  assert (actual_nfa g).
    apply (actual_nfa_cons g eqA eqB H0 H1).
  apply IHg in H2; clear IHg; destruct H2 as [[q' H2]|H2].
  left; exists q'; intuition.
  destruct a0.
  - right; intros q' contra.
    simpl in contra; destruct contra.
    discriminate.
    apply H2 in H3; auto.
  - right; intros q' contra.
    simpl in contra; destruct contra.
    discriminate.
    apply H2 in H3; auto.
  - right; intros q' contra.
    simpl in contra; destruct contra.
    discriminate.
    apply H2 in H3; auto.
  - right; intros q' contra.
    simpl in contra; destruct contra.
    discriminate.
    apply H2 in H3; auto.
  - destruct (eqA q q0) eqn:H3.
    + apply H0 in H3; subst.
      destruct (eqB a a0) eqn:H4.
      apply H1 in H4; subst; left; exists q'; intuition.
      right; intros; intros contra; destruct contra.
      injection H3; intros; symmetry in H6;
      apply H1 in H6; rewrite H6 in H4; discriminate.
      apply H2 in H3; auto.
    + right; intros; intros contra; destruct contra.
      injection H4; intros; symmetry in H7;
      apply H0 in H7; rewrite H7 in H3; discriminate.
      apply H2 in H4; auto.
Qed.

(* The normalized automaton is a DFA if the original transitions are such that
the destination states are equivalent if so are the origin *)
Lemma normalize_dfa {A B} eq (g:nfa (list A) B) l :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  subset g l ->
  (forall q1 q2 a q3 q4, eq_sets q1 q3 ->
    In (trans q1 a q2) g -> In (trans q3 a q4) g ->
    eq_sets q2 q4
  ) ->
  dfa g -> dfa (normalize eq g l).
Proof.
  intros.
  induction H2.
  - apply cons_empty_dfa; auto.
  - simpl; apply cons_dfa_state, IHdfa; intros.
    intros q'; intros; apply H0; intuition.
    apply (H1 q1 q2 a q3 q4); intuition.
  - simpl; apply cons_dfa_symbol, IHdfa; intros.
    intros q'; intros; apply H0; intuition.
    apply (H1 q1 q2 a0 q3 q4); intuition.
  - simpl; apply cons_dfa_accept, IHdfa; intros.
    intros q'; intros; apply H0; intuition.
    apply (H1 q1 q2 a q3 q4); intuition.
  - simpl; apply cons_dfa_start_repeat.
    + apply IHdfa.
      intros q'; intuition.
      intros; apply (H1 q1 q2 a q3 q4); intuition.
    + apply normalize_in_start_states; auto.
  - simpl; apply cons_dfa_start.
    + apply IHdfa.
      intros q'; intuition.
      intros; apply (H1 q1 q2 a q3 q4); intuition.
    + apply normalize_start_states_nil; auto.
  - simpl; apply cons_dfa_trans_repeat.
    + apply IHdfa.
      intros q''; intuition.
      intros; apply (H1 q1 q2 a0 q3 q4); intuition.
    + apply normalize_trans_in; auto.
  - assert (dfa (normalize eq g l)). {
      apply IHdfa.
      intros q''; intuition.
      intros; apply (H1 q1 q2 a0 q3 q4); intuition.
    }
    clear IHdfa; pose proof H4;
    apply dfa_actual_nfa in H4; simpl.
    destruct (nfa_ex_trans_dec (normalize eq g l) H4 (normalize_state eq l q) a).
    2: apply cons_dfa_trans; auto.
    destruct H6 as [Q1 H6].
    apply in_normalize_eq_trans in H6.
    2: auto.
    destruct H6 as [q1 [q2 H6]].
    simpl; apply cons_dfa_trans_repeat.
    auto.
    specialize (H1 q1 q2 a q q').
    assert (eq_sets q2 q'). {
      apply H1.
      - apply eq_sets_transitive with (normalize_state eq l q).
        2: apply eq_sets_comm, get_set_eq; auto.
        intuition.
      - right; intuition.
      - left; auto.
    }
    clear H1.
    apply normalize_eq_trans_in with q1 q2.
    1,4,5: intuition.
    intros Q; intuition.
    apply eq_sets_transitive with (normalize_state eq l q).
    intuition.
    apply eq_sets_comm, get_set_eq; auto.
Qed.
















