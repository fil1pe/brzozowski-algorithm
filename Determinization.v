Require Export Normalization Pumping.

Section Determinization.

Context {State Symbol : Type}.
Hypothesis State_eq_dec : forall (x1 x2:State), { x1 = x2 } + { x1 <> x2 }.
Hypothesis Symbol_eq_dec : forall (x1 x2:Symbol), { x1 = x2 } + { x1 <> x2 }.
Definition NFA := @NFA State Symbol.
Definition Det_state := @Det_state State.
Definition Det_state_eq_dec := Det_state_eq_dec State_eq_dec.
Definition alphabet_nodup := @alphabet_nodup State Symbol Symbol_eq_dec.

(* State powerset construction *)
Definition det_nfa' (g:NFA) :=
  start (start_states g)::
  flat_map (fun a =>
    map (fun s =>
      transition s a (transitionf State_eq_dec Symbol_eq_dec g s a)
    ) (powerset State (states_nodup State_eq_dec g))
  ) (alphabet_nodup g).

(* Normalization *)
Definition det_nfa'_normalized g :=
  normalize_nfa State_eq_dec (det_nfa' g) (det_nfa' g).

(* Inject accept states *)
Definition det_nfa'_with_accept_states g :=
  let g' := det_nfa'_normalized g in
  g' ++
  map (fun Q => accept Q) (
    filter (fun Q =>
      if (has_accept_state_dec State_eq_dec g Q) then true
      else false
    ) (states_nodup Det_state_eq_dec g')
  ).

(* Remove unreachable states *)
Definition det_nfa (g:NFA) :=
  remove_unreachable_states Det_state_eq_dec Symbol_eq_dec (det_nfa'_with_accept_states g).

(*
  If a state is in det_dfa', there is an equivalent set state such that
  there is a transition from it
*)
Lemma det_nfa'_transitions1 g Q a :
  In Q (states (det_nfa' g)) ->
  In a (alphabet g) ->
  exists Q', equiv_sets State Q Q' /\
  In (transition Q' a (transitionf State_eq_dec Symbol_eq_dec g Q' a)) (det_nfa' g).
Proof.
  intros H H10.
  assert (H0: In a (alphabet_nodup g)).
  apply nodup_In; auto.
  assert (exists Q', equiv_sets State Q Q' /\ In Q' (powerset State (states_nodup State_eq_dec g))).
  2: {
    destruct H1 as [Q' [H1 H2]]; clear H.
    exists Q'; split.
    intuition.
    clear H1.
    unfold det_nfa'; right.
    generalize dependent (alphabet_nodup g);
    generalize dependent (powerset State (states_nodup State_eq_dec g));
    intros s H alph H0.
    apply in_flat_map; exists a; split.
    intuition.
    clear H0.
    apply in_map_iff; exists Q'; intuition.
  }
  unfold det_nfa' in H; destruct H.
  - assert (subset State (start_states g) (states_nodup State_eq_dec g)).
    2: {
      apply powerset_complete in H1.
      destruct H1 as [Q' H1].
      symmetry in H; subst; exists Q'.
      1,2: intuition.
    }
    intros q H1.
    apply nodup_In, start_state.
    intuition.
  - apply powerset_complete.
    intuition.
    clear H0 H10;
    generalize dependent (alphabet_nodup g);
    intros alph H.
    induction alph as [|b alph IH].
    contradiction.
    simpl in H; apply in_states_app in H.
    destruct H.
    clear IH.
    apply in_states in H; repeat destruct H.
    6: intuition.
    1-5: apply in_map_iff in H; destruct H as [q [H H0]].
    1-3: discriminate.
    1,2: injection H; intros; subst.
    apply powerset_correct in H0; intuition.
    intros q H1.
    apply transitionf_singleton in H1.
    destruct H1 as [q' [_ H1]].
    apply transition_transitionf, transition_states_alphabet in H1.
    apply nodup_In; intuition.
Qed.

(*
  If a transition from Q1 to Q2 exists in det_nfa', then Q2 equals to
  the result of the original transition function applied to Q1
*)
Lemma det_nfa'_transitions2 g Q1 a Q2 :
  In (transition Q1 a Q2) (det_nfa' g) ->
  Q2 = transitionf State_eq_dec Symbol_eq_dec g Q1 a.
Proof.
  unfold det_nfa';
  generalize dependent (alphabet g);
  generalize dependent (powerset State (states g));
  intros s alph [H|H].
  discriminate.
  apply in_flat_map in H.
  destruct H as [a' [_ H]].
  apply in_map_iff in H.
  destruct H as [Q1' [H _]].
  injection H; intros; subst; intuition.
Qed.

(* All states in det_nfa'_with_accept_states are in det_nfa'_normalized *)
Lemma with_accept_states_states g q :
  In q (states (det_nfa'_with_accept_states g)) ->
  In q (states (det_nfa'_normalized g)).
Proof.
  unfold det_nfa'_with_accept_states, states_nodup; intro H.
  generalize dependent (fun Q =>
    if (has_accept_state_dec State_eq_dec g Q) then true
    else false
  ).
  generalize dependent (det_nfa'_normalized g).
  clear g.
  intros g f H.
  apply in_states_app in H.
  destruct H.
  intuition.
  remember (states g) as l eqn:H0.
  assert (H1: In q (@states Det_state Symbol (map (fun Q => accept Q) (filter f (nodup Det_state_eq_dec l))))).
  rewrite H0; auto.
  clear H H0; induction l as [|q0 l IH].
  contradiction.
  simpl in H1; destruct (in_dec Det_state_eq_dec q0 l).
  intuition.
  simpl in H1; destruct (f q0).
  destruct H1.
  subst.
  1-3: intuition.
Qed.

(* The start states in det_nfa'_with_accept_states are the same original ones *)
Lemma with_accept_states_start_states g :
  start_states (det_nfa'_with_accept_states g) = start_states (det_nfa'_normalized g).
Proof.
  unfold det_nfa'_with_accept_states.
  rewrite start_states_app.
  generalize dependent (filter (fun Q => if has_accept_state_dec State_eq_dec g Q then true else false) (states_nodup Det_state_eq_dec (det_nfa'_normalized g)));
  intro s.
  assert (forall A (s1 s2:ListSet A), s2 = nil -> s1 ++ s2 = s1).
  intros A s1 s2 H; rewrite H, app_nil_r; intuition.
  apply H; clear H.
  induction s as [|q s IH]; intuition.
Qed.

(* All transitions in det_nfa'_with_accept_states are in det_nfa'_normalized *)
Lemma with_accept_states_transitions g q1 a q2 :
  In (transition q1 a q2) (det_nfa'_with_accept_states g) <->
  In (transition q1 a q2) (det_nfa'_normalized g).
Proof.
  unfold det_nfa'_with_accept_states, states_nodup.
  generalize dependent (fun Q =>
    if (has_accept_state_dec State_eq_dec g Q) then true
    else false
  ).
  generalize dependent (det_nfa'_normalized g).
  clear g.
  intros g f; split; intro H.
  2: apply in_or_app; intuition.
  apply in_app_or in H.
  destruct H.
  intuition.
  remember (states g) as l eqn:H0.
  assert (H1: In (transition q1 a q2) (map (fun Q => accept Q) (filter f (nodup Det_state_eq_dec l)))).
  rewrite H0; auto.
  clear H H0; induction l as [|q0 l IH].
  contradiction.
  simpl in H1; destruct (in_dec Det_state_eq_dec q0 l).
  intuition.
  simpl in H1; destruct (f q0).
  destruct H1.
  discriminate.
  1,2: intuition.
Qed.

(* The resulting start state is the original set of start states *)
Lemma det_start_states g :
  exists Q, start_states (det_nfa g) = [Q] /\
  equiv_sets State (start_states g) Q.
Proof.
  assert (start_states (det_nfa' g) = [start_states g]). {
    unfold det_nfa';
    generalize dependent (alphabet_nodup g);
    generalize dependent (powerset State (states_nodup State_eq_dec g));
    intros s alph; simpl.
    assert (start_states (flat_map (fun a => map (fun s0 => transition s0 a (transitionf State_eq_dec Symbol_eq_dec g s0 a)) s) alph) = []).
    2: rewrite H; intuition.
    induction alph as [|a alph IH].
    intuition.
    simpl; rewrite start_states_app, IH, app_nil_r.
    clear IH.
    induction s as [|q s IH].
    1,2: intuition.
  }
  apply (normalize_start_states_singleton State_eq_dec (det_nfa' g) (det_nfa' g) (start_states g)) in H.
  assert (start_states (det_nfa'_normalized g) = [get_set State State_eq_dec (start_states g) (states (det_nfa' g))]).
  intuition.
  clear H.
  rewrite <- with_accept_states_start_states in H0.
  assert (start_states (det_nfa g) = start_states (det_nfa'_with_accept_states g)).
  apply remove_unreachable_states_start_states.
  rewrite <- H in H0; clear H.
  exists (get_set State State_eq_dec (start_states g) (states (det_nfa' g))); split.
  intuition.
  remember (get_set State State_eq_dec (start_states g) (states (det_nfa' g))) as Q.
  symmetry in HeqQ; apply get_set_equiv in HeqQ.
  intuition.
Qed.

(* All states are reachable *)
Lemma det_all_reachable g q :
  In q (states (det_nfa g)) ->
  reachable_state Det_state_eq_dec Symbol_eq_dec (det_nfa g) q.
Proof.
  apply remove_unreachable_correct.
Qed.

(* All resulting states are subsets of the original set of states *)
Lemma det_set_states g q Q :
  In Q (states (det_nfa g)) -> In q Q ->
  In q (states g).
Proof.
  intros H H0.
  apply remove_unreachable_states_states in H.
  apply with_accept_states_states in H.
  unfold det_nfa'_normalized in H.
  apply normalize_states in H.
  destruct H as [Q' [H H1]].
  symmetry in H.
  apply get_set_equiv in H.
  apply H in H0.
  clear H.
  unfold det_nfa' in H1.
  destruct H1.
  symmetry in H; subst; revert H0; apply start_state.
  assert (
    In Q' (powerset State (states_nodup State_eq_dec g)) \/
    exists Q a, Q' = transitionf State_eq_dec Symbol_eq_dec g Q a
  ).
  2: {
    clear H.
    destruct H1.
    - assert (H1: In q (states_nodup State_eq_dec g)).
      2: apply nodup_In in H1; auto.
      generalize dependent Q';
      induction (states_nodup State_eq_dec g) as [|q0 s IH];
      intros Q' H H0.
      destruct H0; try symmetry in H0; subst; contradiction.
      simpl in H0; apply in_app_or in H0; destruct H0.
      apply in_map_iff in H0; destruct H0 as [s' [H0 H1]]; symmetry in H0;
      subst; destruct H.
      subst.
      2,3: right; apply IH in H.
      1-5: intuition.
    - destruct H as [Q'' [a H]]; subst.
      apply (transitionf_all_states State_eq_dec Symbol_eq_dec g Q'' a q);
      intuition.
  }
  clear H0 Q q.
  generalize dependent (alphabet_nodup g).
  generalize dependent (powerset State (states_nodup State_eq_dec g)).
  intros s alph H.
  induction alph as [|a alph IH].
  contradiction.
  simpl in H.
  apply in_states_app in H.
  destruct H.
  2: intuition.
  clear IH.
  induction s as [|Q0 s IH].
  contradiction.
  destruct H as [H|[H|H]]; subst.
  2: right; exists Q0, a.
  1-3: intuition.
Qed.

(* All equivalent states are equal, thanks to normalization *)
Lemma det_equiv_set_states g q1 q2 :
  In q1 (states (det_nfa g)) ->
  In q2 (states (det_nfa g)) ->
  equiv_sets State q1 q2 -> q1 = q2.
Proof.
  intros H H0 H1.
  apply remove_unreachable_states_states, with_accept_states_states in H, H0.
  unfold det_nfa'_normalized in H, H0.
  pose proof (normalize_equiv_set_states State_eq_dec (det_nfa' g) (det_nfa' g) q1 q2) as H2.
  apply H2.
  intros q H3.
  1-4: intuition.
Qed.

(* The resulting accept states are the ones that have original accept states *)
Lemma det_accept_state g Q :
  In Q (states (det_nfa g)) ->
  In Q (accept_states (det_nfa g)) <-> has_state Q (accept_states g).
Proof.
  intro H; split; intro H0.
  - clear H.
    apply remove_unreachable_states_accept_states in H0.
    unfold det_nfa'_with_accept_states in H0.
    apply in_accept_states_app in H0.
    destruct H0.
    + apply normalize_accept_states in H.
      destruct H as [q' [H H0]].
      apply in_accept_states in H0.
      assert (False). {
        clear H.
        unfold det_nfa' in H0; destruct H0.
        discriminate.
        generalize dependent (powerset State (states_nodup State_eq_dec g));
        generalize dependent (alphabet_nodup g);
        intros alph s H.
        induction alph as [|a alph IH].
        intuition.
        simpl in H.
        apply in_app_or in H; destruct H.
        2: intuition.
        clear IH;
        induction s as [|q s IH].
        2: destruct H.
        1,3: intuition.
        discriminate.
      }
      contradiction.
    + generalize dependent (states_nodup Det_state_eq_dec (det_nfa'_normalized g));
      intros s H.
      apply in_accept_states in H.
      apply in_map_iff in H.
      destruct H as [Q' [H H0]].
      injection H; intros; subst.
      apply filter_In in H0; destruct H0 as [H0 H1].
      destruct (has_accept_state_dec State_eq_dec g Q) as [H2|H2].
      intuition.
      discriminate.
  - apply remove_unreachable_states_has_accept_state.
    apply H.
    destruct H0 as [qf [H0 H1]].
    apply remove_unreachable_states_states in H.
    unfold det_nfa'_with_accept_states in H; unfold det_nfa'_with_accept_states.
    apply in_accept_states_app.
    apply in_states_app in H.
    right.
    destruct H.
    + apply in_accept_states.
      apply in_map_iff; exists Q; split.
      2: apply filter_In; split.
      2: apply nodup_In.
      1-2: intuition.
      destruct (has_accept_state_dec State_eq_dec g Q) as [H2|H2].
      intuition.
      assert (False).
      apply H2; exists qf.
      1,2: intuition.
    + generalize dependent (states_nodup Det_state_eq_dec (det_nfa'_normalized g)).
      intros s H.
      apply in_states in H; repeat destruct H.
      1,2,4,5: apply in_map_iff in H; destruct H as [q [H _]]; discriminate.
      apply in_map_iff in H.
      destruct H as [Q' [H H2]].
      injection H; intros; subst; clear H.
      apply filter_In in H2; destruct H2 as [H H2].
      apply in_accept_states.
      apply in_map_iff; exists Q; split.
      2: apply filter_In; split.
      1-3: intuition.
Qed.

(* Used in basic_observation1 *)
Lemma det_exists_ext_transitionf1 g s q Q w :
  In Q (states (det_nfa g)) ->
  subset State s Q ->
  In q (ext_transitionf State_eq_dec Symbol_eq_dec g s w) ->
  exists Q', In Q' (ext_transitionf Det_state_eq_dec Symbol_eq_dec (det_nfa g) [Q] w) /\ In q Q'.
Proof.
  intros H H0 H1.
  apply ext_transitionf_singleton in H1.
  destruct H1 as [q' [H1 H2]].
  apply path_ext_transitionf in H2.
  assert (exists Q', path (det_nfa g) Q Q' w /\ In q Q').
  2: {
    destruct H3 as [Q' H3]; exists Q'; split.
    apply path_ext_transitionf.
    1,2: intuition.
  }
  apply H0 in H1; clear H0.
  generalize dependent Q.
  induction H2; intros Q H0 H1.
  exists Q; split; try constructor; intuition.
  assert (exists Q', In (transition Q a Q') (det_nfa g) /\ In q2 Q'). {
    clear IHpath H2.
    assert (exists Q1 Q2, equiv_sets State Q Q1 /\ In (transition Q1 a Q2) (det_nfa' g) /\ In q2 Q2). {
      apply remove_unreachable_states_states, with_accept_states_states, normalize_states in H0.
      destruct H0 as [Q1 [H0 H2]].
      symmetry in H0; apply get_set_equiv in H0.
      apply H0 in H1.
      apply (det_nfa'_transitions1 g Q1 a) in H2.
      destruct H2 as [Q1' [H2 H3]].
      exists Q1', (transitionf State_eq_dec Symbol_eq_dec g Q1' a); split.
      2: split.
      apply equiv_sets_trans with Q1.
      apply equiv_sets_comm.
      1-3: intuition.
      apply (transition_transitionf State_eq_dec Symbol_eq_dec g q1 a q2) in H.
      apply transitionf_generalize with q1.
      apply H2.
      1,2: intuition.
      apply transition_states_alphabet in H; intuition.
    }
    destruct H2 as [Q1 [Q2 [H2 [H3 H4]]]].
    apply (normalize_states_transitions2 State_eq_dec (det_nfa' g) (det_nfa' g) Q1 a Q2) in H3.
    apply with_accept_states_transitions in H3.
    assert (Q = (get_set State State_eq_dec Q1 (states (det_nfa' g)))).
    2: {
      subst; exists (get_set State State_eq_dec Q2 (states (det_nfa' g))); split.
      2: remember (get_set State State_eq_dec Q2 (states (det_nfa' g))) as Q2';
      symmetry in HeqQ2'; apply get_set_equiv in HeqQ2'; apply HeqQ2'; intuition.
      apply remove_unreachable_states_transitions2; intuition.
    }
    apply (normalize_equiv_set_states State_eq_dec (det_nfa' g) (det_nfa' g) Q (get_set State State_eq_dec Q1 (states (det_nfa' g)))).
    apply subset_self.
    apply remove_unreachable_states_states, with_accept_states_states in H0; intuition.
    apply transition_states_alphabet in H3; destruct H3 as [H3 _].
    apply with_accept_states_states in H3; intuition.
    apply equiv_sets_trans with Q1.
    intuition.
    remember (get_set State State_eq_dec Q1 (states (det_nfa' g))) as Q1';
    symmetry in HeqQ1'; apply get_set_equiv in HeqQ1'; intuition.
  }
  destruct H3 as [Q' [H3 H4]].
  apply IHpath in H4.
  2: apply in_states.
  2: intuition.
  2: right; right; right; right; exists a, Q; intuition.
  destruct H4 as [Q'' [H4 H5]].
  exists Q''; split.
  apply path_trans with Q'.
  1-3: intuition.
Qed.

(* Used in basic_observation2 *)
Lemma det_exists_ext_transitionf2 g q Q Q' w :
  In Q (states (det_nfa g)) ->
  In q Q' ->
  In Q' (ext_transitionf Det_state_eq_dec Symbol_eq_dec (det_nfa g) [Q] w) ->
  exists q', In q (ext_transitionf State_eq_dec Symbol_eq_dec g [q'] w) /\ In q' Q.
Proof.
  intros H H0 H1.
  apply path_ext_transitionf in H1.
  assert (exists q', path g q' q w /\ In q' Q).
  2: destruct H2 as [q' [H2 H3]]; exists q'; split;
  try apply path_ext_transitionf; intuition.
  induction H1.
  exists q; split; try constructor; intuition.
  apply IHpath in H0; clear IHpath.
  2: apply (transition_transitionf Det_state_eq_dec Symbol_eq_dec (det_nfa g) q1 a q2) in H1;
  apply transitionf_all_states in H1; intuition.
  destruct H0 as [q'' [H0 H3]].
  assert (exists q', In (transition q' a q'') g /\ In q' q1).
  2: {
    destruct H4 as [q' [H4 H5]].
    exists q'; split.
    apply path_trans with q''.
    1-3: intuition.
  }
  clear H2 H0.
  apply remove_unreachable_states_transitions1, with_accept_states_transitions, normalize_states_transitions1 in H1.
  destruct H1 as [q1' [q2' [H1 [H2 [H4 _]]]]].
  apply H2 in H3.
  apply det_nfa'_transitions2 in H4; subst.
  apply transitionf_singleton in H3; destruct H3 as [q' [H3 H4]].
  exists q'; split.
  2: apply H1.
  apply (transition_transitionf State_eq_dec Symbol_eq_dec g q' a q'').
  1,2: intuition.
Qed.

(* The resulting NFA has the same language *)
Lemma det_language g : forall w,
  nfa_accepts State_eq_dec Symbol_eq_dec g w <-> nfa_accepts Det_state_eq_dec Symbol_eq_dec (det_nfa g) w.
Proof.
  unfold nfa_accepts, NFA.nfa_accepts, has_accept_state, has_state.
  intro w; split; intro H.
  - destruct H as [q [H H0]].
    pose proof (det_start_states g).
    destruct H1 as [Q0 [H1 H2]].
    assert (H3: In Q0 (states (det_nfa g))).
    apply start_state; rewrite H1; intuition.
    pose proof H3 as H10.
    apply (det_exists_ext_transitionf1 g (start_states g) q Q0 w) in H3.
    2: apply H2.
    2: intuition.
    destruct H3 as [Q' [H3 H4]].
    exists Q'; split.
    rewrite H1; intuition.
    apply ext_transitionf_singleton_all_states in H3.
    apply det_accept_state.
    1,3: intuition.
    exists q; intuition.
  - destruct H as [Q [H H0]].
    apply ext_transitionf_singleton in H; destruct H as [Q0 [H H1]].
    pose proof H as H10.
    apply start_state in H.
    apply det_accept_state in H0.
    destruct H0 as [q [H0 H2]].
    apply (det_exists_ext_transitionf2 g q Q0 Q w) in H.
    2,3: intuition.
    2: apply ext_transitionf_singleton_all_states in H1; try apply H1; apply start_state; intuition.
    destruct H as [q0 [H H3]].
    exists q; split.
    apply (ext_transitionf_generalize State_eq_dec Symbol_eq_dec g (start_states g) q0 q w) in H.
    1,3: intuition.
    pose proof (det_start_states g).
    destruct H4 as [Q0' [H4 H5]].
    rewrite H4 in H10.
    apply in_singleton in H10; subst.
    apply H5; intuition.
Qed.

(* The resulting NFA is a DFA *)
Lemma det_is_dfa g : is_dfa Det_state_eq_dec Symbol_eq_dec (det_nfa g).
Proof.
  split.
  - pose proof (det_start_states g); destruct H as [Q [H H0]];
    unfold start_singleton; split.
    exists Q; rewrite H; intuition.
    intros Q1 Q2 H1 H2; rewrite H in H1, H2;
    apply in_singleton in H1, H2; subst; intuition.
  - unfold transitionf_det; intros Q1 a Q2 Q3 H H0.
    apply transition_transitionf, remove_unreachable_states_transitions1, with_accept_states_transitions in H, H0.
    pose proof H; pose proof H0.
    apply normalize_states_transitions1 in H1, H2.
    destruct H1 as [Q1' [Q2' [H1 [H3 [H4 [H5 H6]]]]]].
    destruct H2 as [Q1'' [Q3' [H7 [H8 [H9 [H10 H11]]]]]].
    apply det_nfa'_transitions2 in H4, H9.
    apply (normalize_equiv_set_states State_eq_dec (det_nfa' g) (det_nfa' g) Q2 Q3).
    apply subset_self.
    apply transition_states_alphabet in H; intuition.
    apply transition_states_alphabet in H0; intuition.
    assert (equiv_sets State Q2' Q3').
    2: {
      apply equiv_sets_trans with Q2'.
      2: apply equiv_sets_trans with Q3'.
      2: intuition.
      apply equiv_sets_comm; symmetry in H6; apply get_set_equiv in H6; intuition.
      symmetry in H11; apply get_set_equiv in H11; intuition.
    }
    rewrite H4, H9.
    apply transitionf_equiv.
    apply equiv_sets_trans with Q1.
    apply equiv_sets_comm.
    1,2: intuition.
Qed.

End Determinization.