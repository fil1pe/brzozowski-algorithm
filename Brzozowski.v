Require Export Reversing Determinization.

Section Brzozowski.

Context {State Symbol : Type}.
Hypothesis State_eq_dec : forall (x1 x2:State), { x1 = x2 } + { x1 <> x2 }.
Definition Det_state_eq_dec := Det_state_eq_dec State_eq_dec.
Hypothesis Symbol_eq_dec : forall (x1 x2:Symbol), { x1 = x2 } + { x1 <> x2 }.
Variable nfa : @NFA State Symbol.
Hypothesis nfa_is_dfa : is_dfa State_eq_dec Symbol_eq_dec nfa.
Hypothesis nfa_all_reachable : forall q, In q (states nfa) ->
  reachable_state State_eq_dec Symbol_eq_dec nfa q.

(* Minimizes reversed NFA *)
Definition mini_rev_dfa := det_nfa State_eq_dec Symbol_eq_dec (rev_nfa nfa).

(* Basic observation: <https://cs.stackexchange.com/questions/105574/proof-of-brzozowskis-algorithm-for-dfa-minimization#answer-105603> *)
Lemma basic_observation1 q Q w :
  In q (states nfa) -> In Q (states mini_rev_dfa) ->

  (has_state (ext_transitionf State_eq_dec Symbol_eq_dec nfa [q] (rev w)) Q ->
  exists Q', In Q' (ext_transitionf Det_state_eq_dec Symbol_eq_dec mini_rev_dfa [Q] w) /\ In q Q').
Proof.
  intros H H0 [q' [H1 H2]].
  apply (rev_ext_transitionf State_eq_dec Symbol_eq_dec nfa q' q (rev w)) in H1.
  rewrite rev_twice in H1.
  apply det_exists_ext_transitionf1 with (s:=[q']).
  1,3: intuition.
  intros q'' [H3|H3]; subst.
  intuition.
  contradiction.
Qed.

Lemma basic_observation2 q Q Q' w :
  In q (states nfa) -> In Q (states mini_rev_dfa) ->

  In Q' (ext_transitionf Det_state_eq_dec Symbol_eq_dec mini_rev_dfa [Q] w) ->
  In q Q' -> has_state (ext_transitionf State_eq_dec Symbol_eq_dec nfa [q] (rev w)) Q.
Proof.
  intros H H0 H1 H2.
  assert (H3: exists q', In q (ext_transitionf State_eq_dec Symbol_eq_dec (rev_nfa nfa) [q'] w) /\ In q' Q).
  eapply det_exists_ext_transitionf2.
  2: apply H2.
  1,2: intuition.
  destruct H3 as [q' [H3 H4]].
  exists q'; split.
  2: intuition.
  apply (rev_ext_transitionf State_eq_dec Symbol_eq_dec nfa q' q (rev w)).
  rewrite rev_twice; intuition.
Qed.

(* All resulting states are distinguishable *)
Theorem all_distinguishable q1 q2 :
  In q1 (states mini_rev_dfa) -> In q2 (states mini_rev_dfa) ->
  equiv_states Det_state_eq_dec Symbol_eq_dec mini_rev_dfa q1 q2 ->
  q1 = q2.
Proof.
  unfold equiv_states, has_accept_state, has_state, has_el; intros H H0 H1.
  apply (det_equiv_set_states State_eq_dec Symbol_eq_dec (rev_nfa nfa)).
  1,2: intuition.
  destruct nfa_is_dfa as [[[q0 H2] H3] H4].
  assert (forall w,
    (exists x, In x (ext_transitionf Det_state_eq_dec Symbol_eq_dec mini_rev_dfa [q1] w) /\ In q0 x) <->
    (exists x, In x (ext_transitionf Det_state_eq_dec Symbol_eq_dec mini_rev_dfa [q2] w) /\ In q0 x)
  ). {
    intro w; specialize (H1 w); split; intros [x H5]; assert (In x (accept_states mini_rev_dfa)).
    1,3: apply det_accept_state.
    apply (ext_transitionf_singleton_all_states Det_state_eq_dec Symbol_eq_dec mini_rev_dfa q1 w); intuition.
    2: apply (ext_transitionf_singleton_all_states Det_state_eq_dec Symbol_eq_dec mini_rev_dfa q2 w); intuition.
    1,2: exists q0; split; try rewrite rev_start_states; intuition.
    - destruct H1 as [[x' [H1 H7]] _].
      exists x; intuition.
      exists x'; split.
      intuition.
      apply det_accept_state in H7.
      2: apply (ext_transitionf_singleton_all_states Det_state_eq_dec Symbol_eq_dec mini_rev_dfa q2 w); intuition.
      destruct H7 as [q0' [H7 H8]].
      rewrite rev_start_states in H8; intuition.
      assert (q0 = q0').
      2: subst; intuition.
      destruct nfa_is_dfa as [[_ H5] _].
      apply H5; intuition.
    - destruct H1 as [_ [x' [H1 H7]]].
      exists x; intuition.
      exists x'; split.
      intuition.
      apply det_accept_state in H7.
      2: apply (ext_transitionf_singleton_all_states Det_state_eq_dec Symbol_eq_dec mini_rev_dfa q1 w); intuition.
      destruct H7 as [q0' [H7 H8]].
      rewrite rev_start_states in H8; intuition.
      assert (q0 = q0').
      2: subst; intuition.
      destruct nfa_is_dfa as [[_ H5] _].
      apply H5; intuition.
  }
  clear H1.
  assert (forall w,
    has_state (ext_transitionf State_eq_dec Symbol_eq_dec nfa [q0] w) q1 <->
    has_state (ext_transitionf State_eq_dec Symbol_eq_dec nfa [q0] w) q2
  ). {
    intro w; specialize (H5 (rev w)); split; intro H1; rewrite <- (rev_twice w) in H1.
    - apply (basic_observation1 q0 q1 (rev w) (start_state nfa q0 H2) H) in H1.
      apply H5 in H1.
      destruct H1 as [x [H1 H6]].
      apply (basic_observation2 q0 q2 x (rev w) (start_state nfa q0 H2) H0 H1) in H6.
      rewrite <- (rev_twice w).
      intuition.
    - apply (basic_observation1 q0 q2 (rev w) (start_state nfa q0 H2) H0) in H1.
      apply H5 in H1.
      destruct H1 as [x [H1 H6]].
      apply (basic_observation2 q0 q1 x (rev w) (start_state nfa q0 H2) H H1) in H6.
      rewrite <- (rev_twice w).
      intuition.
  }
  clear H5.
  unfold equiv_sets, subset; split; intros x H5; assert (In x (states nfa)).
  1,3: apply rev_states; intuition.
  apply (det_set_states State_eq_dec Symbol_eq_dec (rev_nfa nfa) x q1); intuition.
  apply (det_set_states State_eq_dec Symbol_eq_dec (rev_nfa nfa) x q2); intuition.
  1,2: apply nfa_all_reachable in H6; destruct H6 as [w H6]; specialize (H1 w);
  assert (In x (ext_transitionf State_eq_dec Symbol_eq_dec nfa [q0] w)).
  1,3: apply ext_transitionf_start_singleton; destruct nfa_is_dfa; intuition.
  - assert (H8: has_state (ext_transitionf State_eq_dec Symbol_eq_dec nfa [q0] w) q1).
    exists x; intuition.
    apply H1 in H8; destruct H8 as [x' [H8 H9]].
    assert (x' = x).
    apply (ext_transitionf_det State_eq_dec Symbol_eq_dec nfa q0 w); intuition.
    subst; intuition.
  - assert (H8: has_state (ext_transitionf State_eq_dec Symbol_eq_dec nfa [q0] w) q2).
    exists x; intuition.
    apply H1 in H8; destruct H8 as [x' [H8 H9]].
    assert (x' = x).
    apply (ext_transitionf_det State_eq_dec Symbol_eq_dec nfa q0 w); intuition.
    subst; intuition.
Qed.

(* The resulting NFA has the reversed language *)
Lemma mini_rev_language w :
  nfa_accepts State_eq_dec Symbol_eq_dec nfa w <-> nfa_accepts Det_state_eq_dec Symbol_eq_dec mini_rev_dfa (rev w).
Proof.
  pose proof (det_language State_eq_dec Symbol_eq_dec (rev_nfa nfa) (rev w)) as [H0 H1].
  pose proof (rev_language State_eq_dec Symbol_eq_dec nfa w) as [H2 H3].
  split; intros; intuition.
Qed.

End Brzozowski.