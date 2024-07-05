Require Export DFA.

Section Normalization.

Context {State Symbol : Type}.
Hypothesis State_eq_dec : forall (x1 x2:State), { x1 = x2 } + { x1 <> x2 }.
Hypothesis Symbol_eq_dec : forall (x1 x2:Symbol), { x1 = x2 } + { x1 <> x2 }.
Definition NFA := @NFA State Symbol.

Definition Det_state := ListSet State.

Lemma Det_state_eq_dec : forall (x1 x2:Det_state), { x1 = x2 } + { x1 <> x2 }.
Proof.
  apply list_eq_dec, State_eq_dec.
Defined.

(* Normalize the set states of a NFA *)
Fixpoint normalize_nfa (g cp:@NFA.NFA Det_state Symbol) :=
  let normalize_state := fun q => get_set State State_eq_dec q (states cp) in

  match g with
  | state q::g => state (normalize_state q)::normalize_nfa g cp
  | start q::g => start (normalize_state q)::normalize_nfa g cp
  | accept q::g => accept (normalize_state q)::normalize_nfa g cp
  | transition q1 a q2::g => transition (normalize_state q1) a (normalize_state q2)::normalize_nfa g cp
  | x::g => x::normalize_nfa g cp
  | nil => nil
  end.

(* The resulting states *)
Lemma normalize_states g cp q :
  In q (states (normalize_nfa g cp)) ->
  exists q', q = get_set State State_eq_dec q' (states cp) /\
  In q' (states g).
Proof.
  intro H.
  induction g as [|c g IH].
  contradiction.
  assert (forall A (x:A) l, x::l = [x] ++ l).
  simpl; intuition.
  simpl in H; destruct c.
  2: intuition.
  - rewrite H0 in H; apply in_states_app in H.
    destruct H.
    2: apply IH in H; destruct H as [q' H]; exists q'; split; try right; intuition.
    destruct H.
    2: contradiction.
    symmetry in H; exists q0; split; try left; intuition.
  (* same code from above: *)
  - rewrite H0 in H; apply in_states_app in H.
    destruct H.
    2: apply IH in H; destruct H as [q' H]; exists q'; split; try right; intuition.
    destruct H.
    2: contradiction.
    symmetry in H; exists q0; split; try left; intuition.
  (* same code from above: *)
  - rewrite H0 in H; apply in_states_app in H.
    destruct H.
    2: apply IH in H; destruct H as [q' H]; exists q'; split; try right; intuition.
    destruct H.
    2: contradiction.
    symmetry in H; exists q0; split; try left; intuition.
  - rewrite H0 in H; apply in_states_app in H.
    destruct H.
    2: apply IH in H; destruct H as [q' H]; exists q'; split; try right; intuition.
    destruct H.
    symmetry in H; exists q1; split; try left; intuition.
    destruct H.
    2: contradiction.
    symmetry in H; exists q2; split; try (right; left); intuition.
Qed.

(* The resulting start state *)
Lemma normalize_start_states_singleton g cp Q :
  let normalize_state := fun q => get_set State State_eq_dec q (states cp) in
  
  start_states g = [Q] -> start_states (normalize_nfa g cp) = [normalize_state Q].
Proof.
  intros f H.
  assert (start_states (normalize_nfa g cp) = map f (start_states g)).
  2: rewrite H in H0; intuition.
  clear H.
  induction g as [|c g IH].
  intuition.
  destruct c.
  1,2,4,5: intuition.
  simpl; rewrite IH; intuition.
Qed.

(* The resulting accept states *)
Lemma normalize_accept_states g cp q :
  In q (accept_states (normalize_nfa g cp)) ->
  exists q', q = get_set State State_eq_dec q' (states cp) /\
  In q' (accept_states g).
Proof.
  intro H.
  induction g as [|c g IH].
  contradiction.
  simpl in H; destruct c.
  1-3,5: intuition.
  assert (forall A (x:A) l, x::l = [x] ++ l).
  simpl; intuition.
  rewrite H0 in H.
  apply in_accept_states_app in H.
  destruct H.
  2: apply IH in H; destruct H as [q' H]; exists q'; split; try right; intuition.
  destruct H.
  2: contradiction.
  exists q0; split.
  symmetry; intuition.
  left; intuition.
Qed.

(* The resulting transitions *)
Lemma normalize_states_transitions1 g cp q1 a q2 :
  In (transition q1 a q2) (normalize_nfa g cp) ->
  exists q1' q2', equiv_sets State q1 q1' /\ equiv_sets State q2 q2' /\
  In (transition q1' a q2') g /\ q1 = get_set State State_eq_dec q1' (states cp) /\
  q2 = get_set State State_eq_dec q2' (states cp).
Proof.
  intro H.
  induction g as [|c g IH].
  contradiction.
  simpl in H; destruct c.
  1-4: simpl in H; destruct H; try discriminate; apply IH in H;
  destruct H as [q1' [q2' [H0 [H1 [H2 [H3 H4]]]]]];
  exists q1', q2'; repeat split; try right; intuition; try apply H0; try apply H1.
  destruct H.
  2: apply IH in H; destruct H as [q1' [q2' [H0 [H1 [H2 [H3 H4]]]]]];
  exists q1', q2'; repeat split; try right; intuition; try apply H0; try apply H1.
  injection H; intros; subst; exists q0, q3; split.
  2: split.
  3: split.
  3,4: intuition.
  remember (get_set State State_eq_dec q0 (states cp)) eqn:H0.
  2: remember (get_set State State_eq_dec q3 (states cp)) eqn:H0.
  1,2: symmetry in H0; apply get_set_equiv in H0; apply equiv_sets_comm;
  intuition.
Qed.

Lemma normalize_states_transitions2 g cp q1 a q2 :
  let normalize_state := fun q => get_set State State_eq_dec q (states cp) in

  In (transition q1 a q2) g ->
  In (transition (normalize_state q1) a (normalize_state q2)) (normalize_nfa g cp).
Proof.
  intros f H.
  induction g as [|c g IH].
  contradiction.
  simpl in H; destruct c.
  1-4: destruct H; try discriminate; right; intuition.
  destruct H.
  injection H; intros; subst; left; intuition.
  right; intuition.
Qed.

(* The resulting equivalent set states are equal *)
Lemma normalize_equiv_set_states g cp q1 q2 :
  (subset (ListSet State) (states g) (states cp)) ->
  In q1 (states (normalize_nfa g cp)) ->
  In q2 (states (normalize_nfa g cp)) ->
  equiv_sets State q1 q2 -> q1 = q2.
Proof.
  intros H H0 H1 H2.
  apply normalize_states in H0, H1.
  destruct H0 as [q1' [H0 H3]]; destruct H1 as [q2' [H1 H4]].
  apply H in H3, H4; clear H.
  remember (states cp) as s eqn:H5.
  assert (q1 = get_set State State_eq_dec q1' s).
  rewrite H5; intuition.
  clear H0.
  assert (q2 = get_set State State_eq_dec q2' s).
  rewrite H5; intuition.
  clear H1 H5 cp.
  induction s as [|q s IH].
  contradiction.
  destruct H3, H4; subst.
  intuition.
  1,2: apply get_equiv_sets; intuition.
  simpl; simpl in H2, IH.
  destruct (equiv_sets_dec State State_eq_dec q q1') as [H4|H4];
  destruct (equiv_sets_dec State State_eq_dec q q2') as [H5|H5].
  1,4: intuition.
  - remember (get_set State State_eq_dec q2' s) as q' eqn:H6; symmetry in H6; apply get_set_equiv in H6.
    assert (False).
    2: intuition.
    apply H5.
    apply equiv_sets_trans with q'.
    2: apply equiv_sets_comm.
    1,2: intuition.
  - remember (get_set State State_eq_dec q1' s) as q' eqn:H6; symmetry in H6; apply get_set_equiv in H6.
    assert (False).
    2: intuition.
    apply H4.
    apply equiv_sets_trans with q'.
    1,2: apply equiv_sets_comm; intuition.
Qed.

End Normalization.