Require Import List Bool sets nfa dfa reversing determinizing.
Include ListNotations.


(** Brzozowski's algorithm: det (rev g) **)

(* All states are reachable *)
Theorem brzozowski_reach A B eqA eqB H (g:nfa A B) Q :
  (forall a b, a=b <-> eqB a b=true) ->
  let brz := (det eqA eqB H (rev g)) in
  In Q (states brz) ->
  reachable_state (lists_eq eqA) eqB brz Q.
Proof.
  intros.
  pose proof (det_reach eqA eqB H (rev g) Q H0 H1); destruct H2 as [w H2];
  exists w;
  destruct (det eqA eqB H (rev g)) eqn:H3.
  destruct H1.
  replace brz with (det eqA eqB H (rev g)).
  rewrite det_start_states.
  apply path_ext_transition.
  apply lists_eq_correct.
  1,2: auto.
  rewrite H3; auto.
  rewrite H3; discriminate.
Qed.

(* A accept state is a set that has the original start state *)
Lemma brzozowski_accept {A B eqA eqB} H {g:nfa A B} {q0 Q} :
  dfa g -> In q0 (start_states g) ->
  let brz := (det eqA eqB H (rev g)) in
  (in_opt Q (Some (states brz)) \/ Q = None) ->
  in_opt Q (Some (accept_states brz)) <-> in_opt (Some q0) Q.
Proof.
  intro H10; intros.
  destruct H1.
  2: split; intros; subst; auto.
  destruct Q.
  2: destruct H1.
  pose proof H0.
  apply revert_start in H2.
  simpl; simpl in H1.
  split; intros.
  - apply (det_accept H H1) in H3; destruct H3 as [_q0 [H3 H4]].
    assert (_q0 = q0).
    2: subst; auto.
    apply revert_accept in H4; replace (rev (rev g)) with g in H4.
    2: apply rev_twice.
    apply dfa_start with g; auto.
  - apply (det_accept H H1); exists q0; auto.
Qed.

(* Basic observation *)
Lemma basic_observation {A B eqA eqB} H10 {g:nfa A B} {q' Q w} :
  (forall a b, a=b <-> eqB a b=true) ->
  dfa g ->
  let brz := (det eqA eqB H10 (rev g)) in
  In Q (states brz) ->
  in_opt (Some q') (dfa_transition (lists_eq eqA) eqB brz (Some Q) w) <->
  in_opt (dfa_transition eqA eqB g (Some q') (w^R)) (Some Q).
Proof.
  intros H11 H brz H12; intros; split; intros.
  - simpl in H0; destruct (ext_transition (lists_eq eqA) eqB brz [Q] w) as [|Q' L] eqn:H1.
    destruct H0.
    assert (In Q' (ext_transition (lists_eq eqA) eqB brz [Q] w)).
      rewrite H1; left; auto.
    apply path_ext_transition in H2.
    2: apply lists_eq_correct.
    2,3: auto.
    assert (path brz Q Q' w /\ In q' Q').
        split; auto.
    apply (det_path_reach H10 H11) in H3; destruct H3 as [q [H3 H4]].
    apply reverted_path in H3; replace (rev (rev g)) with g in H3.
    2: apply rev_twice.
    simpl; destruct (ext_transition eqA eqB g [q'] (w^R)) as [|_q l] eqn:H5.
    + assert (In q []).
        rewrite <- H5; apply path_ext_transition; auto.
      destruct H6.
    + simpl.
      assert (In _q (ext_transition eqA eqB g [q'] (w^R))).
        rewrite H5; left; auto.
      assert (In q (ext_transition eqA eqB g [q'] (w^R))).
        apply path_ext_transition; auto.
      assert (_q = q).
        clear H5 l; remember (ext_transition eqA eqB g [q'] (w^R)) as l;
        apply (@dfa_trans_ext A B eqA eqB g q' q _q (w^R) l); auto.
      subst; auto.
  - simpl in H0; destruct (ext_transition eqA eqB g [q'] (w^R)) as [|q l] eqn:H1; simpl in H0.
    destruct H0.
    assert (path g q' q (w^R)).
      apply path_ext_transition with eqA eqB; try rewrite H1; intuition.
    apply reverted_path in H2; rewrite <- revert_word_twice in H2.
    assert (H3: exists Q', path brz Q Q' w /\ In q' Q').
      pose proof (@det_path_reach A B eqA eqB H10 (rev g) Q q' w H11) as H3;
      destruct H3 as [_ H3]; apply H3 with q; auto.
    destruct H3 as [Q' [H3 H4]].
    apply (path_ext_transition (lists_eq eqA) eqB brz Q Q' w (lists_eq_correct H10) H11) in H3.
    simpl; destruct (ext_transition (lists_eq eqA) eqB brz [Q] w) as [|_Q' L] eqn:H5.
    destruct H3.
    assert (_Q' = Q').
    2: subst; auto.
    apply (@dfa_trans_ext (list A) B (lists_eq eqA) eqB brz Q Q' _Q' w (_Q' :: L)).
    apply lists_eq_correct; auto.
    1,3-5: intuition.
    apply det_dfa; auto.
Qed.

(* All states are distinguishable *)
Theorem brzozowski_disting {A B} eqA eqB H (g:nfa A B) Q1 Q2 :
  (forall a b, a=b <-> eqB a b=true) ->
  (forall q, In q (states g) -> reachable_state eqA eqB g q) ->
  dfa g ->
  let brz := (det eqA eqB H (rev g)) in
  In Q1 (states brz) -> In Q2 (states brz) ->
  dfa_indisting_states (lists_eq eqA) eqB brz Q1 Q2 ->
  Q1 = Q2.
Proof.
  intros H11 H12 H10.
  intros.
  unfold dfa_indisting_states in H2.
  destruct (start_states g) eqn:H4.
  - apply rev_start_nil, (det_nil eqA eqB H) in H4.
    assert (brz = []).
      auto.
    rewrite H3 in H0.
    destruct H0.
  - assert (H3: exists q0, In q0 (start_states g)).
      exists a; rewrite H4; intuition.
    destruct H3 as [q0 H3]; clear H4.
    assert (forall w, in_opt (Some q0) (dfa_transition (lists_eq eqA) eqB brz (Some Q1) w) <->
    in_opt (Some q0) (dfa_transition (lists_eq eqA) eqB brz (Some Q2) w)). {
      intros.
      specialize (H2 w).
      replace brz with (det eqA eqB H (rev g)) in H2.
      2: auto.
      rewrite (brzozowski_accept H H10 H3), (brzozowski_accept H H10 H3) in H2.
      intuition.
      - simpl; destruct (ext_transition (lists_eq eqA) eqB
          (det eqA eqB H (rev g)) [Q2] w) eqn:H4.
        right; auto.
        left; simpl.
        apply (ext_transition_in_states (lists_eq eqA) eqB (det eqA eqB H (rev g) : nfa (list A) B) [Q2] l0 w).
        2: rewrite H4; intuition.
        intros; destruct H5.
        2: destruct H5.
        subst; auto.
      - simpl; destruct (ext_transition (lists_eq eqA) eqB
          (det eqA eqB H (rev g)) [Q1] w) eqn:H4.
        right; auto.
        left; simpl.
        apply (ext_transition_in_states (lists_eq eqA) eqB (det eqA eqB H (rev g) : nfa (list A) B) [Q1] l0 w).
        2: rewrite H4; intuition.
        intros; destruct H5.
        2: destruct H5.
        subst; auto.
    }
    clear H2.
    assert (H5: forall w, in_opt (dfa_transition eqA eqB g (Some q0) (w^R)) (Some Q1) <->
    in_opt (dfa_transition eqA eqB g (Some q0) (w^R)) (Some Q2)). {
      intros.
      specialize (H4 w).
      replace brz with (det eqA eqB H (rev g)) in H4.
      2: auto.
      rewrite (basic_observation H H11 H10), (basic_observation H H11 H10) in H4;
      intuition.
    }
    clear H4.
    assert (forall w, in_opt (dfa_transition eqA eqB g (Some q0) w) (Some Q1) <->
    in_opt (dfa_transition eqA eqB g (Some q0) w) (Some Q2)). {
      intros.
      specialize (H5 (w^R)).
      replace w with ((w^R)^R).
      2: symmetry; apply revert_word_twice.
      auto.
    }
    clear H5.
    assert (forall q, in_opt q (Some Q1) <-> in_opt q (Some Q2)). {
      destruct q as [q|].
      2: intuition.
      replace brz with (det eqA eqB H (rev g)) in H0, H1.
      2: auto.
      simpl; split; intros.
      - apply (det_states H Q1) with q in H0.
        2: auto.
        pose proof (revert_states_are_states g q) as H5; destruct H5 as [H5 _];
        apply H5 in H0; clear H5.
        apply H12 in H0; destruct H0 as [w H0].
        apply ext_transition_list in H0.
        destruct H0 as [q0' [H5 H6]].
        assert (q0' = q0).
          apply dfa_start with g; auto.
        subst.
        specialize (H2 w); simpl in H2;
        destruct (ext_transition eqA eqB g [q0] w) eqn:H7.
        destruct H6.
        2: auto.
        assert (q = a0). {
          assert (In a0 (a0::l0)).
            left; auto.
          apply dfa_trans_ext with eqA eqB g q0 w (a0::l0); auto.
        }
        subst; intuition.
      - apply (det_states H Q2) with q in H1.
        2: auto.
        pose proof (revert_states_are_states g q) as H5; destruct H5 as [H5 _];
        apply H5 in H1; clear H5.
        apply H12 in H1; destruct H1 as [w H1].
        apply ext_transition_list in H1.
        destruct H1 as [q0' [H5 H6]].
        assert (q0' = q0).
          apply dfa_start with g; auto.
        subst.
        specialize (H2 w); simpl in H2;
        destruct (ext_transition eqA eqB g [q0] w) eqn:H7.
        destruct H6.
        2: auto.
        assert (q = a0). {
          assert (In a0 (a0::l0)).
            left; auto.
          apply dfa_trans_ext with eqA eqB g q0 w (a0::l0); auto.
        }
        subst; intuition.
    }
    assert (eq_sets Q1 Q2). {
      unfold eq_sets; intros q.
      specialize (H4 (Some q)).
      intuition.
    }
    apply (det_eq_states eqA eqB H (rev g)) in H5; auto.
Qed.

(* The language is reverse *)
Theorem brzozowski_language {A B} eqA eqB H (g:nfa A B) w :
  (forall a b, a=b <-> eqB a b=true) ->
  (forall q, In q (states g) -> reachable_state eqA eqB g q) ->
  let brz := (det eqA eqB H (rev g)) in
  lang (lists_eq eqA) eqB brz w <-> lang eqA eqB g (w^R).
Proof.
  intros.
  assert (equivalent_nfas eqA eqB (lists_eq eqA) (rev g) brz).
    intros; apply det_language; auto.
  split; intros.
  - destruct H2 with (w^R);
    apply reverted_nfa_lang.
    1,2: auto.
    apply H2; rewrite <- revert_word_twice; auto.
  - destruct H2 with (w^R);
    apply H2; apply reverted_nfa_lang.
    1,2: auto.
    rewrite <- rev_twice; auto.
Qed.













