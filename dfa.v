Require Import List Bool utils nfa.
Include ListNotations.


(* Inductive construction of DFA, which has at most one start state and
deterministic transitions *)
Inductive dfa {A B} : nfa A B -> Prop :=
  | cons_empty_dfa : actual_nfa (@nil (@nfa_comp A B)) -> dfa (@nil (@nfa_comp A B))
  | cons_dfa_state (g:nfa A B) q : dfa g -> dfa (state q::g)
  | cons_dfa_symbol (g:nfa A B) a : dfa g -> dfa (symbol a::g)
  | cons_dfa_accept (g:nfa A B) q : dfa g -> dfa (accept q::g)
  | cons_dfa_start_repeat (g:nfa A B) q : dfa g -> In q (start_states g) -> dfa (start q::g)
  | cons_dfa_start (g:nfa A B) q : dfa g -> start_states g = [] -> dfa (start q::g)
  | cons_dfa_trans_repeat (g:nfa A B) q a q' : dfa g -> In (trans q a q') g -> dfa (trans q a q'::g)
  | cons_dfa_trans (g:nfa A B) q a q' : dfa g -> (forall q', ~ In (trans q a q') g) -> dfa (trans q a q'::g).


(* Extended transition for DFA *)
Definition dfa_transition {A B} eqA eqB (g:nfa A B) q w :=
  match q with
  | None => None
  | Some q => match (ext_transition eqA eqB g [q] w) with
              | nil => None
              | q::_ => Some q
              end
  end.


(* Indistinguishable states of a DFA *)
Definition dfa_indisting_states {A B} eqA eqB (g:nfa A B) q1 q2 :=
  forall w, in_opt (dfa_transition eqA eqB g (Some q1) w) (Some (accept_states g)) <-> in_opt (dfa_transition eqA eqB g (Some q2) w) (Some (accept_states g)).


(** Proofs about DFAs **)

(* DFA is NFA *)
Lemma dfa_actual_nfa {A B} (g:nfa A B) (H:dfa g) :
  actual_nfa g.
Proof.
  induction H.
  auto.
  1-7: inversion IHdfa; apply actual_nfa_cons with eqA eqB; auto.
Qed.

(* Every start state is equal *)
Lemma dfa_start {A B} (g:nfa A B) q0 q :
  dfa g -> In q0 (start_states g) -> In q (start_states g) -> q = q0.
Proof.
  intros.
  induction H; auto.
  - inversion H0.
  - simpl in H0, H1; destruct H0, H1; subst; auto.
  - simpl in H0, H1; rewrite H2 in H0, H1; destruct H0, H1; subst.
    + auto.
    + inversion H1.
    + inversion H0.
    + inversion H1.
Qed.

(* Every state in transition is equal *)
Lemma dfa_trans {A B} eqA eqB (g:nfa A B) q0 q q' a :
  (forall q1 q2, q1=q2 <-> eqA q1 q2=true) -> (forall a b, a=b <-> eqB a b=true) ->
  dfa g ->
  In q (transition eqA eqB g q0 a) ->
  In q' (transition eqA eqB g q0 a) ->
  q' = q.
Proof.
  intros;
  apply (transition_in eqA eqB g q0 a q H H0) in H2;
  apply (transition_in eqA eqB g q0 a q' H H0) in H3;
  induction H1.
  destruct H2.
  1-5: destruct H2, H3; try discriminate; apply IHdfa; auto.
  - destruct H2, H3.
    + injection H2; injection H3; intros; subst; auto.
    + injection H2; intros; subst; auto.
    + injection H3; intros; subst; auto.
    + auto.
  - destruct H2, H3.
    + injection H2; injection H3; intros; subst; auto.
    + injection H2; intros; subst; auto.
      apply H4 in H3; destruct H3.
    + injection H3; intros; subst; auto.
      apply H4 in H2; destruct H2.
    + auto.
Qed.

Lemma dfa_trans_ext {A B} eqA eqB (g:nfa A B) q0 q q' w l :
  (forall q1 q2, q1=q2 <-> eqA q1 q2=true) -> (forall a b, a=b <-> eqB a b=true) ->
  dfa g ->
  ext_transition eqA eqB g [q0] w = l ->
  In q l ->
  In q' l ->
  q' = q.
Proof.
  intros.
  rewrite <- H2 in H3, H4.
  clear H2.
  generalize dependent q;
  generalize dependent q';
  generalize dependent q0;
  induction w; intros.
  destruct H3, H4; subst; try (destruct H3); try (destruct H2); auto.
  simpl in H3, H4; rewrite app_nil_r in H3, H4.
  assert (forall q q', In q (transition eqA eqB g q0 a) ->
  In q' (transition eqA eqB g q0 a) -> q' = q).
    intros; apply dfa_trans with eqA eqB g q0 a; auto.
  induction (transition eqA eqB g q0 a).
  rewrite ext_transition_nil in H3; destruct H3.
  replace (a0::l0) with ([a0] ++ l0) in H3, H4.
  2: auto.
  rewrite ext_transition_states_app in H3, H4.
  apply in_app_or in H3; apply in_app_or in H4.
  destruct H3, H4.
  - apply (IHw a0); auto.
  - clear IHl0; induction l0.
    rewrite ext_transition_nil in H4; destruct H4.
    replace (a1 :: l0) with ([a1] ++ l0) in H4.
    2: auto.
    rewrite ext_transition_states_app in H4; apply in_app_or in H4;
    destruct H4.
    + assert (a1 = a0).
        apply H2. left; auto. right; left; auto.
      subst; apply IHw with a0; auto.
    + apply IHl0.
      auto.
      intros; apply H2.
      * destruct H5; subst.
        left; auto.
        right; right; auto.
      * destruct H6; subst.
        left; auto.
        right; right; auto.
  - clear IHl0; induction l0.
    rewrite ext_transition_nil in H3; destruct H3.
    replace (a1 :: l0) with ([a1] ++ l0) in H3.
    2: auto.
    rewrite ext_transition_states_app in H3; apply in_app_or in H3;
    destruct H3.
    + assert (a1 = a0).
        apply H2. left; auto. right; left; auto.
      subst; apply IHw with a0; auto.
    + apply IHl0.
      auto.
      intros; apply H2.
      * destruct H5; subst.
        left; auto.
        right; right; auto.
      * destruct H6; subst.
        left; auto.
        right; right; auto.
  - apply IHl0.
    1,2: auto.
    intros; apply H2; right; auto.
Qed.

(* A DFA concatenated to a list of components constructed by accept is a DFA *)
Lemma app_accept_dfa {A B} (g:nfa A B) l :
  dfa g ->
  (forall c, In c l -> exists q, c = accept q) ->
  dfa (g ++ l).
Proof.
  intros; induction H.
  - simpl; induction l.
    apply cons_empty_dfa; auto.
    destruct a.
    + assert (In (state q) (state q::l)).
        intuition.
      apply H0 in H1; destruct H1; discriminate.
    + assert (In (symbol a) (symbol a::l)).
        intuition.
      apply H0 in H1; destruct H1; discriminate.
    + assert (In (start q) (start q::l)).
        intuition.
      apply H0 in H1; destruct H1; discriminate.
    + apply cons_dfa_accept, IHl.
      intros; apply H0; intuition.
    + assert (In (trans q a q') (trans q a q'::l)).
        intuition.
      apply H0 in H1; destruct H1; discriminate.
  - apply cons_dfa_state; intuition.
  - apply cons_dfa_symbol; intuition.
  - apply cons_dfa_accept; intuition.
  - simpl; apply cons_dfa_start_repeat.
    intuition.
    apply in_app_start_states_or; intuition.
  - simpl; apply cons_dfa_start.
    intuition.
    apply start_states_app_nil.
    auto.
    clear IHdfa H1 H g q; induction l.
    auto.
    destruct a.
    1,2,4,5: intuition.
    assert (In (start q) (start q::l)).
      intuition.
    apply H0 in H; destruct H; discriminate.
  - simpl; apply cons_dfa_trans_repeat.
    intuition.
    apply in_or_app; intuition.
  - simpl; apply cons_dfa_trans.
    intuition.
    intros q'' contra.
    apply in_app_or in contra; destruct contra.
    apply H1 in H2; auto.
    apply H0 in H2; destruct H2; discriminate.
Qed.

(* Path is unique *)
Lemma dfa_path {A B} (g:nfa A B) q1 q2 q3 w :
  dfa g -> path g q1 q2 w -> path g q1 q3 w ->
  q2 = q3.
Proof.
  intros;
  pose proof H; apply dfa_actual_nfa in H; inversion H; subst.
  assert (In q2 (ext_transition eqA eqB g [q1] w)).
    apply path_ext_transition; auto.
  assert (In q3 (ext_transition eqA eqB g [q1] w)).
    apply path_ext_transition; auto.
  remember (ext_transition eqA eqB g [q1] w) as l eqn:H7.
  apply (dfa_trans_ext eqA eqB g q1 q3 q2 w l); auto.
Qed.












