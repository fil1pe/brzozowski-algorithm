Require Import List Bool nfa.
Include ListNotations.


(** Word reversing **)

Fixpoint revert_word {A} (w:list A) :=
  match w with
  | nil => nil
  | a::w => revert_word w ++ [a]
  end.
Notation "w ^ 'R'" := (revert_word w) (at level 10).

(* Distributive property *)
Lemma revert_word_distr {A} (w1 w2:list A) :
  (w1 ++ w2)^R = (w2^R) ++ (w1^R).
Proof.
  induction w1; simpl.
  - rewrite app_nil_r; auto.
  - rewrite IHw1, app_assoc; auto.
Qed.

(* A word is equal to itself reverted twice *)
Lemma revert_word_twice {A} (w:list A) :
  w = (w^R)^R.
Proof.
  induction w.
  auto.
  simpl; rewrite revert_word_distr, <- IHw; auto.
Qed.


(** NFA reversing **)

(* Reverts the transitions and swicth the constructors start and accept *)
Fixpoint rev {A B} (g:nfa A B) :=
  match g with
  | nil => nil
  | start q::g => accept q::rev g
  | accept q::g => start q::rev g
  | trans q a q'::g => trans q' a q::rev g
  | x::g => x::rev g
  end.

(* A reverted NFA is a NFA *)
Lemma reverted_actual_nfa {A B} (g:nfa A B) :
  actual_nfa g -> actual_nfa (rev g).
Proof.
  intros; inversion H;
  apply (actual_nfa_cons (rev g) eqA eqB); auto.
Qed.

(* A NFA is equal to itself reverted twice *)
Lemma rev_twice {A B} (g:nfa A B) :
  g = rev (rev g).
Proof.
  induction g.
  auto.
  simpl; destruct a; simpl; rewrite <- IHg; auto.
Qed.

(* A start state becomes an accept state *)
Lemma revert_start {A B} (g:nfa A B) q :
  In q (start_states g) -> In q (accept_states (rev g)).
Proof.
  intros; induction g.
  destruct H.
  simpl in H; destruct a.
  1-2,4-5: try right; try right; intuition.
  destruct H.
  left; intuition.
  right; intuition.
Qed.

(* An accept state becomes a start state *)
Lemma revert_accept {A B} (g:nfa A B) q :
  In q (accept_states g) -> In q (start_states (rev g)).
Proof.
  intros; induction g.
  destruct H.
  simpl in H; destruct a.
  1-3,5: try right; try right; intuition.
  destruct H.
  left; intuition.
  right; intuition.
Qed.

(* The transitions are reversed *)
Lemma revert_trans {A B} (g:nfa A B) q a q' :
  In (trans q a q') g -> In (trans q' a q) (rev g).
Proof.
  intros.
  induction g.
  destruct H.
  simpl in H; destruct a0.
  1-4: destruct H; try discriminate; right; intuition.
  destruct H.
  injection H; intros; subst; left; auto.
  right; intuition.
Qed.

(* All paths are reverted *)
Lemma reverted_path {A B} (g:nfa A B) q1 q2 w :
  path g q1 q2 w <-> path (rev g) q2 q1 (w^R).
Proof.
  assert (forall (g:nfa A B) q1 q2 w, path g q1 q2 w -> path (rev g) q2 q1 (w^R)). {
    clear g q1 q2 w; intros.
    induction H.
    constructor.
    rewrite revert_word_distr; apply path_left with q2.
    2: auto.
    apply revert_trans; auto.
  }
  split; intros.
  apply H; auto.
  rewrite revert_word_twice; replace g with (rev (rev g)).
  2: symmetry; apply rev_twice.
  apply H; auto.
Qed.

(* The reverted language *)
Lemma reverted_nfa_lang {A B} eq eq' (g:nfa A B) w :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  (forall a b, a=b <-> eq' a b=true) ->
  lang eq eq' g w <-> lang eq eq' (rev g) (w^R).
Proof.
  intros H H0; assert (forall g w, lang eq eq' g w -> lang eq eq' (rev g) (w^R)). {
    unfold lang, has_accept_state; clear g w; intros.
    destruct H1 as [q [H1 H2]].
    apply ext_transition_list in H1; destruct H1 as [q0 [H1 H3]].
    exists q0; split.
    2: apply revert_start; auto.
    apply (path_ext_transition eq eq' g q0 q w H H0) in H3.
    apply (ext_transition_single eq eq' (rev g) (start_states (rev g)) q q0 (w^R)); split.
    apply revert_accept; auto.
    apply path_ext_transition.
    1-2: auto.
    apply reverted_path in H3; auto.
  }
  split; intros.
  intuition.
  rewrite (rev_twice g), revert_word_twice.
  intuition.
Qed.

(* If a NFA does not have any start state, its reversion will not have any accept state *)
Lemma rev_start_nil {A B} {g:nfa A B} :
  start_states g = [] -> accept_states (rev g) = [].
Proof.
  intros; induction g.
  auto.
  destruct a.
  1,2,4,5: auto.
  inversion H.
Qed.

(* The reversing of a NFA has the same states *)
Lemma revert_states_are_states {A B} (g:nfa A B) :
  forall q, In q (states (rev g)) <-> In q (states g).
Proof.
  induction g; intros; split; intros.
  1,2: destruct H.
  1,2: destruct a.
  - destruct H; subst.
    left; auto.
    right; apply IHg; auto.
  - simpl; apply IHg; auto.
  - destruct H; subst.
    left; auto.
    right; apply IHg; auto.
  - destruct H; subst.
    left; auto.
    right; apply IHg; auto.
  - destruct H; subst.
    right; left; auto.
    destruct H; subst.
    left; auto.
    right; right; apply IHg; auto.
  - destruct H; subst.
    left; auto.
    right; apply IHg; auto.
  - simpl; apply IHg; auto.
  - destruct H; subst.
    left; auto.
    right; apply IHg; auto.
  - destruct H; subst.
    left; auto.
    right; apply IHg; auto.
  - destruct H; subst.
    right; left; auto.
    destruct H; subst.
    left; auto.
    right; right; apply IHg; auto.
Qed.











