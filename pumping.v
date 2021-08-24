Require Import List Bool Lia utils nfa dfa.
Include ListNotations.


(* The pigeonhole principle *)
Lemma pigeonhole {X} (l1 l2 : list X) :
  (forall x1 x2 : X, {x1 = x2} + {x1 <> x2}) ->
  (forall x, In x l2 -> In x l1) -> length l2 > length l1 ->
  exists l2a l2b l2c y, l2 = l2a ++ [y] ++ l2b ++ [y] ++ l2c.
Proof.
  intro eq_dec; revert l1; induction l2 as [|y l2 IH]; intros l1 H H0.
  - simpl in H0; nia.
  - destruct l1 as [|x l1].
    destruct (H y); left; auto.
    destruct (in_dec eq_dec y l2) as [H1|H1].
    + apply in_split in H1; destruct H1 as [l2a [l2b H1]]; subst;
      exists nil, l2a, l2b, y; auto.
    + assert (H2: In y (x::l1)). apply H; left; auto.
      apply in_split in H2; destruct H2 as [l1a [l1b H2]];
      destruct IH with (l1a ++ l1b) as [l2a [l2b [l2c [z H4]]]].
      * intros z H3; apply in_or_app; rewrite H2 in H; specialize (H z);
        assert (H4: In z (l1a ++ y :: l1b)). apply H; right; auto.
        apply in_app_or in H4; destruct H4 as [H4|H4].
        left; auto.
        destruct H4 as [H4|H4].
        subst; contradiction.
        right; auto.
      * assert (H3: length l1 = length (l1a ++ l1b)). {
          rewrite app_length; assert (H3: length ([x] ++ l1) = length (l1a ++ [y] ++ l1b)).
            simpl ([x] ++ l1); rewrite H2; auto.
          rewrite app_length, app_length, app_length in H3; simpl in H3; nia.
        }
        simpl in H0; rewrite app_length; rewrite app_length in H3; nia.
      * exists (y::l2a), l2b, l2c, z; subst; auto.
Qed.

(* We need a definition of path with history *)
Inductive path' {A B} (g:nfa A B) : list A->list B->Prop :=
  | path'_nil (q:A) : path' g [q] nil
  | path'_next p q1 q2 w a : path' g (p ++ [q1]) w -> In (trans q1 a q2) g -> path' g (p ++ [q1; q2]) (w ++ [a]).

(* It is equivalent to the former *)
Lemma path'_correct {A B} (g:nfa A B) q1 q2 w :
  w <> nil ->
  path g q1 q2 w <-> exists l, path' g (q1::l ++ [q2]) w.
Proof.
  split; intros.
  - generalize dependent q2; induction w using rev_ind; intros.
    destruct H; auto.
    inversion H0; subst.
    destruct w; discriminate.
    apply app_inj_tail in H1; destruct H1; subst;
    destruct w.
    {
      inversion H2; subst.
      2: destruct w; discriminate.
      exists nil; simpl; replace (path' g [q3; q2] [x]) with (path' g (nil ++ [q3; q2]) (nil ++ [x])).
      apply path'_next; try constructor; auto.
      auto.
    }
    destruct IHw with q3.
    intro contra; discriminate.
    auto.
    exists (x0 ++ [q3]); replace (q1 :: (x0 ++ [q3]) ++ [q2]) with ((q1 :: x0) ++ [q3; q2]).
    2: rewrite <- app_assoc; auto.
    apply path'_next; auto.
  - destruct H0 as [l H0];
    generalize dependent l; generalize dependent q2; induction w using rev_ind; intros.
    {
      inversion H0.
      destruct l; discriminate.
      destruct w; discriminate.
    }
    inversion H0.
    destruct l; discriminate.
    apply app_inj_tail in H2; destruct H2; subst.
    replace (p ++ [q0; q3]) with ((p ++ [q0]) ++ [q3]) in H1.
    2: rewrite <- app_assoc; auto.
    replace (q1 :: l ++ [q2]) with ((q1 :: l) ++ [q2]) in H1.
    2: auto.
    apply app_inj_tail in H1; destruct H1; subst.
    destruct w as [|b w].
    {
      inversion H3.
      2: destruct w; discriminate.
      destruct p.
      2: destruct p; discriminate.
      destruct l.
      2: discriminate.
      simpl in *; injection H1; injection H5; intros; subst.
      replace [x] with (nil ++ [x]).
      2: auto.
      apply path_next with q1; try constructor; auto.
    }
    destruct l as [|q0' l _] using rev_ind.
    {
      destruct p.
      2: destruct p; discriminate.
      simpl in *; injection H1; intros; subst.
      inversion H3.
      destruct p; try destruct p; discriminate.
    }
    replace (q1 :: l ++ [q0']) with ((q1 :: l) ++ [q0']) in H1.
    2: auto.
    apply app_inj_tail in H1; destruct H1; subst;
    destruct IHw with q0' l.
    intro contra; discriminate.
    replace (q1 :: l ++ [q0']) with ((q1 :: l) ++ [q0']); auto.
    {
      inversion H3.
      destruct l; discriminate.
      destruct w0; discriminate.
    }
    apply path_next with q3.
    2: auto.
    apply path_next with q0; auto.
Qed.

(* The history length is equal to the word length plus one *)
Lemma path'_length {A B} (g:nfa A B) l w :
  path' g l w -> length l = S (length w).
Proof.
  intros; induction H.
  auto.
  repeat rewrite app_length; rewrite app_length in IHpath';
  simpl in *; nia.
Qed.

(* All terms in the history is a state *)
Lemma path'_in_states {A B} (g:nfa A B) l w :
  w <> nil -> path' g l w -> (forall q, In q l -> In q (states g)).
Proof.
  intros; generalize dependent q; induction H0.
  destruct H; auto.
  inversion H0; subst; intros.
  - destruct p.
    2: destruct p; discriminate.
    simpl in *; inversion H3; intros;
    destruct H2; subst.
    apply trans_in_states with a q2; auto.
    destruct H2.
    2: destruct H2.
    subst; apply trans_in_states_r with a q1; auto.
  - replace (p ++ [q1; q2]) with ((p ++ [q1]) ++ [q2]) in H5.
    2: rewrite <- app_assoc; auto.
    apply in_app_or in H5; destruct H5.
    2: destruct H5; subst.
    3: destruct H5.
    2: apply trans_in_states_r with a q1; auto.
    apply IHpath'.
    2: auto.
    intro contra; destruct w0; discriminate.
Qed.

(* We can decompose the path' *)
Lemma app_path' {A B} (g:nfa A B) l1 q l2 w :
  path' g (l1 ++ [q] ++ l2) w -> exists w1 w2, w = w1 ++ w2 /\ path' g (l1 ++ [q]) w1 /\
  path' g (q::l2) w2.
Proof.
  intros; generalize dependent l2; generalize dependent q; induction w using rev_ind; intros.
  {
    inversion H.
    2: destruct w; discriminate.
    destruct l1.
    2: destruct l1; discriminate.
    destruct l2.
    2: discriminate.
    exists nil, nil; intuition.
  }
  destruct l2 as [|q' l2 _] using rev_ind.
  {
    clear IHw; inversion H.
    destruct w; discriminate.
    apply app_inj_tail in H1; destruct H1; subst;
    replace (p ++ [q1; q2]) with ((p ++ [q1]) ++ [q2]) in H0.
    2: rewrite <- app_assoc; auto.
    apply app_inj_tail in H0; destruct H0; subst;
    exists (w ++ [x]), nil; repeat split.
    rewrite app_nil_r; auto.
    2: constructor.
    simpl in *; replace ((p ++ [q1]) ++ [q]) with (p ++ [q1; q]) in H.
    auto.
    rewrite <- app_assoc; auto.
  }
  inversion H.
  destruct w; discriminate.
  apply app_inj_tail in H1; destruct H1; subst.
  replace (p ++ [q1; q2]) with ((p ++ [q1]) ++ [q2]) in H0.
  2: rewrite <- app_assoc; auto.
  replace (l1 ++ q :: l2 ++ [q']) with ((l1 ++ q :: l2) ++ [q']) in H0.
  2: rewrite <- app_assoc; auto.
  apply app_inj_tail in H0; destruct H0; subst;
  rewrite H0 in H2; apply IHw in H2; destruct H2 as [w1 [w2 H2]];
  exists w1, (w2 ++ [x]); repeat split.
  destruct H2; rewrite H1, <- app_assoc; auto.
  intuition.
  destruct l2 as [|q2 l2 _] using rev_ind.
  - apply app_inj_tail in H0; destruct H0; subst;
    simpl; replace ([q; q']) with (nil ++ [q; q']).
    2: auto.
    apply path'_next; intuition.
  - replace (q :: (l2 ++ [q2]) ++ [q']) with ((q :: l2) ++ [q2; q']).
    2: rewrite <- app_assoc; auto.
    apply path'_next.
    intuition.
    replace (l1 ++ q :: l2 ++ [q2]) with ((l1 ++ q :: l2) ++ [q2]) in H0.
    2: rewrite <- app_assoc; auto.
    apply app_inj_tail in H0; destruct H0; subst.
    auto.
Qed.

(* And compose *)
Lemma path'_app {A B} (g:nfa A B) l1 q l2 w1 w2 :
  path' g (l1 ++ [q]) w1 ->
  path' g (q::l2) w2 ->
  path' g (l1 ++ [q] ++ l2) (w1 ++ w2).
Proof.
  intros; generalize dependent l2; induction w2 as [|a w2 IH] using rev_ind; intros.
  {
    inversion H0; subst.
    repeat rewrite app_nil_r; auto.
    destruct w; discriminate.
  }
  destruct l2 as [|q' l2 _] using rev_ind.
  {
    inversion H0; subst.
    repeat rewrite app_nil_r; auto.
    destruct p.
    discriminate.
    destruct p; discriminate.
  }
  inversion H0; subst.
  destruct w2; discriminate.
  apply app_inj_tail in H2; destruct H2; subst;
  replace (p ++ [q1; q2]) with ((p ++ [q1]) ++ [q2]) in H1.
  2: rewrite <- app_assoc; auto.
  replace (q :: l2 ++ [q']) with ((q :: l2) ++ [q']) in H1.
  2: auto.
  apply app_inj_tail in H1; destruct H1; subst;
  rewrite H1 in H3; apply IH in H3;
  destruct l2 as [|q2 l2 _] using rev_ind.
  2: {
    simpl; replace (l1 ++ q :: (l2 ++ [q2]) ++ [q']) with ((l1 ++ q :: l2) ++ [q2; q']).
    2: repeat rewrite <- app_assoc; auto.
    replace (w1 ++ w2 ++ [a]) with ((w1 ++ w2) ++ [a]).
    2: rewrite app_assoc; auto.
    replace (q :: l2 ++ [q2]) with ((q :: l2) ++ [q2]) in H1.
    2: auto.
    apply app_inj_tail in H1; destruct H1; subst;
    apply path'_next; repeat rewrite <- app_assoc; auto.
  }
  simpl in *; replace (w1 ++ w2 ++ [a]) with ((w1 ++ w2) ++ [a]).
  2: rewrite app_assoc; auto.
  destruct p.
  2: destruct p; discriminate.
  injection H1; intros; subst;
  apply path'_next; auto.
Qed.


(** Pumping lemma **)

(* For every path, there's another path from and to the same states through a word
whose length is less or qual to the number of states *)
Lemma pumping' {A B} eq (g:nfa A B) q1 l q2 w (H: forall q1 q2, q1=q2 <-> eq q1 q2 = true) :
  q1 <> q2 ->
  path' g (q1::l ++ [q2]) w ->
  exists l' w', path' g (q1::l' ++ [q2]) w' /\
  length w' <= length (nodup (eq_dec eq H) (states g)).
Proof.
  intro H20; intros; generalize dependent l; generalize dependent q2; induction w as [|a w IH] using rev_ind; intros.
  - inversion H0.
    destruct l; discriminate.
    destruct w; discriminate.
  - destruct l as [|q3 l _] using rev_ind.
    + exists nil, (w ++ [a]); simpl in *; split.
      auto.
      replace (length (w ++ [a])) with 1.
      2: apply path'_length in H0; simpl in H0; nia.
      inversion H0; apply app_inj_tail in H2; destruct H2; subst.
      assert (In q0 (nodup (eq_dec eq H) (states g))).
        apply nodup_In; apply trans_in_states in H4; auto.
      destruct (nodup (eq_dec eq H) (states g)) as [|x l].
      destruct H2.
      simpl; nia.
    + inversion H0.
      destruct w; discriminate.
      apply app_inj_tail in H2; destruct H2; subst;
      replace (p ++ [q0; q4]) with ((p ++ [q0]) ++ [q4]) in H1.
      2: rewrite <- app_assoc; auto.
      replace (q1 :: (l ++ [q3]) ++ [q2]) with ((q1 :: (l ++ [q3])) ++ [q2]) in H1.
      2: auto.
      apply app_inj_tail in H1; destruct H1; subst;
      replace (q1 :: l ++ [q3]) with ((q1 :: l) ++ [q3]) in H1.
      2: auto.
      apply app_inj_tail in H1; destruct H1; subst;
      destruct (eq_dec eq H q1 q3) as [H5|H11].
      {
        subst; exists nil, [a]; split; simpl in *.
        - replace [a] with (nil ++ [a]).
          2: auto.
          replace [q3; q2] with (nil ++ [q3; q2]).
          2: auto.
          apply path'_next; try constructor; auto.
        - assert (In q3 (nodup (eq_dec eq H) (states g))).
            apply nodup_In; apply trans_in_states in H4; auto.
          destruct (nodup (eq_dec eq H) (states g)) as [|L x].
          destruct H1.
          simpl; nia.
      }
      apply IH in H3.
      2: auto.
      destruct H3 as [l' [w' [H3 H5]]];
      assert (path' g ((q1 :: l') ++ [q3; q2]) (w' ++ [a])).
        apply path'_next; auto.
      destruct (Compare_dec.le_gt_dec (length ((q1 :: l') ++ [q3; q2])) (length (nodup (eq_dec eq H) (states g)))) as [H2|H2].
      {
        exists (l' ++ [q3]), (w' ++ [a]); split.
        rewrite <- app_assoc; auto.
        apply path'_length in H1; nia.
      }
      apply pigeonhole in H2.
      2: apply (eq_dec eq H).
      2: {
        intros; apply nodup_In, path'_in_states with ((q1 :: l') ++ [q3; q2]) (w' ++ [a]).
        intros contra; destruct w'; discriminate.
        1,2: auto.
      }
      destruct H2 as [l1 [l2 [l3 [q H2]]]]; destruct l1; destruct l3 as [|q' l3 _] using rev_ind; simpl in *.
      * replace (q1 :: l' ++ [q3; q2]) with ((q1 :: l' ++ [q3]) ++ [q2]) in H2.
        2: simpl; rewrite <- app_assoc; auto.
        replace (q :: l2 ++ [q]) with ((q :: l2) ++ [q]) in H2.
        2: auto.
        apply app_inj_tail in H2; destruct H2; subst;
        injection H2; intros; subst; destruct H20; auto.
      * replace (q1 :: l' ++ [q3; q2]) with ((q1 :: l' ++ [q3]) ++ [q2]) in H2.
        2: simpl; rewrite <- app_assoc; auto.
        replace (q :: l2 ++ q :: l3 ++ [q']) with ((q :: l2 ++ q :: l3) ++ [q']) in H2.
        2: simpl; rewrite <- app_assoc; auto.
        apply app_inj_tail in H2; destruct H2;
        injection H2; intros; subst.
        destruct l3 as [|q4 l3 _] using rev_ind.
        apply app_inj_tail in H7; destruct H7; subst; destruct H11; auto.
        replace (l2 ++ q :: l3 ++ [q4]) with ((l2 ++ q :: l3) ++ [q4]) in H7.
        2: rewrite <- app_assoc; auto.
        apply app_inj_tail in H7; destruct H7; subst.
        replace (q :: (l2 ++ q :: l3) ++ [q4; q']) with ((q :: l2) ++ [q] ++ (l3 ++ [q4; q'])) in H1.
        2: rewrite <- app_assoc; auto.
        apply app_path' in H1.
        destruct H1 as [w1 [w2 H1]]; exists (l3 ++ [q4]), w2; split.
        2: {
          destruct H1, H6.
          assert (length (w' ++ [a]) = length (w1 ++ w2)).
            rewrite H1; auto.
          repeat rewrite app_length in H8; simpl in *.
          assert (length w1 >= 1).
          2: nia.
          destruct w1.
          2: simpl; nia.
          apply path'_length in H6; apply path'_length in H7; apply path'_length in H3;
          simpl in H3; repeat rewrite app_length in H3;
          simpl in H7; repeat rewrite app_length in H7;
          simpl in *; nia.
        }
        rewrite <- app_assoc; intuition.
      * injection H2; intros; subst.
        replace (l' ++ [q3; q2]) with ((l' ++ [q3]) ++ [q2]) in H6.
        2: rewrite <- app_assoc; auto.
        replace (l1 ++ q :: l2 ++ [q]) with ((l1 ++ q :: l2) ++ [q]) in H6.
        2: rewrite <- app_assoc; auto.
        apply app_inj_tail in H6; destruct H6; subst;
        destruct l2 as [|q4 l2 _] using rev_ind.
        apply app_inj_tail in H6; destruct H6; subst;
        exists l1, w'; intuition.
        replace (l1 ++ q :: l2 ++ [q4]) with ((l1 ++ q :: l2) ++ [q4]) in H6.
        2: rewrite <- app_assoc; auto.
        apply app_inj_tail in H6; destruct H6; subst.
        replace (a0 :: (l1 ++ q :: l2) ++ [q4; q]) with ((a0 :: l1) ++ [q] ++ (l2 ++ [q4; q])) in H1.
        2: simpl; repeat rewrite <- app_assoc; auto.
        apply app_path' in H1.
        destruct H1 as [w1 [w2 H1]]; exists l1, w1; split.
        intuition.
        destruct H1, H6.
        assert (length (w' ++ [a]) = length (w1 ++ w2)).
          rewrite H1; auto.
        repeat rewrite app_length in H8; simpl in *.
        assert (length w2 >= 1).
        2: nia.
        destruct w2.
        2: simpl; nia.
        apply path'_length in H6; apply path'_length in H7; apply path'_length in H3;
        simpl in H3; repeat rewrite app_length in H3;
        simpl in H7; repeat rewrite app_length in H7;
        simpl in *; nia.
      * injection H2; intros; subst.
        replace (l' ++ [q3; q2]) with ((l' ++ [q3]) ++ [q2]) in H6.
        2: rewrite <- app_assoc; auto.
        replace (l1 ++ q :: l2 ++ q :: l3 ++ [q']) with ((l1 ++ q :: l2 ++ q :: l3) ++ [q']) in H6.
        2: simpl; repeat (simpl; rewrite <- app_assoc); auto.
        apply app_inj_tail in H6; destruct H6; subst.
        replace (a0 :: l' ++ [q3; q']) with (a0 :: (l' ++ [q3]) ++ [q']) in H1.
        2: rewrite <- app_assoc; auto.
        rewrite H6 in H1;
        replace (a0 :: (l1 ++ q :: l2 ++ q :: l3) ++ [q']) with ((a0 :: l1) ++ [q] ++ (l2 ++ q :: l3 ++ [q'])) in H1.
        2: repeat (simpl; rewrite <- app_assoc); auto.
        apply app_path' in H1.
        destruct H1 as [w1 [w'' [H1 [H7 H8]]]].
        replace (q :: l2 ++ q :: l3 ++ [q']) with ((q :: l2) ++ [q] ++ (l3 ++ [q'])) in H8.
        2: auto.
        apply app_path' in H8; destruct H8 as [w2 [w3 H8]].
        exists (l1 ++ q :: l3), (w1 ++ w3); split.
        {
          replace (a0 :: (l1 ++ q :: l3) ++ [q']) with ((a0 :: l1) ++ [q] ++ (l3 ++ [q'])).
          2: rewrite <- app_assoc; auto.
          apply path'_app; intuition.
        }
        destruct H8; subst; simpl in *.
        assert (length (w' ++ [a]) = length (w1 ++ w2 ++ w3)).
          rewrite H1; auto.
        repeat (simpl in H8; rewrite app_length in H8);
        assert (length w2 >= 1).
        2: rewrite app_length; nia.
        destruct H9; destruct w2.
        2: simpl; nia.
        inversion H9.
        destruct l2; discriminate.
        destruct w0; discriminate.
Qed.

Lemma pumping {A B} eq (g:nfa A B) q1 q2 w (H: forall q1 q2, q1=q2 <-> eq q1 q2 = true) :
  path g q1 q2 w ->
  exists w', path g q1 q2 w' /\
  length w' <= length (nodup (eq_dec eq H) (states g)).
Proof.
  intros; destruct (eq q1 q2) eqn:H1.
  apply H in H1; subst; exists nil; split; simpl; try nia; constructor.
  destruct w.
  exists nil; split; simpl; try nia; auto.
  apply path'_correct in H0.
  2: discriminate.
  destruct H0 as [l H0]; apply (pumping' eq g q1 l q2 (b::w) H) in H0.
  2: intros H2; apply H in H2; rewrite H2 in H1; discriminate.
  destruct H0 as [l' [w' H0]]; destruct w';  destruct H0.
  inversion H0.
  destruct l'; discriminate.
  destruct w0; discriminate.
  assert (path g q1 q2 (b0::w')). {
    apply path'_correct.
    discriminate.
    exists l'; auto.
  }
  exists (b0 :: w'); intuition.
Qed.

(* L(G1) is subset of L(G2) if G2 has the pumping paths of G1 *)
Lemma pumping_language {A B} eq H (g1 g2:nfa A B) (P:A->A->Prop) q1 q2 w q3 :
  (forall q1 q2, P q1 q2 -> P q2 q1) ->
  dfa g2 -> P q1 q2 ->
  (forall w q3, length w <= S (length (nodup (eq_dec eq H) (states g1))) ->
    path g1 q1 q3 w -> exists q4, P q3 q4 /\ path g2 q2 q4 w) ->
  (forall q1 q2, In q1 (states g2) -> In q2 (states g2) ->
    P q1 q2 -> q1 = q2) ->
  (forall q1 q2 q3, P q1 q2 -> P q2 q3 -> P q1 q3) ->
  path g1 q1 q3 w ->
  exists q4, P q3 q4 /\ path g2 q2 q4 w.
Proof.
  intros H20; intros; generalize dependent q3;
  induction w using rev_ind; intros.
  {
    inversion H5; subst.
    exists q2; intuition; constructor.
    destruct w; discriminate.
  }
  inversion H5; subst.
  destruct w; discriminate.
  apply app_inj_tail in H6; destruct H6; subst.
  pose proof H7; apply IHw in H7.
  apply (pumping eq g1 q1 q4 w H) in H6;
  destruct H6 as [w' [H6 H9]].
  assert (path g1 q1 q3 (w' ++ [x])).
    apply path_next with q4; try constructor; auto.
  pose proof H6; apply H2 in H11.
  2: nia.
  destruct H11 as [q5 [H11 H12]].
  destruct H7 as [_q5 [H7 H13]].
  destruct w.
  apply H2; simpl; try nia; auto.
  assert (_q5 = q5). {
    assert (In _q5 (states g2)).
      inversion H13; apply trans_in_states_r with a q6; auto.
    apply H3.
    auto.
    {
      inversion H12; subst.
      2: apply trans_in_states_r with a q6; auto.
      clear H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H20 IHw; induction H13.
      auto.
      apply IHpath, trans_in_states with a q5; auto.
    }
    apply H4 with q4.
    apply H20.
    1,2: auto.
  }
  subst; clear H11.
  apply H2 in H8.
  2: rewrite app_length; simpl; nia.
  destruct H8 as [q6 [H8 H14]]; exists q6; split.
  auto.
  apply path_next with q5.
  auto.
  inversion H14; subst.
  destruct w'; discriminate.
  apply app_inj_tail in H11; destruct H11; subst.
  assert (q7 = q5).
  2: subst; auto.
  apply dfa_path with g2 q2 w'; auto.
Qed.

Lemma pumping_language_eq {A B} eq H (g1 g2:nfa (list A) B) q1 q2 w q3 :
  dfa g2 -> eq_sets q1 q2 ->
  (forall w q3, length w <= S (length (nodup (eq_dec eq H) (states g1))) ->
    path g1 q1 q3 w -> exists q4, eq_sets q3 q4 /\ path g2 q2 q4 w) ->
  (forall q1 q2, In q1 (states g2) -> In q2 (states g2) ->
    eq_sets q1 q2 -> q1 = q2) ->
  path g1 q1 q3 w ->
  exists q4, eq_sets q3 q4 /\ path g2 q2 q4 w.
Proof.
  intros; apply pumping_language with eq H g1 q1; auto.
  apply eq_sets_comm.
  intros.
  apply eq_sets_transitive with q4.
  apply eq_sets_comm.
  1,2: auto.
Qed.













