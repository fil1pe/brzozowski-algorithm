Ltac Tauto.intuition_solver ::= auto with *.

Require Export List.
Include ListNotations.

Section ListSets.

Variable Element : Type.

Hypothesis Element_eq_dec : forall (x1 x2:Element), { x1 = x2 } + { x1 <> x2 }.

Definition ListSet := list Element.

Definition subset s1 s2 := forall (x:Element), In x s1 -> In x s2.

(* s1 has element of s2 *)
Definition has_el s1 s2 := exists (x:Element), In x s1 /\ In x s2.

(* s1 and s2 are equivalent *)
Definition equiv_sets s1 s2 := subset s1 s2 /\ subset s2 s1.

Fixpoint powerset (s:ListSet) :=
  match s with
  | x::s => map (fun ps => x::ps) (powerset s) ++ powerset s
  | nil => [[]]
  end.

(* Commutation of equivalent states *)
Lemma equiv_sets_comm s1 s2 :
  equiv_sets s1 s2 -> equiv_sets s2 s1.
Proof.
  intro H; split;
  intros x H0; apply H; intuition.
Qed.

(* Transitive of equivalent states *)
Lemma equiv_sets_trans s1 s2 s3 :
  equiv_sets s1 s2 -> equiv_sets s2 s3 -> equiv_sets s1 s3.
Proof.
  intros H H0; split; intros x H1.
  apply H0, H; intuition.
  apply H, H0; intuition.
Qed.

(* An element inside a singleton is equal to the only element of it *)
Lemma in_singleton {A} (x1 x2:A) :
  In x1 [x2] -> x1 = x2.
Proof.
  intros [H|H].
  subst; intuition.
  contradiction.
Qed.

(* Every set is subset of itself *)
Lemma subset_self s :
  subset s s.
Proof.
  intros x H; intuition.
Qed.

(* Every set is equivalent to itself *)
Lemma equiv_sets_self s :
  equiv_sets s s.
Proof.
  split; intros x H; intuition.
Qed.

(* If a set is subset of nil, then it is nil *)
Lemma subset_nil s :
  subset s [] -> s = [].
Proof.
  intros; destruct s as [|x s].
  intuition.
  destruct (H x); intuition.
Qed.

(* Subset decider *)
Lemma subset_dec s1 s2 :
  {subset s1 s2} + {~ subset s1 s2}.
Proof.
  unfold subset.
  induction s1 as [|x s1 IH].
  left; intros x H; contradiction.
  destruct IH as [IH|IH].
  - destruct (in_dec Element_eq_dec x s2) as [H|H].
    left; intros y [H0|H0];
    subst; intuition.
    right; intro H0; intuition.
  - right; intro H; apply IH; intros y H0;
    intuition.
Defined.

(* Powerset returns correct subsets *)
Lemma powerset_correct s1 s2 :
  In s1 (powerset s2) -> subset s1 s2.
Proof.
  intros H.
  generalize dependent s1; induction s2 as [|x s2 IH]; intros s1 H.
  apply in_singleton in H; subst; apply subset_self.
  simpl in H; apply in_app_or in H.
  intros y H0.
  destruct H.
  apply in_map_iff in H; destruct H as [z [H1 H]]; symmetry in H1; subst.
  1,2: apply IH in H.
  destruct H0; subst.
  1-3: intuition.
Qed.

(* Powerset returns all subsets *)
Lemma powerset_complete s1 s2 :
  subset s1 s2 -> exists s1', equiv_sets s1 s1' /\ In s1' (powerset s2).
Proof.
  intros.
  generalize dependent s1; induction s2 as [|x2 s2 IH]; intros s1 H.
  apply subset_nil in H; subst; exists nil; split.
  split; apply subset_self.
  simpl; intuition.
  destruct (In_dec Element_eq_dec x2 s1) as [H0|H0].
  - assert (exists s3, ~ In x2 s3 /\ equiv_sets (x2::s3) s1). {
      clear H IH s2.
      generalize dependent x2; induction s1 as [|x1 s1 IH]; intros x2 H.
      contradiction.
      destruct (Element_eq_dec x2 x1) as [H1|H1].
      - subst.
        destruct (In_dec Element_eq_dec x1 s1) as [H1|H1].
        2: exists s1; repeat split; unfold subset; intuition.
        apply IH in H1.
        destruct H1 as [s3 [H1 H2]].
        exists s3; repeat split.
        intuition.
        1,2: intros x3 H3.
        apply H2 in H3; intuition.
        destruct H3.
        subst; intuition.
        apply H2; intuition.
      - destruct H.
        symmetry in H; contradiction.
        apply IH in H.
        destruct H as [s3 [H H0]].
        exists (x1::s3).
        split.
        intros H2; apply H; destruct H2; try symmetry in H2; intuition.
        split; intros x H2. {
          destruct H2.
          subst; right; apply H0; intuition.
          destruct H2.
          subst; intuition.
          right; apply H0; intuition.
        }
        destruct H2.
        subst; intuition.
        apply H0 in H2.
        repeat destruct H2; intuition.
    }
    destruct H1 as [s3 [H1 H2]].
    assert (subset s3 s2). {
      intros x3 H3.
      destruct H2 as [H2 _].
      assert (In x3 (x2::s3)).
      intuition.
      apply H2 in H4.
      apply H in H4; destruct H4.
      subst; contradiction.
      intuition.
    }
    apply IH in H3; clear IH; destruct H3 as [s1' [H3 H4]].
    exists (x2::s1').
    split.
    + clear H1 H4.
      split. {
        intros x H4.
        apply H2 in H4.
        destruct H4.
        - subst; intuition.
        - right; apply H3; intuition.
      }
      intros x H4.
      destruct H4.
      subst; intuition.
      apply H3 in H1.
      apply H2; intuition.
    + simpl; apply in_or_app; left.
      apply in_map_iff.
      exists s1'; intuition.
  - assert (subset s1 s2). {
      clear IH.
      induction s1 as [|x1 s1 IH].
      - intros x contra; contradiction.
      - assert (subset s1 (x2 :: s2)). {
          intros x H1.
          assert (In x (x1::s1)); intuition.
        }
        apply IH in H1.
        2: intro H2; apply H0; intuition.
        clear IH H1.
        intros x H1.
        assert (In x (x2::s2)).
        intuition.
        destruct H2.
        + subst; contradiction.
        + intuition.
    }
    apply IH in H1.
    destruct H1 as [s1' H1].
    exists s1'; split.
    2: simpl; apply in_or_app.
    1,2: intuition.
Qed.

(* Equivalent sets decider *)
Lemma equiv_sets_dec s1 s2 :
  {equiv_sets s1 s2} + {~ equiv_sets s1 s2}.
Proof.
  unfold equiv_sets.
  destruct (subset_dec s1 s2) as [H|H], (subset_dec s2 s1) as [H0|H0].
  intuition.
  1-3: right; intro H1; intuition.
Defined.

(* Gets the first equivalent state from a list l *)
Fixpoint get_set (s:ListSet) l :=
  match l with
  | s'::l =>
    if equiv_sets_dec s' s then
      s'
    else
      get_set s l
  | nil => s
  end.

(* get_set returns an equivalent state *)
Lemma get_set_equiv s s' l :
  get_set s l = s' ->
  equiv_sets s s'.
Proof.
  intro H.
  induction l as [|x l IH];
  simpl in H.
  subst; apply equiv_sets_self.
  destruct (equiv_sets_dec x s) as [H0|H0].
  subst; apply equiv_sets_comm.
  1,2: intuition.
Qed.

(* Getting equivalent sets from a list that has one of them returns the same set *)
Lemma get_equiv_sets s s' l :
  In s l \/ In s' l ->
  equiv_sets (get_set s l) (get_set s' l) ->
  get_set s l = get_set s' l.
Proof.
  intros H H0.
  assert (equiv_sets s s'). {
    remember (get_set s l) as s1 eqn:H1;
    symmetry in H1; apply get_set_equiv in H1.
    remember (get_set s' l) as s2 eqn:H2;
    symmetry in H2; apply get_set_equiv in H2.
    apply equiv_sets_trans with s2.
    2: apply equiv_sets_comm; intuition.
    apply equiv_sets_trans with s1; intuition.
  }
  clear H0.
  induction l as [|x l IH];
  simpl; simpl in H, H1.
  destruct H; contradiction.
  destruct (equiv_sets_dec x s) as [H2|H2];
  destruct (equiv_sets_dec x s') as [H3|H3].
  intuition.
  - assert (False).
    apply H3, equiv_sets_trans with s.
    1-3: intuition.
  - assert (False).
    apply H2, equiv_sets_trans with s'.
    2: apply equiv_sets_comm.
    1-3: intuition.
  - destruct H; destruct H; subst.
    contradiction.
    1,3: apply IH; intuition.
    apply equiv_sets_comm in H1; contradiction.
Qed.

End ListSets.