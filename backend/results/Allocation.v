Ltac custom0 H0 H1 H2 H3 H4 H5 H7 H11 H9 H13 H16 H15 H31 H32 :=  unfold H0; [intros H1 H2 H3 H4 H5; [destruct H4; [destruct H5; [left; [eapply H16; [eauto | eauto | .. ] | .. ] | destruct H9; [rewrite <- H13; [auto | .. ] | .. ] | .. ] | destruct H7; [rewrite H11; [destruct H5; [auto | destruct H15; [right; [split; [auto | intuition; [left; [eapply H31; [eauto | eauto | .. ] | .. ] | left; [congruence | .. ] | left; [congruence | .. ] | right; [split; [congruence | eapply H32; [eauto | eauto | .. ] | .. ] | .. ] | .. ] | .. ] | .. ] | .. ] | .. ] | .. ] | .. ] | .. ] | .. ] | .. ].
Ltac custom1 H0 :=  apply H0; [red; [auto | .. ] | .. ].
Ltac custom2 H0 H1 H2 H3 H4 H11 H12 H13 :=  unfold H0, H1, H2; [intros H3 H4; [destruct H3; [destruct H4; [intros H11 H12; [apply H13 | .. ] | auto | .. ] | destruct H4; [auto | auto | .. ] | .. ] | .. ] | .. ].
Ltac custom3 H0 H1 H2 H3 H4 H5 :=  unfold H0, H1; [intros H2 H3 H4; [red; [intros H5; [subst H3; [intuition; [ |  | eelim OrderedEqKind.lt_not_eq; [eauto | red; [auto | .. ] | .. ] | .. ] | .. ] | .. ] | .. ] | .. ] | .. ].
Ltac custom4  :=  destruct y; [simpl; [congruence | .. ] | simpl; [congruence | .. ] | simpl; [congruence | .. ] | .. ].
Ltac custom5 H0 H1 H8 :=  destruct ( OrderedEqKind.compare ( ekind H0 ) ( ekind H1 ) ); [custom1  | apply H8; [red; [destruct H0; [destruct H1; [congruence | .. ] | .. ] | .. ] | .. ] | custom1  | .. ].
Ltac custom6 H0 H1 H2 :=  intros H0 H1 H2; [destruct H0; [destruct H1; [ |  | .. ] | destruct H1; [ | auto | .. ] | .. ] | .. ].
Ltac custom7  :=  destruct y; [simpl; [congruence | .. ] | simpl; [congruence | .. ] | simpl; [congruence | .. ] | .. ].
Ltac custom8 H3 H4 H2 H0 H9 :=  Next Obligation; [split; [intros H3; [destruct ( OrderedEquation'.eq_dec H2 H0 ); [ | apply H9 | .. ] | .. ] | intros H4; [destruct ( OrderedEquation.eq_dec H2 H0 ); [ |  | .. ] | .. ] | .. ] | .. ].
Ltac custom9 H0 :=  apply H0; [auto | .. ].
Ltac custom10 H0 H1 H2 H3 :=  apply ( H0 H1 ); [apply H2 with H3; [auto |  | .. ] | .. ].
Ltac custom11  :=  eelim OrderedLoc.lt_not_eq; [eauto | red; [auto | .. ] | .. ].
Ltac custom12 H0 H1 H2 H3 H4 :=  intros H0 H1 H2 H3 H4; [destruct H0; [destruct H1; [ | try contradiction | .. ] |  | .. ] | .. ].
Ltac custom13 H1 :=  Next Obligation; [split; [intros H1 |  | .. ] | .. ].
Ltac custom14 H0 :=  unfold H0; [auto | .. ].
Ltac custom15 H0 H1 :=  red; [intros H0; [rewrite H1 | .. ] | .. ].
Ltac custom16 H0 H1 :=  destruct ( OrderedPositive.compare ( ereg H0 ) ( ereg H1 ) ); [custom1  |  | custom1  | .. ].
Ltac custom17 H0 H1 :=  destruct ( OrderedLoc.compare ( eloc H0 ) ( eloc H1 ) ); [custom1  |  | custom1  | .. ].
Ltac custom18  :=  simpl; [congruence | .. ].
Ltac custom19 H0 :=  red in H0; [custom5 ].
Ltac custom20 H0 :=  red in H0; [custom19 ].
Ltac custom21 H0 :=  red in H0; [custom20 ].
Ltac custom22 H0 :=  red in H0; [custom15 ].
Ltac custom23 H0 H1 :=  Definition compare : forall x y : t, Compare lt eq x y; [intros H0 H1 | .. ].
Ltac custom24  :=  custom10 ; [auto | .. ].
Ltac custom25 H0 :=  rewrite H0; [auto | .. ].
Ltac custom26 H0 H1 H2 :=  apply H0 in H1; [destruct H2; [ |  | .. ] | .. ].
Ltac custom27  :=  eelim Plt_strict; [eauto | .. ].
Ltac custom28 H0 H1 H2 H3 H4 H5 :=  unfold H0; [intros H1 H2 H3 H4 H5 | .. ].
Ltac custom29 H0 :=  intros H0; [destruct H0; [ |  | .. ] | .. ].
Ltac custom30 H0 H1 :=  rewrite H0 in H1; [custom9 ].
Ltac custom31 H0 H1 :=  rewrite <- H0 in H1; [custom9 ].
Ltac custom32  :=  custom6 ; [ | auto |  | .. ].

Lemma index_inj : forall x y, index x = index y -> x = y .
Proof.
   destruct x as [  | | ].
    - custom4.
    - custom7.
    - destruct y as [  | | ].
      -- custom18.
      -- custom18.
      -- custom18.
Qed.
Lemma eq_refl : forall x : t, eq x x .
Proof.
   custom14 eq.
Qed.
Lemma eq_sym : forall x y : t, eq x y -> eq y x .
Proof.
   custom14 eq.
Qed.
Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z .
Proof.
   custom28 eq x y z H H0. rewrite H. exact H0.
Qed.
Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z .
Proof.
   custom0 lt x y z H H0 H1 Plt_trans H2 OrderedLoc.lt_trans OrderedEqKind.lt_trans.
Qed.
Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y .
Proof.
   custom3 lt eq x y H H0.
    - custom27.
    - custom11.
Qed.
custom23
Proof.
   custom16 x y l e. custom17 x y l e0. custom21 e1.
Qed.
Definition eq_dec ( x y : t ) : { x = y } + { x <> y } .
Proof.
   decide equality.
    - apply Loc.eq.
    - apply peq.
    - apply IndexedEqKind.eq.
Qed.
Lemma eq_refl : forall x : t, eq x x .
Proof.
   custom14 eq.
Qed.
Lemma eq_sym : forall x y : t, eq x y -> eq y x .
Proof.
   custom14 eq.
Qed.
Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z .
Proof.
   custom28 eq x y z H H0. custom25 H.
Qed.
Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z .
Proof.
   custom0 lt x y z H H0 H1 OrderedLoc.lt_trans H2 Plt_trans OrderedEqKind.lt_trans.
Qed.
Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y .
Proof.
   custom3 lt eq x y H H0.
    - custom11.
    - custom27.
Qed.
custom23
Proof.
   custom17 x y l e. custom16 x y l e0. custom21 e1.
Qed.
custom13
Proof.
   intros H.
    - eelim EqSet.empty_1. eauto.
    - ...
    - . eelim EqSet2.empty_1.
Qed.
custom8
Proof.
   apply EqSet2.add_2. custom10 eqs_same e EqSet.add_3 q. auto.
Qed.
custom8
Proof.
   eelim EqSet2.remove_1.
    - eauto.
    - eauto.
    - ...
    - . auto. eelim EqSet.remove_1.
    - eauto.
    - ...
    - . custom9 EqSet2.remove_2.
Qed.
Lemma eq_refl : forall x, eq x x .
Proof.
   custom29 x e.
    - simpl. red. tauto.
    - simpl. auto.
Qed.
Lemma eq_sym : forall x y, eq x y -> eq y x .
Proof.
   unfold eq. custom32.
    - custom22 H. tauto.
    - auto.
Qed.
Lemma eq_trans : forall x y z, eq x y -> eq y z -> eq x z .
Proof.
   unfold eq. custom12 x y z H H0 e e0.
    - destruct y as [  H0 H e0 | H0 H e0 ].
      -- try contradiction.
      -- destruct z as [  H0 e1 | H0 e1 ].
        --- auto.
        --- auto.
    - destruct z as [  H0 e1 | H0 e1 ].
      -- red in H0. custom22 H. auto.
      -- auto.
Qed.
Lemma beq_correct : forall x y, beq x y = true -> eq x y .
Proof.
   unfold beq, eq. custom6 x y H e e0.
    - custom9 EqSet.equal_2.
    - discriminate.
    - discriminate.
Qed.
Lemma ge_refl : forall x y, eq x y -> ge x y .
Proof.
   unfold eq, ge, EqSet.Equal, EqSet.Subset. custom32.
    - intros a H0. custom25 H.
    - auto.
Qed.
Lemma ge_trans : forall x y z, ge x y -> ge y z -> ge x z .
Proof.
   unfold ge, EqSet.Subset. custom12 x y z H H0 e e0.
    - auto.
    - destruct z as [  H0 e1 | H0 e1 ].
      -- eauto.
      -- eauto.
Qed.
Lemma ge_bot : forall x, ge x bot .
Proof.
   unfold ge, bot, EqSet.Subset. simpl. custom29 x e.
    - intros a H. elim ( EqSet.empty_1 H ).
    - auto.
Qed.
custom13
Proof.
   intros H. custom26 EqSet.union_1 H.
    - custom31 eqs_same H. custom31 eqs_same H. custom26 EqSet2.union_1 H.
      -- custom30 eqs_same H. custom30 eqs_same H.
      -- .
    - .
Qed.
Lemma ge_lub_left : forall x y, ge ( lub x y ) x .
Proof.
   custom2 lub ge EqSet.Subset x y e e0 a H EqSet.union_2. auto.
Qed.
Lemma ge_lub_right : forall x y, ge ( lub x y ) y .
Proof.
   custom2 lub ge EqSet.Subset x y e e0 a H EqSet.union_3. auto.
Qed.

