Lemma transf_program_match : forall p tp, transf_program p = OK tp -> match_prog p tp .
Proof.
   intros p tp H. custom46 match_transform_partial_program.
Qed.
Remark diff_same : forall s, diff s s = nil .
Proof.
   induction s as [ | [ v i ] s ].
    - custom21.
    - simpl. rewrite Pos.compare_refl. custom35 dec_eq_true.
Qed.
Remark delta_state_same : forall s, delta_state s s = ( nil, nil ) .
Proof.
   destruct s as [  a | ].
    - simpl. rewrite ! diff_same. auto.
    - custom21.
Qed.
Lemma transf_code_match : forall lm c before, match_code c ( transf_code lm before c ) .
Proof.
   intros lm. destruct c as [  | c i ].
    - intros before. custom62.
    - intros before. simpl. assert ( DEFAULT : forall before after, match_code ( i :: c ) ( i :: add_delta_ranges before after ( transf_code lm after c ) ) ).
      -- intros before0 after. custom55 REC.
      -- custom10 i DEFAULT m t z s l o m0 a s0 b e l0 c0.
        --- auto.
        --- custom70 c DEFAULT i. custom10 i DEFAULT m t z s l0 o m0 a s0 b e l1 c0.
          ---- set ( after := get_label l0 lm ). set ( c1 := Llabel l0 :: add_delta_ranges before after ( transf_code lm after c ) ). replace c1 with ( add_delta_ranges before before c1 ).
            ----- constructor. custom55 REC.
            ----- unfold add_delta_ranges. custom35 delta_state_same.
          ---- auto.
Qed.
Lemma transf_function_match : forall f tf, transf_function f = OK tf -> match_function f tf .
Proof.
   unfold transf_function. intros f tf H. destruct ( ana_function f ) as [ lm| ].
    - inv H. custom55 transf_code_match.
    - inv H.
Qed.
Remark find_label_add_delta_ranges : forall lbl c before after, find_label lbl ( add_delta_ranges before after c ) = find_label lbl c .
Proof.
   intros lbl c before after. custom28 add_delta_ranges before after killed.
    - custom21.
    - induction born as [ | [ v i ] l ].
      -- custom21.
      -- custom21.
Qed.
Lemma find_label_match_rec : forall lbl c' c tc, match_code c tc -> find_label lbl c = Some c' -> exists before after tc', find_label lbl tc = Some ( add_delta_ranges before after tc' ) /\ match_code c' tc' .
Proof.
   custom57.
    - custom15 H0. destruct ( is_label lbl i ) as [  H0 | H0 ].
      -- inv H0. econstructor. econstructor. custom49.
      -- custom35 find_label_add_delta_ranges.
    - discriminate.
Qed.
Lemma find_label_match : forall f tf lbl c, match_function f tf -> find_label lbl f. ( fn_code ) = Some c -> exists before after tc, find_label lbl tf. ( fn_code ) = Some ( add_delta_ranges before after tc ) /\ match_code c tc .
Proof.
   intros f tf lbl c H H0. inv H. custom66.
Qed.
Lemma set_state_1 : forall v i s, In ( v, i ) ( set_state v i s ) .
Proof.
   induction s as [ | [ v' i' ] s ].
    - custom21.
    - simpl. destruct ( Pos.compare v v' ) as [  | | ].
      -- custom21.
      -- custom21.
      -- custom21.
Qed.
Lemma set_state_2 : forall v i v' i' s, v' <> v -> In ( v', i' ) s -> In ( v', i' ) ( set_state v i s ) .
Proof.
   induction s as [ | [ v1 i1 ] s ].
    - .
    - custom13 H H0 v v1 H1. simpl. custom52 H0. custom38 H H0. contradiction.
Qed.
Lemma set_state_3 : forall v i v' i' s, wf_avail s -> In ( v', i' ) ( set_state v i s ) -> ( v' = v /\ i' = i ) \/ ( v' <> v /\ In ( v', i' ) s ) .
Proof.
   custom57.
    - custom11 H1 v v0 H2.
      -- custom51 H1.
        --- right. custom24 not_eq_sym. custom30 Plt_ne.
        --- custom19 not_eq_sym Plt_ne Plt_trans v0.
      -- custom51 H1.
        --- auto.
        --- custom14 not_eq_sym Plt_ne. custom46 H.
      -- auto.
      -- destruct IHwf_avail as [ A | [ A B ] ].
        --- auto.
        --- auto.
        --- auto.
      -- right. custom64.
    - intuition congruence.
Qed.
Lemma wf_set_state : forall v i s, wf_avail s -> wf_avail ( set_state v i s ) .
Proof.
   custom32.
    - custom37 v v0 H1.
      -- subst v0. custom8.
      -- constructor.
        --- red. simpl. intros v' i' H2. custom71 H2.
          ---- auto.
          ---- custom44 Plt_trans v0.
        --- custom8.
      -- exploit set_state_3.
        --- eexact H0.
        --- eauto.
        --- intros [ [ A B ] | [ A B ] ].
          ---- subst. eauto.
          ---- eauto.
    - red. custom60.
    - constructor.
Qed.
Lemma remove_state_1 : forall v i s, wf_avail s -> ~ In ( v, i ) ( remove_state v s ) .
Proof.
   induction 1.
    - custom61. intros H. auto.
    - custom61. intros H1. destruct ( Pos.compare_spec v v0 ) as [  H2 H1 | H2 H1 | H2 H1 ].
      -- subst v0. custom67 v.
      -- custom31 H1 v. elim ( Plt_strict v ). custom44 Plt_trans v0.
      -- custom71 H1.
        --- custom67 v.
        --- tauto.
Qed.
Lemma remove_state_2 : forall v v' i' s, v' <> v -> In ( v', i' ) s -> In ( v', i' ) ( remove_state v s ) .
Proof.
   induction s as [ | [ v1 i1 ] s ].
    - .
    - custom13 H H0 v v1 H1. custom52 H0. custom59.
Qed.
Lemma remove_state_3 : forall v v' i' s, wf_avail s -> In ( v', i' ) ( remove_state v s ) -> v' <> v /\ In ( v', i' ) s .
Proof.
   custom57.
    - custom11 H1 v v0 H2.
      -- custom19 not_eq_sym Plt_ne Plt_trans v0.
      -- custom14 not_eq_sym Plt_ne. eauto.
      -- custom24 not_eq_sym. apply Plt_ne. eauto.
      -- destruct IHwf_avail as [ A B ].
        --- auto.
        --- auto.
      -- custom64.
    - contradiction.
Qed.
Lemma wf_remove_state : forall v s, wf_avail s -> wf_avail ( remove_state v s ) .
Proof.
   custom32. custom37 v v0 H1.
    - auto.
    - custom8.
    - exploit remove_state_3.
      -- eexact H0.
      -- eauto.
      -- intros [ A B ]. eauto.
Qed.
Lemma wf_filter : forall pred s, wf_avail s -> wf_avail ( List.filter pred s ) .
Proof.
   custom32. simpl. destruct ( pred ( v, i ) ) eqn : P.
    - custom18 v' i' H1. apply filter_In in H1. destruct H1 as [  H2 H1 ]. eauto.
    - auto.
Qed.
Lemma join_1 : forall v i s1, wf_avail s1 -> forall s2, wf_avail s2 -> In ( v, i ) s1 -> In ( v, i ) s2 -> In ( v, i ) ( join s1 s2 ) .
Proof.
   custom27.
    - custom59.
    - custom38 I1 I2. destruct I1, I2 as [  H4 H3 | H4 H3 | H4 H3 | H4 H3 ].
      -- inv H3. inv H4. rewrite Pos.compare_refl. rewrite dec_eq_true. auto with coqlib.
      -- inv H3. assert ( L : Plt v1 v ) by eauto. apply Pos.compare_gt_iff in L. custom35 L.
      -- inv H4. assert ( L : Plt v0 v ) by eauto. apply Pos.compare_lt_iff in L. rewrite L. custom47 IHwf_avail. auto.
      -- destruct ( Pos.compare v0 v1 ) as [  | | ].
        --- destruct ( eq_debuginfo i0 i1 ) as [  e | n ].
          ---- auto with coqlib.
          ---- auto with coqlib.
        --- custom63 IHwf_avail.
          ---- auto with coqlib.
          ---- auto with coqlib.
        --- eauto.
Qed.
Lemma join_2 : forall v i s1, wf_avail s1 -> forall s2, wf_avail s2 -> In ( v, i ) ( join s1 s2 ) -> In ( v, i ) s1 /\ In ( v, i ) s2 .
Proof.
   custom27.
    - custom15 I. try tauto.
    - custom15 I. destruct ( Pos.compare_spec v0 v1 ) as [  H3 I | H3 I | H3 I ].
      -- subst v1. destruct ( eq_debuginfo i0 i1 ) as [  I e | I n ].
        --- subst i1. custom70 I H3. custom29 IHwf_avail.
        --- custom29 IHwf_avail.
      -- exploit ( IHwf_avail ( ( v1, i1 ) :: s0 ) ).
        --- custom8.
        --- eauto.
        --- custom60.
      -- exploit IHwf_avail0.
        --- eauto.
        --- tauto.
Qed.
Lemma wf_join : forall s1, wf_avail s1 -> forall s2, wf_avail s2 -> wf_avail ( join s1 s2 ) .
Proof.
   induction 1.
    - custom40. try constructor.
    - custom40. destruct ( Pos.compare_spec v v0 ) as [  H3 | H3 | H3 ].
      -- subst v0. destruct ( eq_debuginfo i i0 ) as [  e | n ].
        --- custom18 v' i' H3. apply join_2 in H3.
          ---- destruct H3 as [  H4 H3 ]. eauto.
          ---- auto.
          ---- auto.
        --- auto.
      -- custom63 IHwf_avail.
      -- apply IHwf_avail0.
Qed.
Lemma symbols_preserved : forall ( s : ident ), Genv.find_symbol tge s = Genv.find_symbol ge s .
Proof.
   intros s. apply ( Genv.find_symbol_match TRANSF ).
Qed.
Lemma functions_translated : forall ( v : val ) ( f : fundef ), Genv.find_funct ge v = Some f -> exists tf, Genv.find_funct tge v = Some tf /\ transf_fundef f = OK tf .
Proof.
   custom50 v f H Genv.find_funct_transf_partial TRANSF.
Qed.
Lemma function_ptr_translated : forall ( b : block ) ( f : fundef ), Genv.find_funct_ptr ge b = Some f -> exists tf, Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = OK tf .
Proof.
   custom50 b f H Genv.find_funct_ptr_transf_partial TRANSF.
Qed.
Lemma sig_preserved : forall f tf, transf_fundef f = OK tf -> funsig tf = funsig f .
Proof.
   unfold transf_fundef, transf_partial_fundef. intros f tf H. destruct f as [  H f | H e ].
    - monadInv H. exploit transf_function_match.
      -- eauto.
      -- intros M. inv M. auto.
    - inv H. reflexivity.
Qed.
Lemma find_function_translated : forall ros ls f, find_function ge ros ls = Some f -> exists tf, find_function tge ros ls = Some tf /\ transf_fundef f = OK tf .
Proof.
   unfold find_function. intros ros ls f H. destruct ros as [  H m | H i ].
    - custom30 functions_translated.
    - rewrite symbols_preserved. destruct ( Genv.find_symbol ge i ) as [  H b | H ].
      -- custom30 function_ptr_translated.
      -- congruence.
Qed.
Lemma can_eval_safe_arg : forall ( rs : locset ) sp m ( a : builtin_arg loc ), safe_builtin_arg a -> exists v, eval_builtin_arg tge rs sp m a v .
Proof.
   induction a.
    - custom33. custom34. custom42. custom43. custom53. custom54. custom68. custom69.
    - .
    - .
    - .
    - custom15 H. try ( econstructor ; now eauto with barg ).
    - .
    - .
    - .
    - .
    - custom15 H. destruct H as [ S1 S2 ]. destruct ( IHa1 S1 ) as [ v1 E1 ]. destruct ( IHa2 S2 ) as [ v2 E2 ]. exists ( Val.longofwords v1 v2 ). auto with barg.
    - custom15 H. try contradiction.
Qed.
Lemma eval_add_delta_ranges : forall s f sp c rs m before after, star step tge ( State s f sp ( add_delta_ranges before after c ) rs m ) E0 ( State s f sp c rs m ) .
Proof.
   intros s f sp c rs m before after. custom28 add_delta_ranges before after killed.
    - simpl. custom48 star_step.
      -- eauto.
      -- constructor.
      -- custom62.
      -- custom21.
    - induction born as [ | [ v i ] l ].
      -- simpl. apply star_refl.
      -- simpl. destruct i as [ a SAFE ]. simpl. exploit can_eval_safe_arg.
        --- eauto.
        --- intros [ v1 E1 ]. custom16 star_step.
          ---- eexact E1.
          ---- constructor.
Qed.
Lemma parent_locset_match : forall s ts, list_forall2 match_stackframes s ts -> parent_locset ts = parent_locset s .
Proof.
   induction 1.
    - custom21.
    - simpl. inv H. auto.
Qed.
Theorem transf_step_correct : forall s1 t s2, step ge s1 t s2 -> forall ts1 ( MS : match_states s1 ts1 ), exists ts2, plus step tge ts1 t ts2 /\ match_states s2 ts2 .
Proof.
   induction 1.
    - custom9 ts1 MS TRC. custom0 plus_left eval_add_delta_ranges. custom41.
    - custom9 ts1 MS TRC. custom1 plus_left eval_add_delta_ranges. custom41.
    - custom9 ts1 MS TRC. custom2 plus_left eval_add_delta_ranges. econstructor.
      -- instantiate ( 1 := v ). custom36 H eval_operation_preserved.
      -- eauto.
    - custom9 ts1 MS TRC. custom3 plus_left eval_add_delta_ranges. custom22 exec_Lload a H eval_addressing_preserved.
    - custom9 ts1 MS TRC. custom4 plus_left eval_add_delta_ranges. eapply exec_Lstore with ( a := a ).
      -- custom36 H eval_addressing_preserved.
      -- eauto.
      -- eauto.
    - custom9 ts1 MS TRC. custom45 tf' A B. custom23 plus_one.
      -- custom56. custom56. custom8.
      -- econstructor.
        --- eexact A.
        --- custom58.
    - custom9 ts1 MS TRC. custom45 tf' A B. exploit parent_locset_match.
      -- eauto.
      -- intros PLS. custom23 plus_one.
        --- rewrite PLS. custom8.
        --- custom49.
          ---- rewrite PLS. eexact A.
          ---- custom58.
          ---- custom72 TRF. custom9 ts1 MS TRC. custom5 plus_left eval_add_delta_ranges.
            ----- custom25 external_call_symbols_preserved senv_preserved. eapply eval_builtin_args_preserved with ( ge1 := ge ).
              ------ exact symbols_preserved.
              ------ eauto.
            ----- traceEq.
    - .
    - custom9 ts1 MS TRC. custom6 plus_left eval_add_delta_ranges.
      -- constructor.
      -- traceEq.
    - custom7 ts1 MS TRC before' after' tc' A B plus_left eval_add_delta_ranges.
      -- constructor. eauto.
      -- traceEq.
    - custom26 before' after' tc' A B. custom12 plus_left eval_add_delta_ranges.
      -- custom66. eauto.
      -- traceEq.
    - custom9 ts1 MS TRC. custom17 plus_left eval_add_delta_ranges.
      -- eapply exec_Lcond_false.
        --- auto.
        --- auto.
      -- traceEq.
    - custom9 ts1 MS TRC. exploit find_label_match.
      -- eauto.
      -- eauto.
      -- intros ( before' & after' & tc' & A & B ). custom20 plus_left eval_add_delta_ranges.
        --- reflexivity.
        --- eauto.
        --- eauto.
        --- eauto.
        --- eauto.
    - custom9 ts1 MS TRC. custom23 plus_one.
      -- .
      -- constructor. custom72 TRF. rewrite ( parent_locset_match _ _ STACKS ). custom41.
    - custom39 ts1 MS H7. rename x into tf. assert ( MF : match_function f tf ) by ( apply transf_function_match ; auto ). inversion MF. custom23 plus_one.
      -- custom65.
      -- constructor.
        --- simpl. eauto.
        --- reflexivity.
    - custom39 ts1 MS H8. custom23 plus_one.
      -- custom41.
      -- custom49.
        --- eapply external_call_symbols_preserved.
          ---- apply senv_preserved.
          ---- eauto.
        --- eauto.
    - intros ts1 MS. inv MS. inv H3. inv H1. econstructor. split.
      -- custom48 plus_left. apply eval_add_delta_ranges.
      -- custom8. auto.
Qed.
Lemma transf_initial_states : forall st1, initial_state prog st1 -> exists st2, initial_state tprog st2 /\ match_states st1 st2 .
Proof.
   intros st1 H. inversion H. exploit function_ptr_translated.
    - eauto.
    - intros [ tf [ A B ] ]. exists ( Callstate nil tf ( Locmap.init Vundef ) m0 ). split.
      -- econstructor.
        --- eapply ( Genv.init_mem_transf_partial TRANSF ). eauto.
        --- rewrite ( match_program_main TRANSF ), symbols_preserved. auto.
        --- eauto.
        --- rewrite <- H3. custom30 sig_preserved.
      -- custom56. constructor.
Qed.
Lemma transf_final_states : forall st1 st2 r, match_states st1 st2 -> final_state st1 r -> final_state st2 r .
Proof.
   intros st1 st2 r H H0. inv H0. inv H. inv H5. custom49.
Qed.
Theorem transf_program_correct : forward_simulation ( semantics prog ) ( semantics tprog ) .
Proof.
   eapply forward_simulation_plus.
    - apply senv_preserved.
    - eexact transf_initial_states.
    - eexact transf_final_states.
    - eexact transf_step_correct.
Qed.
Current Working Directory: /Users/maxxin-admin/Documents/school/projects/dream-prover/dream-prover
writing to src/resources/compression-eval/CompCert-compressed/enumerate/greedy/Debugvarproof/csv/Debugvarproof-1.00.csv
extracted tactics -----------
Ltac custom0 H0 H1 :=  econstructor; [split; [eapply H0; [ | apply H1 | traceEq | .. ] | constructor; [auto | auto | auto | .. ] | .. ] | .. ].
Ltac custom1 H0 H1 :=  econstructor; [split; [eapply H0; [ | apply H1 | traceEq | .. ] | constructor; [auto | auto | auto | .. ] | .. ] | .. ].
Ltac custom2 H0 H1 :=  econstructor; [split; [eapply H0; [ | apply H1 | traceEq | .. ] | constructor; [auto | auto | auto | .. ] | .. ] | .. ].
Ltac custom3 H0 H1 :=  econstructor; [split; [eapply H0; [ | apply H1 | traceEq | .. ] | constructor; [auto | auto | auto | .. ] | .. ] | .. ].
Ltac custom4 H0 H1 :=  econstructor; [split; [eapply H0; [ | apply H1 | traceEq | .. ] | constructor; [auto | auto | auto | .. ] | .. ] | .. ].
Ltac custom5 H0 H1 :=  econstructor; [split; [eapply H0; [ | apply H1 |  | .. ] | constructor; [auto | auto | auto | .. ] | .. ] | .. ].
Ltac custom6 H0 H1 :=  econstructor; [split; [eapply H0; [ | apply H1 |  | .. ] | constructor; [auto | auto | auto | .. ] | .. ] | .. ].
Ltac custom7 H0 H1 H2 H14 H15 H16 H17 H18 H19 H20 :=  intros H0 H1; [inv H1; [try ( inv H2 ); [exploit find_label_match; [eauto | eauto | intros ( H14 & H15 & H16 & H17 & H18 ); [econstructor; [split; [eapply H19; [ | apply H20 |  | .. ] | constructor; [auto | auto | auto | .. ] | .. ] | .. ] | .. ] | .. ] | .. ] | .. ] | .. ].
Ltac custom8  :=  constructor; [auto | auto | .. ].
Ltac custom9 H0 H1 H2 :=  intros H0 H1; [inv H1; [try ( inv H2 ) | .. ] | .. ].
Ltac custom10 H0 :=  destruct H0; [auto | auto | auto | auto | auto | auto | auto | auto |  |  | auto | auto | auto | .. ].
Ltac custom11 H0 H1 H2 H14 H12 H17 H16 H19 H21 H25 :=  simpl; [intros H0; [destruct ( Pos.compare_spec H1 H2 ); [ | simpl in H14; [simpl in H12; [destruct H17; [inv H19 |  | .. ] | .. ] | .. ] | simpl in H16; [subst H2]destruct H21; [inv H25 |  | .. ] | .. ] | .. ] | .. ].
Ltac custom12 H0 H7 :=  econstructor; [split; [eapply H0; [ | apply H7 |  | .. ] | custom8 ; [auto | .. ] | .. ] | .. ].
Ltac custom13 H0 H1 H2 H3 :=  simpl; [intros H0 H1; [destruct ( Pos.compare_spec H2 H3 ); [subst H3; [auto] | simpl | simpl; [destruct H1; [auto | auto | .. ] | .. ] | .. ] | .. ] | .. ].
Ltac custom14 H0 H7 :=  split; [apply H0; [apply H7 | .. ] | auto | .. ].
Ltac custom15 H0 :=  simpl; [intros H0 | .. ].
Ltac custom16 H0 :=  eapply H0; [econstructor; [constructor; [ |  | .. ] | simpl; [constructor | .. ] | simpl; [auto | .. ] | .. ] | eauto | traceEq | .. ].
Ltac custom17 H6 H10 :=  econstructor; [split; [eapply H6; [ | apply H10 |  | .. ] | custom8 ; [auto | .. ] | .. ] | .. ].
Ltac custom18 H4 H5 H6 :=  constructor; [red; [intros H4 H5 H6 | .. ] | auto | .. ].
Ltac custom19 H6 H7 H8 H3 :=  split; [apply H6; [apply H7; [apply H8 with H3; [eauto | eauto | .. ] | .. ] | .. ] | auto | .. ].
Ltac custom20 H6 H10 :=  econstructor; [split; [eapply H6; [econstructor; [ |  |  |  | .. ] | apply H10 |  | .. ] | custom8 ; [auto | .. ] | .. ] | .. ].
Ltac custom21  :=  simpl; [auto | .. ].
Ltac custom22 H0 H1 H2 H10 :=  eapply H0 with ( H1 := H1 ); [rewrite <- H2; [apply H10; [exact symbols_preserved | .. ] | .. ] | eauto | eauto | .. ].
Ltac custom23 H0 :=  econstructor; [split; [apply H0 |  | .. ] | .. ].
Ltac custom24 H3 :=  split; [apply H3 | auto | .. ].
Ltac custom25 H0 H4 :=  econstructor; [ | eapply H0; [apply H4 | eauto | .. ] | eauto | .. ].
Ltac custom26 H12 H13 H14 H15 H16 :=  custom9 ; [exploit find_label_match; [eauto | eauto | intros ( H12 & H13 & H14 & H15 & H16 ) | .. ] | .. ].
Ltac custom27  :=  induction 1; [simpl; [try tauto | .. ] | simpl; [induction 1; [ |  | .. ] | .. ] | .. ].
Ltac custom28 H0 H1 H2 H6 :=  unfold H0; [destruct ( delta_state H1 H2 ) as [ killed born ]; [induction H6 as [ | [ v i ] l ]; [simpl |  | .. ] | .. ] | .. ].
Ltac custom29 H0 :=  exploit H0; [eauto | eauto | tauto | .. ].
Ltac custom30 H0 :=  apply H0; [auto | .. ].
Ltac custom31 H0 H7 H5 :=  destruct H0; [elim ( Plt_strict H7 ); [inv H5; [eauto] | .. ] |  | .. ].
Ltac custom32  :=  induction 1; [simpl; [constructor; [ |  | .. ] | .. ] |  | .. ].
Ltac custom33  :=  custom15 ; [try ( econstructor ; now eauto with barg ) | .. ].
Ltac custom34  :=  custom15 ; [try contradiction | .. ].
Ltac custom35 H0 :=  rewrite H0; [auto | .. ].
Ltac custom36 H0 H1 :=  rewrite <- H0; [apply H1; [exact symbols_preserved | .. ] | .. ].
Ltac custom37 H0 H1 :=  simpl; [destruct ( Pos.compare_spec H0 H1 ); [ |  | custom18  | .. ] | .. ].
Ltac custom38 H0 H1 :=  simpl; [intros H0 H1 | .. ].
Ltac custom39 H0 H1 H2 :=  intros H0 H1; [inv H1; [monadInv H2 | .. ] | .. ].
Ltac custom40  :=  simpl; [induction 1; [try constructor |  | .. ] | .. ].
Ltac custom41  :=  constructor; [auto | .. ].
Ltac custom42  :=  custom15 ; [try ( econstructor ; now eauto with barg ) | .. ].
Ltac custom43  :=  custom15 ; [try contradiction | .. ].
Ltac custom44 H0 H1 :=  apply H0 with H1; [eauto | eauto | .. ].
Ltac custom45 H2 H3 H4 :=  exploit find_function_translated; [eauto | intros ( H2 & H3 & H4 ) | .. ].
Ltac custom46 H0 :=  eapply H0; [eauto | .. ].
Ltac custom47 H0 :=  apply H0; [custom8  |  | auto with coqlib | .. ].
Ltac custom48 H0 :=  eapply H0; [econstructor; [ |  |  | .. ] |  | traceEq | .. ].
Ltac custom49  :=  econstructor; [eauto | .. ].
Ltac custom50 H0 H1 H2 H3 H4 :=  intros H0 H1 H2; [apply ( H3 H4 ); [auto | .. ] | .. ].
Ltac custom51 H0 H10 :=  destruct H0; [inv H10 | right | .. ].
Ltac custom52 H0 :=  destruct H0; [congruence | auto | .. ].
Ltac custom53  :=  custom15 ; [try ( econstructor ; now eauto with barg ) | .. ].
Ltac custom54  :=  custom15 ; [try contradiction | .. ].
Ltac custom55 H0 :=  constructor; [apply H0 | .. ].
Ltac custom56  :=  constructor; [ | auto | .. ].
Ltac custom57  :=  induction 1; [custom15  |  | .. ].
Ltac custom58  :=  symmetry; [custom30  | .. ].
Ltac custom59  :=  custom38 ; [auto | .. ].
Ltac custom60  :=  simpl; [tauto | .. ].
Ltac custom61  :=  simpl; [red | .. ].
Ltac custom62  :=  simpl; [constructor | .. ].
Ltac custom63 H0 :=  apply H0; [custom8  |  |  | .. ].
Ltac custom64  :=  custom24 ; [auto | .. ].
Ltac custom65  :=  custom8 ; [auto | .. ].
Ltac custom66  :=  custom46 ; [eauto | .. ].
Ltac custom67 H0 :=  elim ( Plt_strict H0 ); [eauto | .. ].
Ltac custom68  :=  custom15 ; [try ( econstructor ; now eauto with barg ) | .. ].
Ltac custom69  :=  custom15 ; [try contradiction | .. ].
Ltac custom70 H0 :=  destruct H0; [auto |  | .. ].
Ltac custom71 H0 H7 :=  destruct H0; [inv H7 |  | .. ].
Ltac custom72 H0 :=  inv H0; [eauto | .. ].
