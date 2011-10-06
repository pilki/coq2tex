Require Import AST.
Require Import Memory.
(*Require Import Values.*)
Require Import Maps.
Require Import NArith.
Require Import ZArith.
Require Import List.
Require Import Program.
Require Import Coqlibext.
Require Import ArithClasses.
Require Import Integers.
Require Import Do_notation.
Open Scope Z_scope.

Lemma vect_eq_rew: forall A n (v1 v2 : vector A n), `v1 = `v2 -r> v1 = v2.
Proof. constructor. apply vect_eq. Qed.

Hint Rewrite vect_eq_rew: clean.



Record instr_id := mk_instr_id 
  { open_instr_id : ident}.

Global Instance singletonInd_instr_id : singletonInd instr_id ident :=
{ open := open_instr_id;
  mk := mk_instr_id}.
Proof.
  destruct i; auto.
  auto.
Qed.



(* The language and its semantic are parametrized by the instructions
   of the source language, for example C instructions for the source
   to source version, or Cminor ones for the complete version bound to
   Compcert*)

Module Type INSTRS(N:NUMERICAL).
  Import N.
  Existing Instance Num_num.

  Parameter val: Type.
  Parameter instruction: Type.
  Parameter context_siz: instruction -> nat.



  Parameter context_size: instruction -> nat.
  Notation "'cs'" := context_size.


  (* What locations are read by the instruction. The ident is then one
     of the array, and the matrix is the linear form that must be
     applied to the context to obtain the cell in the array. The
     context is here augmented with 1, as usual. All the location are
     read *)

  Parameter read_locs: forall i: instruction,
    list (array_id * list (vector num ( S (cs i)))).


  (* each instruction write one, and exactly one location. The initial
     idea of having potentially several location optionally written to
     allow conditional has been abandoned because it would not allow
     to add dynamic tests. The idea is that since a dynamic comparison
     of pointers can fail if one of the two pointers is not defined,
     we must make sure that every location is accessed to be able to
     add the test, so that if a pointer is not valid, the write would
     have failed in the original program.*)

  Parameter write_loc: forall i, array_id * list (vector num (S (cs i))).



  (* the semantic of the instruction is "pure", except specifically on
  the written instructions and depends only on the read values. It is
  in Prop because it is not used by the optimiser, just by the
  preservation proof. It takes the context as an input to allow
  instruction like T[i] = i;*)

  Parameter semantic: forall i, vector num (cs i) -> list val -> val -> Prop.

  (* I'm not 100% sure yet that this is needed, but it might: for the
     validator to prove that two loops programs are equivalent, it
     will lift them to the polyhedral world, and compare them
     there. Hence, it needs a complete equivalence between the loop
     form and the polyhedral form, which should need determinism of
     the semantic. *)
  Parameter deterministic_semantic:
    forall i v lv val1 val2,
      semantic i v lv val1 -> semantic i v lv val2 -> val1 = val2.

End INSTRS.

(* as for memories, we need to be able to move from instruction in int
   to instructions in Z *)

Module INSTRSI2Z (I:INSTRS(IntNum)) <: INSTRS(ZNum).
  Definition instruction := I.instruction.
  Definition val := I.val.

  (* the number of variables for the instruction. Typically, the depth
     of the instruction in the loop nest in the original program plus
     the number of parameters of the program *)

  Definition context_size:= I.context_size.
  Notation "'cs'" := context_size.

  (* What locations are read by the instruction. The ident is then one
     of the array, and the matrix is the linear form that must be
     applied to the context to obtain the cell in the array. The
     context is here augmented with 1, as usual. All the location are
     read *)

  Definition i2zidmat {p} (pair : array_id * list (ivector p)) :=
    match pair with
      | (id, l) => (id, map i2zvect l)
    end.


  Definition read_locs i :=
    map i2zidmat (I.read_locs i).

  Definition write_loc i := i2zidmat (I.write_loc i).

  Inductive sem i (zv: vector Z (cs i)) lv v : Prop :=
    | sem_intro:
      forall iv, z2ivect zv = Some iv -> I.semantic i iv lv v ->
        sem i zv lv v.
  Definition semantic := sem.


  Lemma deterministic_semantic:
    forall i v lv val1 val2,
      semantic i v lv val1 -> semantic i v lv val2 -> val1 = val2.
  Proof.
    intros * SEM1 SEM2.
    inv SEM1; inv SEM2.
    replace iv0 with iv in *; [|congruence].
    eapply I.deterministic_semantic; eauto.
  Qed.
End INSTRSI2Z.
Set Implicit Arguments.
Module Semantique (N:NUMERICAL) (M:BASEMEM(N))(I:INSTRS(N) with Definition val := M.val).
  Import N.
  Existing Instance Num_num.
  Notation "'nvector'" := (vector num).
  Notation "'cs'" := I.context_size.




  (* [stmt n] is a loop statement of depth n (counting the parameters
     of the program, but not the constant 1). I know I am going to
     regret the use of dependent type, but I don't really know how to
     to it in a better way.*)

  Inductive stmt (n: nat) :=
  (* a loop has an index going from 0 to the bound (excluded) obtained
     from the global parameters of the program and the outer
     indices. Comparison to bound is always considered signed *)

  | Loop :
    forall
      (lower_bound: list (num * (nvector (S n))))
      (upper_bound: list (num * (nvector (S n))))
      (lstep: num)
      (body: list (stmt (S n))), stmt n

  (* an instruction does not contain the actual "instr" but a label
     pointing to it. The reason is that some instructions are
     "duplicated" and we need to recognize them easily for the
     validation part.

     The length of the list of vectors must be equal to the context
     size of the instruction, but this cannot be express here, since
     we don't have the correspondence instr_iduction -> instruction. It will be
     made explicit in the semantic below *)

  | Instr: instr_id -> list (nvector (S n)) -> stmt n.


  (* a program depends on a number of parameters, and will use some arrays. *)
  Record program : Type := mkprogram  {
    nbr_params: nat;

    (* PTree.t from the module Maps of compcert is a map with
       positive keys*)
    instrs: PTree.t I.instruction;


    prog_main: list (stmt nbr_params)
  }.


  (* semantic of loops statements and programs *)
  Section RELSEM.

    (* the environment is the values of the indices *)
    Definition env := nvector.

    Parameter prog: program.

    (* Continuation. We have a [cont n] when we are executing a stmt n *)

    Inductive cont: nat ->  Type :=
    | Kstop: forall {n}, cont n
    | Kseq: forall {n}, stmt n -> cont n -> cont n
    | Kloop {n} (lower_bound upper_bound: list (num * (nvector (S n)))) (lstep: num) :
      list (stmt (S n)) -> cont n -> cont (S n).

    Fixpoint add_stmts {n} (sl: list (stmt n)) (k: cont n) :=
      match sl with
        | nil => k
        | s :: ss => Kseq s (add_stmts ss k)
      end.

    (* since our language is easier (only one kind of state (no
       function call), no skip stmt, no branching, etc, etc), we do
       not need to include the current stmt in the state. It is easier
       to simply get it form the current continuation *)

    Record state: Type := mkState
      { s_cs; (* n is not a type parameter, because we could not write step *)
        s_cont: cont s_cs;
        s_env: env s_cs;
        s_mem: M.mem}.

    Definition translate_loc {csi} ctxt (p: array_id * list (nvector (S csi)))
     :cell_id num:=
      {| array := fst p;
         cell := List.map (fun v =>〈v, ctxt〉) (snd p)|}.
    Open Scope numerical_scope.



    (* I don't know how to prove a general property on mmap *)
    Lemma mmap_option A B (f: A -> option B) l1 l2:
      mmap f l1 = Some l2 ->
      list_forall2 (fun b ob => Some b = ob) l2 (map f l1).
    Proof.
      revert l2. induction l1; intros l2 MMAP; simpl in *.
      clean. constructor.

      monadInv MMAP.
      constructor; auto.
    Qed.


    Definition Amin_lst (a : num) (l: list num) :=
      fold_left Amin l a.

    Lemma fold_left_Amin: forall l a, fold_left Amin l a <= a.
    Proof.
      induction l; simpl in *; intros.

      reflexivity.

      etransitivity; eauto. apply Amin_le1.
    Qed.

    Lemma fold_left_Amin_le: forall l a1 a2, a1 <= a2 ->
      fold_left Amin l a1 <= fold_left Amin l a2.
    Proof.
      induction l; simpl.

      intuition.

      intros * LE.
      apply IHl.
      destruct (Ale_dec a1 a); [rewrite Amin_correct1 | rewrite Amin_correct2]; auto;
      (destruct (Ale_dec a2 a); [rewrite Amin_correct1 | rewrite Amin_correct2]); auto.
      apply Agt_le in n. assert (a = a2); [| subst; reflexivity].
      apply Ale_antisym; auto. etransitivity; eauto.
      reflexivity.
    Qed.



    Lemma Amin_lst_le a l: list_forall (fun x => Amin_lst a l <= x) (a::l).
    Proof.
      constructor.
      apply fold_left_Amin.

      induction l.
      constructor.
      simpl. repeat constructor.
      etransitivity.
      apply fold_left_Amin. apply Amin_le2.
      eapply list_forall_imply; [|eauto].
      simpl.
      unfold Amin_lst.
      intros. etransitivity; eauto.
      apply fold_left_Amin_le. apply Amin_le1.
    Qed.

    Lemma Amin_lst_correct a l a':
      list_forall (fun x => a' <= x) (a :: l) ->
      a' <= Amin_lst a l.
    Proof.
      unfold Amin_lst.
      intro. inv H.
      revert dependent a. revert H3.
      induction l; intros LFA * LEQ; simpl.

      assumption.
      inv LFA.
      apply IHl; auto.

      destruct (Ale_dec a0 a); [rewrite Amin_correct1 | rewrite Amin_correct2]; auto.
    Qed.



    Definition Amax_lst (a : num) (l: list num) :=
      fold_left Amax l a.

    Lemma fold_left_Amax: forall l a, a <= fold_left Amax l a.
    Proof.
      induction l; simpl in *; intros.

      reflexivity.

      etransitivity; [| apply IHl].
      apply Amax_ge1.
    Qed.

    Lemma fold_left_Amax_le: forall l a1 a2, a1 <= a2 ->
      fold_left Amax l a1 <= fold_left Amax l a2.
    Proof.
      induction l; simpl.

      intuition.

      intros * LE.
      apply IHl.
      destruct (Ale_dec a1 a); [rewrite Amax_correct2 | rewrite Amax_correct1]; auto;
      (destruct (Ale_dec a2 a); [rewrite Amax_correct2 | rewrite Amax_correct1]); auto.
      reflexivity.

      apply Agt_le in n. auto.

      apply Agt_le in n. etransitivity; eauto.
    Qed.



    Lemma Amax_lst_le a l: list_forall (fun x => x <= Amax_lst a l) (a::l).
    Proof.
      constructor.
      apply fold_left_Amax.

      induction l.
      constructor.
      simpl. repeat constructor.
      etransitivity; [|apply fold_left_Amax].
      apply Amax_ge2.

      eapply list_forall_imply; [|eauto].
      simpl.
      unfold Amax_lst.
      intros. etransitivity; eauto.
      apply fold_left_Amax_le. apply Amax_ge1.
    Qed.

    Lemma Amax_lst_correct a l a':
      list_forall (fun x => x <= a') (a :: l) ->
      Amax_lst a l <= a'.
    Proof.
      unfold Amax_lst.
      intro. inv H.
      revert dependent a. revert H3.
      induction l; intros LFA * LEQ; simpl.

      assumption.
      inv LFA.
      apply IHl; auto.

      destruct (Ale_dec a0 a); [rewrite Amax_correct2 | rewrite Amax_correct1]; auto.
    Qed.



    (* v is the "first value" of the loop *)
    Inductive fst_value (lower_bound upper_bound: list (num * num)) (lstep: num)
      (v: num): Prop :=
    | fstv_pos:
      forall a1 lb l1,
        mmap (fun p => Aceild (snd p) (fst p)) lower_bound = Some lb ->
        lstep > 0 -> a1 :: l1 = lb -> Amax_lst a1 l1 = v ->
        fst_value lower_bound upper_bound lstep v
    | fstv_neg:
      forall a2 ub l2,
        mmap (fun p => Afloord (snd p) (fst p)) upper_bound = Some ub ->
        lstep < 0 -> a2 :: l2 = ub -> Amin_lst a2 l2 = v ->
        fst_value lower_bound upper_bound lstep v.

    Inductive in_bound (lower_bound upper_bound: list (num * num)) (lstep: num)
      (v: num): Prop :=
    | inb_pos:
      lstep > 0 -> upper_bound <> nil ->
      list_forall (fun p => Ale 1 (fst p) /\ Ale (fst p * v) (snd p)) upper_bound ->
      in_bound lower_bound upper_bound lstep v
    | inb_neg:
      lstep < 0 -> lower_bound <> nil ->
      list_forall (fun p => Ale 1 (fst p) /\ Ale (snd p) (fst p * v)) lower_bound ->
      in_bound lower_bound upper_bound lstep v.


    Definition extend_env {n} (e:env n) : env (S n) := 1 ::: e.

    Definition apply_ext_env {n} (e:env n) := fun (p: num * _) => (fst p, 〈1 ::: e, snd p〉).
    Definition apply_ext_env_lst {n} (e: env n) := map (apply_ext_env e).

    Inductive step : state -> state -> Prop :=
    | step_instr:
      forall n (k: cont n) id instr e lst M rlocs rvals wloc wval ctxt tctxt mem1 mem2,
        (* we extract the instruction related to the id *)
        PTree.get 'id prog.(instrs) = Some instr ->
        (* we convert the list of transformation to a matrix of proper dimension*)
        make_vector (cs instr) lst = Some M ->

        (* context of the instruction *)
        M × (1 ::: e) = ctxt ->
        (1 ::: ctxt) = tctxt ->
        (* we translate the read locations and access them*)
        map (translate_loc tctxt) (I.read_locs instr) = rlocs->
        mmap (M.read mem1) rlocs = Some rvals ->

        (* the semantic gives us a value to write back *)
        I.semantic instr ctxt rvals  wval ->

        (* we write it to the write location *)
        translate_loc tctxt (I.write_loc instr) = wloc->
        M.write mem1 wloc wval = Some mem2 ->

        step
        {| s_cs:= n; s_cont := (Kseq (Instr id lst) k); s_env := e; s_mem := mem1|}
        {| s_cs:= n; s_cont := k; s_env := e; s_mem := mem2|}

    | step_enter_loop:
      forall n lower upper lower_v upper_v lstep lst k e m fst_v,
        apply_ext_env_lst e lower = lower_v ->
        apply_ext_env_lst e upper = upper_v ->
        fst_value lower_v upper_v lstep fst_v ->
        in_bound lower_v upper_v lstep fst_v ->

        step
        {| s_cs:= n; s_cont := Kseq (Loop lower upper lstep lst) k;
          s_env := e; s_mem := m|}
        {| s_cs:= S n;
           s_cont := add_stmts lst (Kloop lower upper lstep lst k) ;
           s_env := fst_v ::: e; s_mem := m|}

    | step_skip_loop:
      forall n lower upper lower_v upper_v lstep lst k e m fst_v,
        apply_ext_env_lst e lower = lower_v ->
        apply_ext_env_lst e upper = upper_v ->
        fst_value lower_v upper_v lstep fst_v ->
        ~ in_bound lower_v upper_v lstep fst_v ->

        step
        {| s_cs:= n; s_cont := Kseq (Loop lower upper lstep lst) k;
          s_env := e; s_mem := m|}
        {| s_cs:= n;
           s_cont := k ;
           s_env := e; s_mem := m|}

    | step_repeat_loop:
      forall n lower upper lower_v upper_v lstep lst k e m v,
        apply_ext_env_lst e lower = lower_v ->
        apply_ext_env_lst e upper = upper_v ->
        in_bound lower_v upper_v lstep (v + lstep) ->

        step
        {| s_cs:= S n; s_cont := Kloop lower upper lstep lst k;
           s_env := v ::: e; s_mem := m|}
        {| s_cs:= S n;
           s_cont := add_stmts lst (Kloop lower upper lstep lst k) ;
           s_env := (v + lstep) ::: e; s_mem := m|}
    | step_exit_loop:
      forall n lower upper lower_v upper_v lstep lst k e m v,
        apply_ext_env_lst e lower = lower_v ->
        apply_ext_env_lst e upper = upper_v ->
        ~ in_bound lower_v upper_v lstep (v + lstep) ->
        step
        {| s_cs:= S n; s_cont := Kloop lower upper lstep lst k;
           s_env := v ::: e; s_mem := m|}
        {| s_cs:= n;
           s_cont := k ;
           s_env :=  e; s_mem := m|}
.

Tactic Notation "inv_step" constr(st) :=
  cases st (inv st).

(*Tactic Notation "step_cases" tactic(first) tactic(c) :=
  first;
  [ c "step_instr"
  | c "step_enter_loop"
  | c "step_skip_loop"
  | c "step_repeat_loop"
  | c "step_exit_loop"].*)

(* a valid trace is a liste of state, from an initial state, to a
   final one (with continuation Kstop) of memory m*)

Inductive valid_trace: forall (init_state : state) (final_mem: M.mem)
  (trace: list state), Prop :=
| VT_final: forall n e m,
  valid_trace
  {|s_cs := n; s_cont := Kstop; s_env := e; s_mem := m|} m
  [{|s_cs := n; s_cont := Kstop; s_env := e; s_mem := m|}]
| VT_step: forall s1 s2 m trace,
  step s1 s2 -> valid_trace s2 m trace ->
  valid_trace s1 m (s1::trace).

Tactic Notation "inv_valid_trace" constr(vt) :=
  cases vt (inv vt).

Inductive prog_sem (params: nvector prog.(nbr_params)) m1 m2 : Prop:=
| PS_intro: forall trace,
  valid_trace
  {|s_cs := prog.(nbr_params);
    s_cont := add_stmts prog.(prog_main) Kstop;
    s_env := params;
    s_mem := m1|}
  m2 trace ->
  prog_sem params m1 m2.




Lemma fst_value_deterministic lower_bound upper_bound lstep v1 v2:
  fst_value lower_bound upper_bound lstep v1 ->
  fst_value lower_bound upper_bound lstep v2 ->
  v1 = v2.
Proof.
  intros FST1 FST2.
  inv FST1; inv FST2; try congruence.
  apply Agt_le in H0. contradiction.
  apply Agt_le in H0. contradiction.
Qed.


Lemma step_deterministic st st1 st2: step st st1 -> step st st2 ->
  st1 = st2.
Proof.
  intros STEP1 STEP2. 
  inv_step STEP1;
  inv STEP2; clean;
  repeat match goal with
    | H1: ?X = ?Y,
      H2: ?X = ?Z |- _ =>
        match Y with
          | Z => fail 1
          | _ => let H := fresh "H" in
            assert (Y = Z) as H by congruence; clean in H; subst
        end
    | H1: fst_value ?LB ?UB ?LS ?v1,
      H2: fst_value ?LB ?UB ?LS ?v2 |- _ =>
        match v1 with
          | v2 => fail 1
          | _ => pose proof (fst_value_deterministic H1 H2); subst
        end
  end; try reflexivity; try contradiction.

  Case "step_instr".
  assert (wval = wval0).
  eapply I.deterministic_semantic; eauto. subst.
  repeat match goal with
    | H1: ?X = ?Y,
      H2: ?X = ?Z |- _ =>
        match Y with
          | Z => fail 1
          | _ => let H := fresh "H" in
            assert (Y = Z) as H by congruence; clean in H; subst
        end
  end. reflexivity.
Qed.


Lemma valid_trace_deterministic init_state m1 m2 trace1 trace2:
  valid_trace init_state m1 trace1 ->
  valid_trace init_state m2 trace2 -> m1 = m2 (* /\ trace1 = trace2 *).
Proof.
  intros VAL1. revert trace2.
  induction' VAL1; intros trace2 VAL2;
  (inv_valid_trace VAL2; clean).

  Case "VT_final"; SCase "VT_step".
    inv H.

  Case "VT_step"; SCase "VT_final".
    inv H.

  Case "VT_step"; SCase "VT_step". 
  assert (s2 = s3) by (eauto using step_deterministic). subst.

  eauto.
Qed.

Theorem prog_sem_determinisic: forall param m1 m2 m2',
  prog_sem param m1 m2 -> prog_sem param m1 m2' -> m2 = m2'.
Proof.
  intros * SEM SEM'.
  inv SEM; inv SEM'.
  eauto using valid_trace_deterministic.
Qed.

(* we now show that a program never touches the parameters *)


Unset Implicit Arguments.
Inductive cont_ends_at_n (n: nat) : forall p, cont p -> Prop :=
| CEAN_stop: cont_ends_at_n n n (@Kstop n)
| CEAN_seq: forall p st (k: cont p),
  cont_ends_at_n n p k -> cont_ends_at_n n p (Kseq st k)
| CEAN_loop: forall p l1 l2 v lst (k: cont p),
  cont_ends_at_n n p k -> cont_ends_at_n n (S p) (Kloop l1 l2 v lst k).
Set Implicit Arguments.


Lemma cont_only_decrease n p (k: cont p): cont_ends_at_n n _ k ->
  (n <= p)%nat.
Proof.
  intros CONT_ENDS.
  induction CONT_ENDS; try omega.
Qed.

Lemma concat_vect0 n (v1: nvector O) (v2: nvector n):
  v1 +++ v2 = v2.
Proof.
  dest_vects. destruct v1; simpl in *; auto.
  unfold concat_vect. simpl. apply vect_eq. simpl. reflexivity.
Qed.

Hint Resolve concat_vect0.

  Ltac clean_n :=
    match goal with
      | H : ?X = (?N + ?X)%nat |- _ =>
        assert (N = O) by omega; subst; simpl in *; clean
    end.


(* v2 extends v1 *)
Inductive vect_extends n1 (v1: nvector n1): forall n2, nvector n2 -> Prop :=
| VE_same: vect_extends v1 v1
| VE_cons: forall n2 (v2: nvector n2) N,
  vect_extends v1 v2 -> vect_extends v1 (vcons N v2)
.


Lemma vect_ext_longer n1 (v1: nvector n1) n2 (v2: nvector n2):
  vect_extends v1 v2 -> (n2 >= n1)%nat.
Proof.
  intro EXT.
  induction EXT; omega.
Qed.

Lemma vect_ext_length_eq n1 (v1: nvector n1) n2 (v2: nvector n2):
  n1 = n2 -> vect_extends v1 v2 -> v1 ~= v2.
Proof.
  intros EQ EXT.
  induction EXT.
  constructor.
  subst. apply vect_ext_longer in EXT. elimtype False. omega.
Qed.

Lemma vect_ext_same_length1 n (v1 v2: nvector n):
  vect_extends v1 v2 -> v1 = v2.
Proof.
  intro.
  apply JMeq_eq. apply vect_ext_length_eq; auto.
Qed.

Lemma vect_ext_same_length2 n (v1 v2: nvector n):
  vect_extends v1 v2 -> v2 = v1.
Proof.
  intros. symmetry. apply vect_ext_same_length1. auto.
Qed.

Lemma vect_ext_shorter n1 n2 (v1: nvector n1) (v2: nvector n2) x:
  (n1 <= n2)%nat ->
  vect_extends v1 (x ::: v2) ->
  vect_extends v1 v2.
Proof.
  intros INF EXT.
  inv_clean EXT. omegaContradiction.
Qed.



Lemma add_stmt_not_stop: forall n lower upper lstep lst (k: cont n),
  add_stmts lst (Kloop lower upper lstep lst k) = Kstop -r> False.
Proof.
  intros. constructor. destruct lst; simpl; intro H; inv H.
Qed.

Hint Rewrite add_stmt_not_stop: clean.
Hint Resolve vect_ext_same_length1 vect_ext_same_length2.


  Ltac clean_useless := repeat match goal with
    | x: ?t |- _=>
      match type of t with
        | Type => clear x; idtac x
      end
  end.

Tactic Notation "step_inversion" ident(H):=
  match type of H with
    | step _ _ =>
      let H' := fresh H in
      pose proof H as H';
      (cases H (dependent destruction H'))
  end.
Tactic Notation "step_inv" ident(H):=
  match type of H with
    | step _ _ =>
      (cases H (dependent destruction H)); clean
  end.

Lemma cont_ends_Kstop: forall n1 n2,
  tag_to_inv (cont_ends_at_n n1 n2 Kstop).
Proof.
  auto.
Qed.

Lemma cont_ends_Kseq: forall n1 n2 st,
  tag_to_inv (cont_ends_at_n n1 n2 (Kseq st Kstop)).
Proof.
  auto.
Qed.

Lemma cont_ends_Kloop: forall n1 n2 lv1 lv2 v lst,
  tag_to_inv (cont_ends_at_n n1 (S n2) (Kloop lv1 lv2 v lst Kstop)).
Proof.
  auto.
Qed.

Hint Rewrite cont_ends_Kstop cont_ends_Kseq cont_ends_Kloop: opt_inv.



Lemma nctp_aux (params : nvector prog.(nbr_params)) n (e: env n)
  trace k m1 m2:
  valid_trace {| s_cs := n;
                 s_cont := k;
                 s_env := e;
                 s_mem := m1 |} m2 trace ->
  cont_ends_at_n (prog.(nbr_params)) _ k ->
  vect_extends params e ->
   last trace = Some {| s_cs := prog.(nbr_params);
                        s_cont := Kstop;
                        s_env := params;
                        s_mem := m2 |}.
Proof.
  intros VALID.
  cases VALID (dependent induction VALID); intros ENDSAT EXT.

  Case "VT_final".
  simpl. f_equal.
  inv ENDSAT. clean. f_equal; auto.


  Case "VT_step".
  inv' VALID.
  SCase "VT_final".
  Focus 1.
  simpl.


  (step_inv H); try solve [repeat f_equal; auto].

  SSCase "step_exit_loop".
  simpl in *.
  eapply IHVALID; eauto. constructor.
  inv EXT; clean. omegaContradiction.

  Case "VT_step"; SCase "VT_step". 
  destruct s2.
  eapply IHVALID ;[SSCase "equal" | SSCase "cont_ends_at" | SSCase "vect_extends"];
    clear IHVALID. 


  SSCase "equal".
    reflexivity.

  SSCase "cont_ends_at".
  (step_inv H); try solve [ inv_clean ENDSAT].
  S3Case "step_enter_loop".
  clear - ENDSAT. inv_clean ENDSAT.
  match goal with
    | |- context[add_stmts _ ?X ] => remember X as k
  end.
  assert (cont_ends_at_n (nbr_params prog) _ k).
  subst k. constructor; auto.
  clear Heqk.
  induction lst; simpl in * ;auto; constructor; auto.
  S3Case "step_repeat_loop".
  clear - ENDSAT. inv_clean ENDSAT.
  match goal with
    | |- context[add_stmts _ ?X ] => remember X as k
  end.
  assert (cont_ends_at_n (nbr_params prog) _ k).
  subst k. constructor; auto.
  clear Heqk.
  induction lst; simpl in * ;auto; constructor; auto.

  SSCase "vect_extends".
  (step_inv H); try solve [constructor; auto].

  inv_clean ENDSAT. apply cont_only_decrease in H4.
  inv EXT. inversion H6. omegaContradiction. clean. constructor. auto.

  inv_clean ENDSAT. apply cont_only_decrease in H4.
  inv EXT. inversion H6. omegaContradiction. clean.
Qed.


Theorem no_changes_to_params params trace m1 m2:
   valid_trace
                 {|
                 s_cs := nbr_params prog;
                 s_cont := add_stmts (prog_main prog) Kstop;
                 s_env := params;
                 s_mem := m1 |} m2 trace ->
   last trace = Some {| s_cs := nbr_params prog;
                        s_cont := Kstop;
                        s_env := params;
                        s_mem := m2 |}.
Proof.
  intros. eapply nctp_aux. eauto.
  remember (prog.(prog_main)) as main.
  clear.
  induction main; constructor; auto.
  constructor.
Qed.

End RELSEM.
End Semantique.
