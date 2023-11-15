Require Import Lia.
Require Import Arith.
Require Import List.
Require Import Program.
Require Import Relations.
Require Import Program.Wf.
Import ListNotations.

Set Implicit Arguments.

Section AssocList.

  Variable T: Type.
  Variable U: Type.

  Definition assoc_list: Type :=
    list (T * U).

  Hypothesis T_eq_dec:
    forall t1 t2: T,
    { t1 = t2 } + { t1 <> t2 }.

  Fixpoint lookup al key: option U :=
    match al with
    | [] =>
      None
    | (t, u) :: cdr =>
      if T_eq_dec key t then
        Some u
      else
        lookup cdr key
    end.

  Fixpoint delete_key al key: assoc_list :=
    match al with
    | [] =>
      []
    | (t, u) :: cdr =>
      if T_eq_dec key t then
        delete_key cdr key
      else
        (t, u) :: delete_key cdr key
    end.

  Goal
    forall al key value,
    ~In (key, value) (delete_key al key).
  Proof.
    induction al; intros; intro.
    - simpl in H.
      assumption.
    - destruct a; simpl in H.
      destruct (T_eq_dec key t).
      + firstorder.
      + destruct H.
        * dependent destruction H.
          contradiction.
        * firstorder.
  Qed.

End AssocList.

Section Dijkstra.

  Variable vertex: Set.
  Variable V: list vertex.
  Variable E: vertex -> vertex -> option nat.

  (* Source. *)
  Variable s: vertex.

  Hypothesis vertex_eq_dec:
    forall v u: vertex,
    { v = u } + { v <> u }.

  Implicit Types Q: list vertex.
  Implicit Types u: vertex.

  Definition get_weight (v: vertex) (u: vertex): nat :=
    match E v u with
    | Some n => n
    | None => 0
    end.

  Definition distance: Type :=
    assoc_list vertex nat.

  Definition set d v n: distance :=
    (v, n) :: delete_key vertex_eq_dec d v.

  Definition get (d: distance) (v: vertex) (w: nat): nat :=
    match lookup vertex_eq_dec d v with
    | Some x => x
    | None => w
    end.

  Program Fixpoint take_shortest (Q: list vertex) (d: distance) (H: length Q > 0)
    { measure (length Q) }: vertex :=
    match Q with
    | [] =>
      False_rect _ _
    | [v] =>
      v
    | v :: (u :: _) as Q' =>
      let u' := take_shortest Q' d _ in
      match (lookup vertex_eq_dec d v, lookup vertex_eq_dec d u') with
      | (Some x, Some y) =>
        if x <? y then
          v
        else
          u'
      | (None, Some y) => u'
      | (_, None) => v
      end
    end.

  Next Obligation.
    inversion H.
  Defined.

  Next Obligation.
    simpl; lia.
  Defined.

  Fixpoint remove Q v :=
    match Q with
    | [] => []
    | u :: us =>
      if vertex_eq_dec v u then
        us
      else
        u :: remove us v
      end.

  Lemma In_positive_length:
    forall Q v,
    In v Q -> length Q > 0.
  Proof.
    destruct Q; intros.
    - exfalso.
      inversion H.
    - simpl; lia.
  Qed.

  Lemma remove_In_decreases_length:
    forall Q v,
    In v Q ->
    length (remove Q v) = length Q - 1.
  Proof with firstorder.
    induction Q; intros.
    - exfalso.
      inversion H.
    - simpl.
      destruct (vertex_eq_dec v a).
      + lia.
      + simpl.
        destruct H.
        * exfalso...
        * specialize (IHQ v H).
          apply In_positive_length in H.
          lia.
  Qed.

  Lemma remove_In_preservation:
    forall x Q,
    In x Q ->
    forall y,
    x <> y ->
    In x (remove Q y).
  Proof.
    induction Q; simpl; intros.
    - assumption.
    - destruct H.
      + subst.
        destruct (vertex_eq_dec y x).
        * subst; exfalso.
          contradiction.
        * left; auto.
      + destruct (vertex_eq_dec y a).
        * subst; auto.
        * right; auto.
  Qed.

  Fixpoint neighbors (Q: list vertex) (u: vertex): list vertex :=
    match Q with
    | [] =>
      []
    | v :: Q' =>
      if E u v then
        v :: neighbors Q' u
      else
        neighbors Q' u
      end.

  Lemma take_shortest_In:
    forall d Q H,
    In (take_shortest Q d H) Q.
  Proof.
    admit.
  Admitted.

  (* -------------------------------------------------------------------------

    b0(Q, dist, prev):
            while Q is not empty:
    b1(Q, dist, prev):
                u ← vertex in Q with min dist[u]
                remove u from Q
    b2(Q, V, dist, prev, u):
                for each neighbor v of u still in Q:
    b3(Q, V, dist, prev, u, v):
                    alt ← dist[u] + Graph.Edges(u, v)
                    if alt < dist[v]:
                        dist[v] ← alt
                        prev[v] ← u
                    else:
                        pass
    b4(Q, dist, prev):
            return dist[], prev[]

  ------------------------------------------------------------------------- *)

  (* Block b2... *)
  Fixpoint b2 N (d: distance) u :=
    match N with
    | [] =>
      d
    | v :: N' =>
      (* Block b3... *)
      let alt := get d u 0 + get_weight u v in
      (* The default value, if v is not set in d, is 1 + alt such that we will
         get inside the if! *)
      if alt <? get d v (1 + alt) then
        let d' := set d v alt in
        b2 N' d' u
      else
        (* Continue the for loop. *)
        b2 N' d u
    end.

  (* Block b0... *)
  Program Fixpoint b0 Q d { measure (length Q) } :=
    match Q with
    | [] =>
      (* Block b4... *)
      d
    | _ =>
      (* Block b1... *)
      let u := take_shortest Q d _ in
      let Q' := remove Q u in
      (* Is u recheable? If so, it has a defined distance! *)
      if lookup vertex_eq_dec d u then
        let N := neighbors Q' u in
        let d' := b2 N d u in
        b0 Q' d'
      else
        (* In here, u is unrecheable (i.e., infinity in the pseudocode). *)
        b0 Q' d
    end.

  Next Obligation.
    destruct Q; try contradiction.
    simpl; lia.
  Defined.

  Next Obligation.
    rewrite remove_In_decreases_length.
    - destruct Q; try contradiction.
      simpl; lia.
    - apply take_shortest_In.
  Defined.

  Next Obligation.
    rewrite remove_In_decreases_length.
    - destruct Q; try contradiction.
      simpl; lia.
    - apply take_shortest_In.
  Defined.

  Definition dijkstra :=
    (* We start by taking the distance from s to itself as 0! *)
    b0 V [(s, 0)].

  Lemma b0_unfold_done:
    forall d,
    b0 [] d = d.
  Proof.
    reflexivity.
  Qed.

  Lemma b0_unfold_step:
    forall Q d H,
    b0 Q d = let u := take_shortest Q d H in
             let Q' := remove Q u in
             let V := neighbors Q' u in
             let d' := b2 V d u in
             b0 Q' d'.
  Proof.
    intros.
    destruct Q.
    - exfalso.
      inversion H.
    - unfold b0.
      unfold b0_func at 1.
      rewrite Fix_eq; simpl.
      + admit.
      + intros.
        destruct x; auto; simpl.
        destruct x; auto; simpl.
  Admitted.

  (* ---------------------------------------------------------------------- *)

  Inductive path: vertex -> vertex -> nat -> Prop :=
    | path_here:
      forall v,
      In v V ->
      path v v 0
    | path_step:
      forall v u n,
      In v V ->
      In u V ->
      E v u = Some n ->
      path v u n
    | path_trans:
      forall v u w n m,
      path v u n ->
      path u w m ->
      path v w (n + m).

  Lemma path_In_V_left:
    forall v u w,
    path v u w -> In v V.
  Proof.
    induction 1; auto.
  Qed.

  Lemma path_In_V_right:
    forall v u w,
    path v u w -> In u V.
  Proof.
    induction 1; auto.
  Qed.

  Definition shortest_path v u n: Prop :=
    (* The path from v to u with weight n is the shortest if:
         1) it exists (of course); and
         2) for any other existing paths from v to u with weight m, n <= m
    *)
    path v u n /\ (forall m, path v u m -> n <= m).

  Lemma shortest_path_In_V_left:
    forall v u w,
    shortest_path v u w -> In v V.
  Proof.
    destruct 1.
    eapply path_In_V_left.
    eassumption.
  Qed.

  Lemma shortest_path_In_V_right:
    forall v u w,
    shortest_path v u w -> In u V.
  Proof.
    destruct 1.
    eapply path_In_V_right.
    eassumption.
  Qed.

  Lemma shortest_path_unique:
    forall v u x y,
    shortest_path v u x ->
    shortest_path v u y ->
    x = y.
  Proof.
    destruct 1; destruct 1.
    specialize (H0 y H1).
    specialize (H2 x H).
    lia.
  Qed.

  Definition sane d: Prop :=
    forall v x,
    In (v, x) d -> path s v x.

  Definition recheable v u: Prop :=
    exists w,
    shortest_path v u w.

  (* The following proposition is kept at each step of the while loop! *)

  Definition invariant (Q: list vertex) (d: distance): Prop :=
    forall v,
    In v V ->
    (* Not visited yet: *) In v Q \/
       (* Already seem: *) (recheable s v ->
                           (* If it is reacheable, then... *)
                              exists2 w, In (v, w) d & shortest_path s v w).

  (* -------------------------------------------- *)

  (* Each time I execute b2, the relaxing function, the sanity is kept! *)

  Lemma sane_preservation:
    forall Q d,
    sane d ->
    forall H u,
    u = take_shortest Q d H ->
    forall Q',
    Q' = remove Q u ->
    forall N,
    N = neighbors Q' u ->
    forall d',
    d' = b2 N d u ->
    sane d'.
  Proof.
    admit.
  Admitted.

  (* Each time I execute b2, the relaxing function, our invariant is kept! *)

  Lemma invariance_preservation:
    forall Q d,
    invariant Q d ->
    forall H u,
    u = take_shortest Q d H ->
    forall Q',
    Q' = remove Q u ->
    forall N,
    N = neighbors Q' u ->
    forall d',
    d' = b2 N d u ->
    sane d' ->
    invariant Q' d'.
  Proof.
    intros; intros x ?.
    (* The vertex x has already been processed? *)
    destruct H with x; auto.
    - (* The vertex x is still on the work list! Are we removing it *now*? *)
      destruct (vertex_eq_dec x u).
      + (* We'll process it now! *)
        subst x; right; intros.
        destruct H8 as (w, ?).
        exists w; auto.
        (* Hmmm... some tricky equations here. *)
        admit.
      + (* It won't be processed yet! So postpone this... *)
        left; rewrite H2.
        apply remove_In_preservation; auto.
    - (* We have already processed it! So we just keep our invariant: we can't
         make the path even smaller... *)
      right; intros.
      destruct H7 as (w, ?, ?); auto.
      exists w; auto.
      (* By H7 we know that d' should have (x, a) such that a <= w. By H5, there
         is a path from s to x with weight a. By H9, we know that w <= a. So,
         a = w and we are done. *)
      admit.
  Admitted.

  Lemma step_correctness:
    forall Q d w,
    sane d ->
    invariant Q d ->
    forall v,
    shortest_path s v w ->
    In (v, w) (b0 Q d).
  Proof.
    intros Q.
    (* The proof follows by induction on the length of Q. *)
    remember (length Q) as n.
    generalize dependent Q.
    induction n using lt_wf_ind; intros.
    destruct n.
    - (* If Q is empty, our hypothesis says that every recheable vertex has its
         optimal path stored in d. *)
      destruct Q; try discriminate; clear Heqn.
      unfold invariant in H0.
      assert (In v V) by (eapply shortest_path_In_V_right; eauto).
      destruct H1 with v; auto.
      + inversion H4.
      + rewrite b0_unfold_done.
        unfold sane in H0.
        destruct H4 as (x, ?, ?).
        * exists w; auto.
        * replace w with x; auto.
          apply shortest_path_unique with s v; auto.
    - (* We still have some work to do! Let's process the smallest value. *)
      assert (length Q > 0) by lia.
      rewrite b0_unfold_step with (H := H3); try lia; simpl.
      remember (take_shortest Q d H3) as u.
      remember (remove Q u) as Q'.
      remember (neighbors Q' u) as N.
      remember (b2 N d u) as d'.
      (* Specialize our inductive hypothesis first... *)
      specialize H with (m := n) (Q := Q') (d := d').
      (* We can use our inductive hypothesis directy now! *)
      apply H.
      + (* |Q| > |Q'| *)
        auto.
      + rewrite HeqQ'.
        rewrite remove_In_decreases_length; try lia.
        rewrite Hequ.
        apply take_shortest_In; try lia.
      + (* Relaxing doesn't add paths that don't exist. *)
        eapply sane_preservation; eauto.
      + eapply invariance_preservation; eauto.
        (* Same as above! *)
        eapply sane_preservation; eauto.
      + (* We already know our vertex is recheable with weight w. *)
        assumption.
  Qed.

  Theorem correctness:
    forall v w,
    shortest_path s v w ->
    In (v, w) dijkstra.
  Proof.
    intros.
    apply step_correctness.
    - intros u x ?.
      destruct H0; try contradiction.
      dependent destruction H0.
      constructor.
      apply shortest_path_In_V_left with v w.
      assumption.
    - left; auto.
    - assumption.
  Qed.

End Dijkstra.

(* -------------------------------------------------------------------------- *)

Section Example.

  Definition V :=
    [1; 2; 3; 4].

  Definition E: nat -> nat -> option nat :=
    fun v u =>
      match (v, u) with
      | (1, 2) => Some 4
      | (1, 3) => Some 3
      | (2, 1) => Some 2
      | (3, 2) => Some 1
      | (3, 4) => Some 9
      | (1, 4) => Some 2
      | _ => None
      end.

  Compute dijkstra V E 1 Nat.eq_dec.
  Compute dijkstra V E 2 Nat.eq_dec.
  Compute dijkstra V E 3 Nat.eq_dec.
  Compute dijkstra V E 4 Nat.eq_dec.

End Example.

Require Import Extraction.
Extraction Language Haskell.

Recursive Extraction dijkstra.
