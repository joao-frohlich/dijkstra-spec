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

End AssocList.

(*

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
*)

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
    (v, n) :: d.

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

  Lemma remove_preservation:
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
      let N := neighbors Q' u in
      let d' := b2 N d u in
      b0 Q' d'
    end.

  Next Obligation.
    destruct Q; try contradiction.
    simpl; lia.
  Defined.

  Next Obligation.
    simpl.
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

  (* Definition sane d: Prop :=
    forall v x,
    In (v, x) d ->
    exists2 y,
    shortest_path s v y & x >= y. *)

  Definition invariant (Q: list vertex) (d: distance): Prop :=
    forall v,
    In v V ->
    (* Not visited yet: *) In v Q \/
       (* Already seem: *) (exists2 w, In (v, w) d & shortest_path s v w).

  Lemma invariance_preservation:
    forall Q d,
    invariant Q d ->
    forall v w,
    shortest_path s v w ->
    forall H u,
    u = take_shortest Q d H ->
    forall Q',
    Q' = remove Q u ->
    forall N,
    N = neighbors Q' u ->
    forall d',
    d' = b2 N d u ->
    invariant Q' d'.
  Proof.
    intros; intros x ?.
    destruct H with x as [ ? | (y, ?, ?) ]; auto.
    - (* The node x hasn't been visited. We can visit it now, or it may remain
         on the queue. Check if we are visiting it now! *)
      destruct (vertex_eq_dec x u).
      + (* We are visiting it now! *)
        right; subst x.
        admit.
      + (* It remains on the queue! *)
        left; subst.
        remember (take_shortest Q d H1) as u.
        apply remove_preservation; auto.
    - (* We already visited x, so we alrady know its shortest path! *)
      right; exists y.
      + (* The relax can't change y, so this relies on H7. *)
        admit.
      + assumption.
  Admitted.

  Lemma step_correctness:
    forall Q d w,
    invariant Q d ->
    forall v,
    shortest_path s v w ->
    In (v, w) (b0 Q d).
  Proof.
    intros Q.
    remember (length Q) as n.
    generalize dependent Q.
    induction n using lt_wf_ind; intros.
    destruct n.
    - (* We're sure we've seem v! *)
      destruct Q; try discriminate; clear Heqn.
      unfold invariant in H0.
      assert (In v V) by (eapply shortest_path_In_V_right; eauto).
      specialize (H0 v H2).
      rewrite b0_unfold_done.
      destruct H0.
      + exfalso.
        inversion H0.
      + destruct H0 as (x, ?, ?).
        replace w with x.
        * assumption.
        * apply shortest_path_unique with s v; auto.
    - assert (length Q > 0) by lia.
      rewrite b0_unfold_step with (H := H2); try lia; simpl.
      remember (take_shortest Q d H2) as u.
      remember (remove Q u) as Q'.
      remember (neighbors Q' u) as N.
      remember (b2 N d u) as d'.
      (* We can use our inductive hypothesis now! *)
      apply H with n.
      + auto.
      + rewrite HeqQ'.
        rewrite remove_In_decreases_length; try lia.
        rewrite Hequ.
        apply take_shortest_In; try lia.
      + eapply invariance_preservation; eauto.
      + assumption.
  Qed.

  Theorem correctness:
    forall v w,
    shortest_path s v w ->
    In (v, w) dijkstra.
  Proof.
    intros.
    apply step_correctness.
    - intros u ?.
      left; auto.
    - assumption.
  Qed.

End Dijkstra.

(* -------------------------------------------------------------------------- *)

Section Example.

  Definition V :=
    [1; 2; 3].

  Definition E: nat -> nat -> option nat :=
    fun v u =>
      match (v, u) with
      | (1, 2) => Some 4
      | (1, 3) => Some 3
      | (2, 1) => Some 2
      | (3, 2) => Some 1
      | _ => None
      end.

  Definition example := dijkstra V E 1 Nat.eq_dec.

End Example.

Require Import Extraction.
Extraction Language Haskell.

Recursive Extraction example.
