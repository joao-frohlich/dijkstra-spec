(* A brincadeira agora é com SSA *)

Axiom TODO: forall {T}, T.

(*
Q: list of vertices
dist: function from vertices to weight
prev: function from vertices to vertices

*)

Require Import Lia.
Require Import Arith.
Require Import List.
Require Import Program.
Import ListNotations.

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
  Variable edges: list (vertex * vertex * nat).

  Hypothesis vertex_eq_dec:
    forall v u: vertex,
    { v = u } + { v <> u }.

  (* Source. *)
  Variable s: vertex.

  Set Implicit Arguments.
  Implicit Types Q: list vertex.
  Implicit Types u: vertex.

  Axiom get_weight: vertex -> vertex -> nat.

  Axiom set: forall {T}, nat -> vertex -> T -> nat.

  Axiom get: forall {T}, nat -> vertex -> T.

  Axiom take_shortest: list vertex -> nat -> vertex.

  Fixpoint remove Q v :=
    match Q with
    | [] => []
    | u :: us =>
      if vertex_eq_dec v u then
        us
      else
        u :: remove us v
      end.

  Lemma remove_In_decreases_length:
    forall Q v,
    In v Q ->
    length (remove Q v) < length Q.
  Proof with firstorder.
    induction Q; intros.
    - exfalso.
      inversion H.
    - simpl.
      destruct (vertex_eq_dec v a).
      + auto.
      + simpl.
        destruct H.
        * exfalso...
        * specialize (IHQ v H).
          lia.
  Qed.

  Axiom neighbors: list vertex -> vertex -> list vertex.

  Lemma take_shortest_In:
    forall Q d,
    In (take_shortest Q d) Q.
  Proof.
    admit.
  Admitted.

  (* Block b2... *)
  Fixpoint b2 Q V (d p: nat) u :=
    match V with
    | [] =>
      (d, p)
    | v :: V' =>
      (* Block b3... *)
      let alt := get d u + get_weight u v in
      if alt <? get d v then
        let d' := set d v alt in
        let p' := set p v u in
        b2 Q V' d' p' u
      else
        (* Continue the for loop. *)
        b2 Q V' d p u
    end.

  (* Block b0... *)
  Program Fixpoint b0 Q d p { measure (length Q) } :=
    if Q (* is empty... *) then
      (* Block b4... *)
      (d, p)
    else
      (* Block b1... *)
      let u := take_shortest Q d in
      let Q' := remove Q u in
      let V := neighbors Q u in
      let (d', p') := b2 Q' V d p u in
      b0 Q' d' p'.

  Next Obligation.
    apply remove_In_decreases_length.
    apply take_shortest_In.
  Defined.

End Dijkstra.