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
  Definition weight := nat.

  Variable edges: vertex -> vertex -> option weight.

  Hypothesis vertex_eq_dec:
    forall v u: vertex,
    { v = u } + { v <> u }.

  (* Source. *)
  Variable s: vertex.

  Set Implicit Arguments.
  Implicit Types Q: list vertex.
  Implicit Types u: vertex.

  Fixpoint get_weight edges u v :=
    match edges with
    | [] => 0
    | (u', v', w) :: edges' =>
      if vertex_eq_dec u u' then
        if vertex_eq_dec v v' then
          w
        else
          get_weight edges' u v
      else
        get_weight edges' u v
    end.

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


  (* 
Dijkstra(G, s)
    b0:
    for all u ∈ V,
        b1:
        d(u) <- ∞
    b2:
    d(s) <- 0
    R <- {}
    while R != V
        b3:
        u <- vertex not in R with smallest d(u)
        R <- insert u R
        b4:
        for all vertices v adjacent to u
            b5:
            alt <- d(u) + l(u, v)
            if d(v) > alt
                b6:
                d(v) <- alt
    b7:
    return d
  *)



  (* Block b4... *)
  Fixpoint b4 Q V (d: nat) u :=
    match V with
    | [] =>
      d
    | v :: V' =>
      (* Block b5... *)
      let alt := get d u + edges u v in
      if alt <? get d v then
        (* Block b6 *)
        let d' := set d v alt in
        b4 Q V' d' u
      else
        (* Continue the for loop. *)
        b4 Q V' d u
    end.

  (* Block b0... *)
  Program Fixpoint b3 V R  { measure (length V - lenght R) } :=
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