From DijkstraSpec Require Import nat_inf_type graph_specs.
Import NatInf.

Ltac solve_dijkstra :=
    unfold Dijkstra_Min_Weight;
    simpl; unfold Le_inf, Eq_inf, Lt_inf;
    repeat split; simpl; intuition.