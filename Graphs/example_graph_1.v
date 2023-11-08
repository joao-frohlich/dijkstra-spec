From DijkstraSpec Require Import nat_lists_extras nat_inf_type graph graph_functions impl graph_specs extra_tactics perm_paths.
Import Graph.
Import NatInf.

Definition example_graph_1 :=
    { 1, [(2, |4|); (3, |2|)] } &
    { 2, [(1, |1|)]} &
    { 3, [(2, |1|)]} &
    Empty.

Example example_graph_1_valid : Valid_Graph example_graph_1.
Proof.
    unfold example_graph_1, Valid_Graph.
    simpl; repeat split; auto.
Qed.

Example example_graph_1_get_paths_1_1_valid : (Get_Paths_Valid example_graph_1 1 1).
Proof. repeat split; (try apply example_graph_1_valid); simpl; auto. Qed.

Example example_graph_1_dijkstra_1_1 : (Dijkstra_Min_Weight example_graph_1 1 1).
Proof. solve_dijkstra. Qed.


Example example_graph_1_get_paths_1_2 : (Get_Paths_Valid example_graph_1 1 2).
Proof. repeat split; (try apply example_graph_1_valid); simpl; auto. Qed.

Example example_graph_1_dijkstra_1_2 : (Dijkstra_Min_Weight example_graph_1 1 2).
Proof. solve_dijkstra. Qed.


Example example_graph_1_get_paths_1_3 : (Get_Paths_Valid example_graph_1 1 3).
Proof. repeat split; (try apply example_graph_1_valid); simpl; auto. Qed.

Example example_graph_1_dijkstra_1_3 : (Dijkstra_Min_Weight example_graph_1 1 3).
Proof. solve_dijkstra. Qed.


Example example_graph_1_get_paths_2_1 : (Get_Paths_Valid example_graph_1 2 1).
Proof. repeat split; (try apply example_graph_1_valid); simpl; auto. Qed.

Example example_graph_1_dijkstra_2_1 : (Dijkstra_Min_Weight example_graph_1 2 1).
Proof. solve_dijkstra. Qed.


Example example_graph_1_get_paths_2_2 : (Get_Paths_Valid example_graph_1 2 2).
Proof. repeat split; (try apply example_graph_1_valid); simpl; auto. Qed.

Example example_graph_1_dijkstra_2_2 : (Dijkstra_Min_Weight example_graph_1 2 2).
Proof. solve_dijkstra. Qed.


Example example_graph_1_get_paths_2_3 : (Get_Paths_Valid example_graph_1 2 3).
Proof. repeat split; (try apply example_graph_1_valid); simpl; auto. Qed.

Example example_graph_1_dijkstra_2_3 : (Dijkstra_Min_Weight example_graph_1 2 3).
Proof. solve_dijkstra. Qed.


Example example_graph_1_get_paths_3_1 : (Get_Paths_Valid example_graph_1 3 1).
Proof. repeat split; (try apply example_graph_1_valid); simpl; auto. Qed.

Example example_graph_1_dijkstra_3_1 : (Dijkstra_Min_Weight example_graph_1 3 1).
Proof. solve_dijkstra. Qed.


Example example_graph_1_get_paths_3_2 : (Get_Paths_Valid example_graph_1 3 2).
Proof. repeat split; (try apply example_graph_1_valid); simpl; auto. Qed.

Example example_graph_1_dijkstra_3_2 : (Dijkstra_Min_Weight example_graph_1 3 2).
Proof. solve_dijkstra. Qed.


Example example_graph_1_get_paths_3_3 : (Get_Paths_Valid example_graph_1 3 3).
Proof. repeat split; (try apply example_graph_1_valid); simpl; auto. Qed.

Example example_graph_1_dijkstra_3_3 : (Dijkstra_Min_Weight example_graph_1 3 3).
Proof. solve_dijkstra. Qed.


Example example_graph_1_get_paths_invalid : (Get_Paths_Valid example_graph_1 1 4).
Proof. repeat split; (try apply example_graph_1_valid); simpl; auto. Qed.

Example example_graph_1_dijkstra_invalid : (Dijkstra_Min_Weight example_graph_1 1 4).
Proof. solve_dijkstra. Qed.