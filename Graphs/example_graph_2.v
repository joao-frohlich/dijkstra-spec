From DijkstraSpec Require Import nat_lists_extras nat_inf_type graph graph_functions impl graph_specs extra_tactics.
Import Graph.
Import NatInf.

Definition example_graph_2 :=
    { 1, [(2, |3|); (3, |1|); (4, |5|)] } &
    { 2, [(3, |5|)]} &
    { 3, [(2, |1|)]} &
    { 4, [] } &
    Empty.

Example example_graph_2_valid : Valid_Graph example_graph_2.
Proof.
    unfold example_graph_2, Valid_Graph.
    simpl; repeat split; auto.
Qed.

Example example_graph_2_get_paths_1_1_valid : (Get_Paths_Valid example_graph_2 1 1).
Proof. repeat split; simpl; auto; (try apply example_graph_2_valid). Qed.

Example example_graph_2_dijkstra_1_1 : (Dijkstra_Min_Weight example_graph_2 1 1).
Proof. solve_dijkstra. Qed.


Example example_graph_2_get_paths_1_2 : (Get_Paths_Valid example_graph_2 1 2).
Proof. repeat split; simpl; auto; (try apply example_graph_2_valid). Qed.

Example example_graph_2_dijkstra_1_2 : (Dijkstra_Min_Weight example_graph_2 1 2).
Proof. solve_dijkstra. Qed.


Example example_graph_2_get_paths_1_3 : (Get_Paths_Valid example_graph_2 1 3).
Proof. repeat split; simpl; auto; (try apply example_graph_2_valid). Qed.

Example example_graph_2_dijkstra_1_3 : (Dijkstra_Min_Weight example_graph_2 1 3).
Proof. solve_dijkstra. Qed.


Example example_graph_2_get_paths_1_4 : (Get_Paths_Valid example_graph_2 1 4).
Proof. repeat split; simpl; auto; (try apply example_graph_2_valid). Qed.

Example example_graph_2_dijkstra_1_4 : (Dijkstra_Min_Weight example_graph_2 1 4).
Proof. solve_dijkstra. Qed.


Example example_graph_2_get_paths_2_1 : (Get_Paths_Valid example_graph_2 2 1).
Proof. repeat split; simpl; auto; (try apply example_graph_2_valid). Qed.

Example example_graph_2_dijkstra_2_1 : (Dijkstra_Min_Weight example_graph_2 2 1).
Proof. solve_dijkstra. Qed.


Example example_graph_2_get_paths_2_2 : (Get_Paths_Valid example_graph_2 2 2).
Proof. repeat split; simpl; auto; (try apply example_graph_2_valid). Qed.

Example example_graph_2_dijkstra_2_2 : (Dijkstra_Min_Weight example_graph_2 2 2).
Proof. solve_dijkstra. Qed.


Example example_graph_2_get_paths_2_3 : (Get_Paths_Valid example_graph_2 2 3).
Proof. repeat split; simpl; auto; (try apply example_graph_2_valid). Qed.

Example example_graph_2_dijkstra_2_3 : (Dijkstra_Min_Weight example_graph_2 2 3).
Proof. solve_dijkstra. Qed.


Example example_graph_2_get_paths_2_4 : (Get_Paths_Valid example_graph_2 2 4).
Proof. repeat split; simpl; auto; (try apply example_graph_2_valid). Qed.

Example example_graph_2_dijkstra_2_4 : (Dijkstra_Min_Weight example_graph_2 2 4).
Proof. solve_dijkstra. Qed.


Example example_graph_2_get_paths_3_1 : (Get_Paths_Valid example_graph_2 3 1).
Proof. repeat split; simpl; auto; (try apply example_graph_2_valid). Qed.

Example example_graph_2_dijkstra_3_1 : (Dijkstra_Min_Weight example_graph_2 3 1).
Proof. solve_dijkstra. Qed.


Example example_graph_2_get_paths_3_2 : (Get_Paths_Valid example_graph_2 3 2).
Proof. repeat split; simpl; auto; (try apply example_graph_2_valid). Qed.

Example example_graph_2_dijkstra_3_2 : (Dijkstra_Min_Weight example_graph_2 3 2).
Proof. solve_dijkstra. Qed.


Example example_graph_2_get_paths_3_3 : (Get_Paths_Valid example_graph_2 3 3).
Proof. repeat split; simpl; auto; (try apply example_graph_2_valid). Qed.

Example example_graph_2_dijkstra_3_3 : (Dijkstra_Min_Weight example_graph_2 3 3).
Proof. solve_dijkstra. Qed.


Example example_graph_2_get_paths_3_4 : (Get_Paths_Valid example_graph_2 3 4).
Proof. repeat split; simpl; auto; (try apply example_graph_2_valid). Qed.

Example example_graph_2_dijkstra_3_4 : (Dijkstra_Min_Weight example_graph_2 3 4).
Proof. solve_dijkstra. Qed.


Example example_graph_2_get_paths_4_1 : (Get_Paths_Valid example_graph_2 4 1).
Proof. repeat split; simpl; auto; (try apply example_graph_2_valid). Qed.

Example example_graph_2_dijkstra_4_1 : (Dijkstra_Min_Weight example_graph_2 4 1).
Proof. solve_dijkstra. Qed.


Example example_graph_2_get_paths_4_2 : (Get_Paths_Valid example_graph_2 4 2).
Proof. repeat split; simpl; auto; (try apply example_graph_2_valid). Qed.

Example example_graph_2_dijkstra_4_2 : (Dijkstra_Min_Weight example_graph_2 4 2).
Proof. solve_dijkstra. Qed.


Example example_graph_2_get_paths_4_3 : (Get_Paths_Valid example_graph_2 4 3).
Proof. repeat split; simpl; auto; (try apply example_graph_2_valid). Qed.

Example example_graph_2_dijkstra_4_3 : (Dijkstra_Min_Weight example_graph_2 4 3).
Proof. solve_dijkstra. Qed.


Example example_graph_2_get_paths_4_4 : (Get_Paths_Valid example_graph_2 4 4).
Proof. repeat split; simpl; auto; (try apply example_graph_2_valid). Qed.

Example example_graph_2_dijkstra_4_4 : (Dijkstra_Min_Weight example_graph_2 4 4).
Proof. solve_dijkstra. Qed.


Example example_graph_2_get_paths_invalid : (Get_Paths_Valid example_graph_2 1 5).
Proof. repeat split; simpl; auto; (try apply example_graph_2_valid). Qed.

Example example_graph_2_dijkstra_invalid : (Dijkstra_Min_Weight example_graph_2 1 5).
Proof. solve_dijkstra. Qed.
