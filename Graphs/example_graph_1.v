From DijkstraSpec Require Import nat_lists_extras nat_inf_type graph graph_functions impl graph_specs extra_tactics perm_paths.
Import Graph.
Import NatInf.

Definition example_graph_1 :=
    { 1, [(2, |4|); (3, |2|)] } &
    { 2, [(1, |1|)]} &
    { 3, [(2, |1|)]} &
    Empty.

Compute (b0 example_graph_1 1).

Example example_graph_1_valid : Valid_Graph example_graph_1.
Proof.
    unfold example_graph_1, Valid_Graph.
    simpl; repeat split; auto.
Qed.

Example example_graph_1_get_paths_1_1_valid : (Get_Paths_Valid example_graph_1 1 1).
Proof. compute; intuition. Qed.

Example example_graph_1_get_paths_1_1_correct :
    Eq_Path_Set (get_paths example_graph_1 1 1) (generate_all_valid_graph_paths_from_o_to_d example_graph_1 1 1).
Proof. compute; auto. Qed.

Example example_graph_1_dijkstra_1_1 : (Dijkstra_Min_Weight example_graph_1 1 1).
Proof. compute; auto. Qed.


Example example_graph_1_get_paths_1_2_valid : (Get_Paths_Valid example_graph_1 1 2).
Proof. compute; intuition. Qed.

Example example_graph_1_get_paths_1_2_correct :
    Eq_Path_Set (get_paths example_graph_1 1 2) (generate_all_valid_graph_paths_from_o_to_d example_graph_1 1 2).
Proof. compute; auto. Qed.

Example example_graph_1_dijkstra_1_2 : (Dijkstra_Min_Weight example_graph_1 1 2).
Proof. compute; auto. Qed.


Example example_graph_1_get_paths_1_3_valid : (Get_Paths_Valid example_graph_1 1 3).
Proof. compute; intuition. Qed.

Example example_graph_1_get_paths_1_3_correct :
    Eq_Path_Set (get_paths example_graph_1 1 3) (generate_all_valid_graph_paths_from_o_to_d example_graph_1 1 3).
Proof. compute; auto. Qed.

Example example_graph_1_dijkstra_1_3 : (Dijkstra_Min_Weight example_graph_1 1 3).
Proof. compute; intuition. Qed.


Example example_graph_1_get_paths_2_1_valid : (Get_Paths_Valid example_graph_1 2 1).
Proof. compute; intuition. Qed.

Example example_graph_1_get_paths_2_1_correct :
    Eq_Path_Set (get_paths example_graph_1 2 1) (generate_all_valid_graph_paths_from_o_to_d example_graph_1 2 1).
Proof. compute; auto. Qed.

Example example_graph_1_dijkstra_2_1 : (Dijkstra_Min_Weight example_graph_1 2 1).
Proof. compute; intuition. Qed.


Example example_graph_1_get_paths_2_2_valid : (Get_Paths_Valid example_graph_1 2 2).
Proof. compute; intuition. Qed.

Example example_graph_1_get_paths_2_2_correct :
    Eq_Path_Set (get_paths example_graph_1 2 2) (generate_all_valid_graph_paths_from_o_to_d example_graph_1 2 2).
Proof. compute; auto. Qed.

Example example_graph_1_dijkstra_2_2 : (Dijkstra_Min_Weight example_graph_1 2 2).
Proof. compute; intuition. Qed.


Example example_graph_1_get_paths_2_3_valid : (Get_Paths_Valid example_graph_1 2 3).
Proof. compute; intuition. Qed.

Example example_graph_1_get_paths_2_3_correct :
    Eq_Path_Set (get_paths example_graph_1 2 3) (generate_all_valid_graph_paths_from_o_to_d example_graph_1 2 3).
Proof. compute; auto. Qed.

Example example_graph_1_dijkstra_2_3 : (Dijkstra_Min_Weight example_graph_1 2 3).
Proof. compute; intuition. Qed.


Example example_graph_1_get_paths_3_1_valid : (Get_Paths_Valid example_graph_1 3 1).
Proof. compute; intuition. Qed.

Example example_graph_1_get_paths_3_1_correct :
    Eq_Path_Set (get_paths example_graph_1 3 1) (generate_all_valid_graph_paths_from_o_to_d example_graph_1 3 1).
Proof. compute; auto. Qed.

Example example_graph_1_dijkstra_3_1 : (Dijkstra_Min_Weight example_graph_1 3 1).
Proof. compute; intuition. Qed.


Example example_graph_1_get_paths_3_2_valid : (Get_Paths_Valid example_graph_1 3 2).
Proof. compute; intuition. Qed.

Example example_graph_1_get_paths_3_2_correct :
    Eq_Path_Set (get_paths example_graph_1 3 2) (generate_all_valid_graph_paths_from_o_to_d example_graph_1 3 2).
Proof. compute; auto. Qed.

Example example_graph_1_dijkstra_3_2 : (Dijkstra_Min_Weight example_graph_1 3 2).
Proof. compute; intuition. Qed.

Example example_graph_1_get_paths_3_3_valid : (Get_Paths_Valid example_graph_1 3 3).
Proof. compute; intuition. Qed.

Example example_graph_1_get_paths_3_3_correct :
    Eq_Path_Set (get_paths example_graph_1 3 3) (generate_all_valid_graph_paths_from_o_to_d example_graph_1 3 3).
Proof. compute; auto. Qed.

Example example_graph_1_dijkstra_3_3 : (Dijkstra_Min_Weight example_graph_1 3 3).
Proof. compute; intuition. Qed.

Example example_graph_1_get_paths_invalid : (Get_Paths_Valid example_graph_1 1 5).
Proof. compute; intuition. Qed.

Example example_graph_1_get_paths_invalid_correct :
    Eq_Path_Set (get_paths example_graph_1 1 5) (generate_all_valid_graph_paths_from_o_to_d example_graph_1 1 5).
Proof. compute; auto. Qed.

Example example_graph_1_dijkstra_invalid : (Dijkstra_Min_Weight example_graph_1 1 5).
Proof. compute; intuition. Qed.