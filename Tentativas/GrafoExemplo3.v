(* Usando definições do artigo do Martin Erwig sobre grafos indutivos: *)
(* https://web.engr.oregonstate.edu/~erwig/papers/InductiveGraphs_JFP01.pdf *)

From Coq Require Import Strings.String.
From Coq Require Export Bool.Bool.
From Coq Require Export Arith.Arith.
From Coq Require Export Arith.PeanoNat.
From Coq Require Export Unicode.Utf8.
From Coq Require Export Lia.
From Coq Require Export Lists.List.
Export ListNotations.

(* Funções e lemas auxiliares sobre listas de naturais *)

(* Verificação booleana da existência de um número natural *)
Fixpoint in_nat_list (l : list nat) (x : nat) :=
    match l with
    | [] => false
    | y :: l' => if x =? y then true else in_nat_list l' x
    end.

(* Equivalência entre in_nat_list e a definição indutiva In *)
Lemma in_nat_list_iff_In : forall (l : list nat) (x : nat),
    In x l <-> in_nat_list l x = true.
Proof.
    split.
    - intros.
      induction l; auto.
      simpl.
      destruct (x =? a) eqn:E; auto.
      apply IHl.
      simpl in H.
      destruct H.
      rewrite H in E.
      assert (x =? x = true).
      { apply Nat.eqb_eq; auto. }
      rewrite E in H0.
      discriminate H0.
      apply H.
    - intros.
      induction l.
      + inversion H.
      + simpl.
        inversion H.
        destruct (x =? a) eqn:E.
        * left.
          rewrite Nat.eqb_eq in E.
          auto.
        * apply IHl in H1.
          right.
          apply H1.
Qed.

(* Remover uma ocorrência de um dado número da lista*)
Fixpoint remove_nat_one (l : list nat) (x : nat) :=
    match l with
    | [] => []
    | h :: t => if h =? x then t else h :: (remove_nat_one t x)
    end.

(* Prova que se x está em l, então o tamanho de l é igual a
1 + tamanho da lista resultante da aplicação de remove_nat_one l x*)
Lemma remove_nat_one_length : forall (l : list nat) (x : nat),
    In x l -> length l = 1 + length (remove_nat_one l x).
Proof.
    intros.
    induction l.
    - inversion H.
    - simpl.
      destruct (a =? x) eqn:E; auto.
      simpl in H.
      destruct H; auto.
      rewrite H in E.
      assert (x =? x = true).
      { apply Nat.eqb_eq. auto. }
      rewrite E in H0.
      discriminate H0.
Qed.

(* Move um elemento x para a cabeça de uma lista l *)
Definition set_nat_head (l : list nat) (x : nat) :=
    if in_nat_list l x then x :: (remove_nat_one l x) else l.

(* Prova que a aplicação de set_nat_head mantem o tamanho da lista
inalterado *)
Lemma set_nat_head_same_length : forall (l : list nat) (x : nat),
    length l = length (set_nat_head l x).
Proof.
    intros.
    induction l; auto.
    simpl.
    unfold set_nat_head.
    destruct (in_nat_list (a :: l) x) eqn:E.
    - apply in_nat_list_iff_In in E.
      simpl in E.
      simpl.
      destruct E as [H | H].
      + destruct (a =? x) eqn:E; auto.
        rewrite H in E.
        apply Nat.eqb_neq in E.
        destruct E.
        auto.
      + destruct (a =? x) eqn:E; auto.
        simpl.
        rewrite <- remove_nat_one_length; auto.
    - auto.
Qed.

(* Definição de grafos como listas de adjacências *)
Definition Node := nat.
Definition Weight := nat.
Definition Adj := list (Node*Weight).
Inductive Context := 
    | mkcontext : Node -> Adj -> Context.

Inductive Graph :=
    | Empty : Graph
    | CGraph : Context -> Graph -> Graph.

Infix "&" := CGraph (at level 60, right associativity).

Definition empty_graph := Empty.

Definition example_graph_1 :=
    (mkcontext 1 [(3,4); (2,3)]) &
    (mkcontext 2 [(1,2)]) &
    (mkcontext 3 []) &
    Empty.

Definition is_empty g :=
    match g with
    | Empty => true
    | _ => false
    end.

Lemma empty_graph_is_empty : is_empty empty_graph = true.
Proof.
    auto.
Qed.


(* Função de mapeamento sobre grafos. Aplica uma função f sobre todos
os nós de um grafo g *)
Fixpoint graph_map (f : Context -> Context) (g : Graph) :=
    match g with
    | Empty => Empty
    | c & g' => f c & (graph_map f g')
    end.

Lemma graph_map_compose : forall (f f' : Context -> Context) (g : Graph),
    (forall c : Context, f' (f c) = f (f' c)) ->
    graph_map f (graph_map f' g) = graph_map f' (graph_map f g).
Proof.
    intros.
    induction g; auto.
    simpl.
    rewrite IHg.
    rewrite H.
    auto.
Qed.

Fixpoint get_node_context (g : Graph) (u : Node) : option Context :=
  match g with
  | Empty => None
  | (mkcontext n s) & g' =>
    if n =? u then
      Some (mkcontext n s)
    else
      get_node_context g' u
  end.

Fixpoint get_nodes (g : Graph) : list Node :=
  match g with
  | Empty => []
  | (mkcontext n _) & g' => n :: (get_nodes g')
  end.

(* Função de inserção de nó. Um nó é adicionado sem nenhuma aresta, e apenas é adicionado se ele não existe no grafo *)
Definition add_node (g : Graph) (x : Node) :=
    match get_node_context g x with
    | None => (mkcontext x []) & g
    | Some _ => g
    end.

(* Função para adicionar uma aresta. Ela adiciona o par (w,v) na
lista de adjacência do nó u *)
Fixpoint add_edge' (g : Graph) (o d : Node) (p : Weight) :=
  match g with
  | Empty => Empty
  | (mkcontext n s) & g' =>
    if o =? n then (mkcontext n ((d,p) :: s)) & g'
    else (mkcontext n s) & add_edge' g' o d p
  end.

Definition add_edge (g : Graph) (o d : Node) (p : Weight) :=
  add_edge' (add_node (add_node g o) d) o d p.

Fixpoint add_edges (g : Graph) (l : list (Node*Node*Weight)) :=
  match l with
  | [] => g
  | (o,d,p) :: l' => add_edges (add_edge g o d p) l'
  end.

Definition grafo_exemplo_2 :=
  add_edges Empty [(1,2,6); (1,3,3); (2,1,1); (3,2,2)].

Compute grafo_exemplo_2.

(* Pega todos os nós de uma lista de adjacência que estejam contidos
numa lista de nós *)
Fixpoint get_elem_in_list (a : Adj) (b : list Node) :=
    match a with
    | [] => []
    | (h, _) :: t => if in_nat_list b h then h :: get_elem_in_list t b else get_elem_in_list t b
    end.


Require Import Coq.Program.Wf. (* for lt_wf *)

(* Implementação do algoritmo de DFS. A implementação é feita usando um Program Fixpoint,
com uma demonstração que a lista to_vis decresce a cada chamada recursiva.

Para a função são passados os parâmetros:
- g: o grafo de entrada
- u: o vértice atual
- d: o vértice destino
- to_vis: uma lista de vértices a serem visitados

A primeira verificação checa se o vértice atual é igual ao vértice destino

Se não for, são definidas uma lista auxiliar, to_vis', que move o nó atual para a frente da lista de
vértices a serem visitados; uma lista auxiliar, suc, que contém os sucessores do nó atual que ainda
não foram visitados; e uma função auxiliar, aux, que dado um vértice x, chama a função dfs' recursivamente
removendo o nó atual (movido para a frente da lista de vértices a serem visitados na função to_vis') da
lista de vértices a serem visitados

O resultado da função se dá por meio de uma função de fold_left, cujo valor padrão é false, a operação é
um ou, e a lista de valores é o resultado do mapeamento da função aux sobre a lista suc.

Por fim, {measure (length to_vis)} gera a necessidade de provar que o tamanho de t, que é obtida por
meio de pattern matching da lista to_vis' quando to_vis' não é vazia, representando a cauda de
to_vis', é estritamente menor que o tamanho de to_vis.

Isso é verdade porque to_vis' tem o mesmo tamanho de to_vis, o que pode ser provado pelo lema
set_nat_head_same_length.
*)
Program Fixpoint dfs' (g : Graph) (u d : Node) (to_vis : list Node) {measure (length to_vis)} : bool :=
  (* Verifica se o nó atual é o mesmo nó que está sendo procurado pela busca *)
  if u =? d then true
  else
    (* Move o nó atual da busca para a frente de nós a serem visitados *)
    let (* 1 *) to_vis' := 
      set_nat_head to_vis u
    in
    (* Salva a lista de nós a serem visitados a partir do nó atual. Só são considerados nós que ainda
    não foram visitados *)
    let (* 2 *) suc := match (get_node_context g u) with
      | None => []
      | Some (mkcontext _ s) => get_elem_in_list s to_vis
    end in
    (* Função auxiliar para chamar a função dfs' recursivamente, pois a necessidade de especificar um
    nó x impede que isso seja feito na função fold_left *)
    let (* 3 *) aux (x : Node) :=
      match (* 1' *) to_vis' with
      | [] => false
      | h :: t => (dfs' g x d t)
      end
    in
    (* Aplicação da função dfs' sobre todos os sucessores do nó atual *)
    fold_left orb (map (* 3' *) aux (* 2' *) suc) false.
Next Obligation.
Proof.
  rename Heq_to_vis' into H.
  unfold set_nat_head in H.
  destruct (in_nat_list to_vis u) eqn:E in H.
  - injection H.
    apply in_nat_list_iff_In in E.
    intros H1 H2.
    rewrite H1.
    unfold lt.
    rewrite <- remove_nat_one_length; auto.
  - rewrite <- H. auto.
Qed.


(* Simplificação da chamada da função de DFS *)
(* Definition dfs (g: Graph) (o d : Node) := 
  match g with
  | Empty => false
  | _ => dfs' g o d (get_nodes g)
  end. *)

Definition dfs (g : Graph) (o d : Node) :=
  dfs' g o d (get_nodes g).

(* Exemplo da execução da função de DFS sobre o grafo de exemplo 1 *)
Compute (dfs example_graph_1 1 2).

Example foo : forall (g : Graph) (o : Node), 
  g <> Empty -> dfs g o o = true.
Proof.
  intros. induction g.
  - destruct H; auto.
  - unfold dfs, dfs'.
    unfold dfs'_func; simpl; rewrite fix_sub_eq; simpl.
    + assert (o =? o = true) by (rewrite Nat.eqb_eq; auto); rewrite H0; auto.
    + unfold projT1, projT2.
      intros x f1 f2 Heq.
      destruct x, s, s.
      destruct (x0 =? x1); auto.
      repeat f_equal.
      

  (* - unfold dfs, get_nodes; simpl.
    unfold dfs', dfs'_func; simpl; rewrite fix_sub_eq; simpl.
    + assert (o =? o = true) by (rewrite Nat.eqb_eq; auto); rewrite H; auto.
    + intros x f g Heq.
      destruct x.
      destruct s.
      destruct s.
      destruct (x0 =? x1).
      * auto.
      * repeat f_equal.
        exists (mkcontext ()). *)
Admitted.

(* 
Exemplo de prova sobre Program Fixpoint
Program Fixpoint bla (n:nat) {measure n} :=
match n with
| 0 => 0
| S n' => S (bla n')
end.

Lemma obv : forall n, bla n = n.
Proof.
  intros n. induction n.
  - reflexivity.
  - unfold bla; rewrite fix_sub_eq; simpl; fold (bla n).
    rewrite IHn; reflexivity.
    intros x f g Heq.
    destruct x.
    + reflexivity.
    + f_equal. apply Heq.
Qed.
*)

Fixpoint get_node_dist (dist : list (Node*Weight)) (u : Node) (inf : Weight) : Weight :=
  match dist with
  | [] => inf
  | (u',w) :: dist' => if u =? u' then w else get_node_dist dist' u inf
  end.

Fixpoint update_node_dist (dist : list(Node*Weight)) (u : Node) (w : Weight) : list(Node*Weight) :=
  match dist with
  | [] => []
  | (u', w') :: dist' => if u =? u' then (u,w) :: dist' else (u',w') :: update_node_dist dist' u w
  end.

Fixpoint get_edges_in_list (a : Adj) (b : list Node) :=
  match a with
  | [] => []
  | (v,w) :: t => if in_nat_list b v then (v, w) :: get_edges_in_list t b else get_edges_in_list t b
  end.

Fixpoint min_weight_in_list (dist : list(Node*Weight)) (l : list Node) (inf : Weight) : Weight :=
  match dist with
  | [] => inf
  | (u,w) :: t => let md := min_weight_in_list t l inf in
                  if in_nat_list l u then
                    if w <? md then w else md
                  else md
  end.

Fixpoint node_with_min_weight_in_list (dist : list(Node*Weight)) (l : list Node) (w : Weight) :=
  match dist with
  | [] => None
  | (u,w') :: t =>  if in_nat_list l u then
                      if w =? w' then
                        Some u
                      else
                        node_with_min_weight_in_list t l w
                    else
                      node_with_min_weight_in_list t l w
  end.

Definition next_node (dist : list(Node*Weight)) (to_vis : list Node) (inf : Weight) :=
  node_with_min_weight_in_list dist to_vis (min_weight_in_list dist to_vis inf).

(* Fixpoint fold_list_left (f : ()) (l : list (Node*Weight)) *)

Program Fixpoint dijkstra' (g : Graph) (u d : Node) (inf : Weight)
  (to_vis : list Node) (dist : list (Node*Weight)) {measure (length to_vis)} : Weight :=
  let ret := 
    get_node_dist dist d inf
  in
  if u =? d then ret
  else
    let to_vis' :=
      set_nat_head to_vis u
    in
    let suc := match (get_node_context g u) with
      | None => []
      | Some (mkcontext _ s) => get_edges_in_list s to_vis
    end in
    let relax (dist : list (Node*Weight)) (n : (Node*Weight)) : list (Node*Weight) :=
      let v := (fst n) in
      let w := (snd n) in
      let new_dist := 
        (get_node_dist dist u inf) + w
      in
      if (new_dist) <? (get_node_dist dist v inf) then
        update_node_dist dist v new_dist
      else
        dist
    in
    let new_dist_list : list (Node*Weight) :=
      fold_left (relax) suc dist
    in
    match to_vis' with
      | [] => ret
      | h :: t => match (next_node new_dist_list t inf) with
        | None => ret
        | Some v => dijkstra' g v d inf t new_dist_list
      end
    end.
Next Obligation.
Proof.
  rename Heq_to_vis' into H.
  unfold set_nat_head in H.
  destruct (in_nat_list to_vis u) eqn:E in H.
  - injection H.
    apply in_nat_list_iff_In in E.
    intros H1 H2.
    rewrite H1.
    unfold lt.
    rewrite <- remove_nat_one_length; auto.
  - rewrite <- H. auto.
Qed.

Fixpoint sum_adj_weight (a : Adj) :=
  match a with
  | [] => 0
  | (_,w) :: a' => w + sum_adj_weight a'
  end.

Fixpoint sum_weights (g : Graph) : Weight :=
  match g with
  | Empty => 0
  | c & g => match c with
    | mkcontext _ a => (sum_adj_weight a) + sum_weights g
    end
  end.

Definition dijkstra (g : Graph) (o d : Node) : Weight :=
  let inf :=
    sum_weights g
  in
  let dist :=
    (combine (get_nodes g) (repeat inf (length (get_nodes g))))
  in
  dijkstra' g o d inf (get_nodes g) (update_node_dist dist o 0).

Definition example_graph_2 :=
  (mkcontext 1 [(3,4); (2,1)]) &
  (mkcontext 2 [(3,2); (1,1)]) &
  (mkcontext 3 [(2,1)]) &
  Empty.

Compute dijkstra example_graph_2 1 3.

Lemma dijkstra_o_o_0 : forall (g : Graph) (o : Node),
  In o (get_nodes g) -> dijkstra g o o = 0.
Proof.
  intros.
  unfold dijkstra.
  induction g.
  - destruct H.
  - simpl.
    destruct c.
    simpl in H.
    destruct H.
    + simpl.
      rewrite H.
      destruct (o =? o) eqn:E.
      * unfold get_nodes.
        simpl.
        unfold dijkstra'.
        unfold dijkstra'_func.
        simpl.
        unfold projT1, projT2.
        unfold get_node_dist.
        unfold dijkstra'_func_obligation_2.
        unfold projT2.
        simpl.
      * rewrite Nat.eqb_neq in E. contradiction.
    +  
        
    