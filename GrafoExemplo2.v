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
Definition Adj := list (Weight*Node).
Inductive Context := 
    | mkcontext : Node -> Adj -> Context.

Inductive Graph :=
    | Empty : Graph
    | CGraph : Context -> Graph -> Graph.

Infix "&" := CGraph (at level 60, right associativity).

Definition empty_graph := Empty.

Definition example_graph_1 :=
    (mkcontext 1 [(4,3); (3,2)]) &
    (mkcontext 2 [(2,1)]) &
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

(* Função de inserção de nó. Um nó é adicionado sem nenhuma aresta *)
Definition add_node (g : Graph) (x : Node) :=
    (mkcontext x []) & g.


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

(* Realiza um fold sobre todos os nós de um grafo *)
Fixpoint ufold (A : Type) (f : Context -> A -> A) (d : A) (g : Graph) : A :=
    match g with
    | Empty => d
    | c & g => f c (ufold A f d g)
    end.

Definition get_node (c : Context) (l' : list nat) :=
    match c with
    | (mkcontext n s) => n :: l'
    end.

Fixpoint get_node_context (g : Graph) (u : Node) : option Context :=
    match g with
    | Empty => None
    | (mkcontext n s) & g' => if n =? u then Some (mkcontext n s) else get_node_context g' u
    end.

(* Pega o conjunto de nós de um grafo *)
Definition nodes (g : Graph) : list Node := ufold (list nat) get_node [] g.

(* Função para adicionar uma aresta. Ela adiciona o par (w,v) na
lista de adjacência do nó u *)
Fixpoint add_edge' (g : Graph) (u v : Node) (w : nat) :=
    match g with
    | Empty => Empty
    | (mkcontext n s) & g' =>
        if u =? n then (mkcontext n ((w,v) :: s)) & g'
        else (mkcontext n s) & add_edge' g' u v w
    end.

Definition add_edge (g : Graph) (u v : Node) (w : nat) :=
    let N := nodes g in
        if in_nat_list N u then
            if in_nat_list N v then
                add_edge' g u v w
            else g
        else g.

(* Pega todos os nós de uma lista de adjacência que estejam contidos
numa lista de nós *)
Fixpoint get_elem_in_list (a : Adj) (b : list Node) :=
    match a with
    | [] => []
    | (_, h) :: t => if in_nat_list b h then h :: get_elem_in_list t b else get_elem_in_list t b
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
  if u =? d then true
  else
    let to_vis' := 
      set_nat_head to_vis u
    in
    let suc := match (get_node_context g u) with
      | None => []
      | Some (mkcontext _ s) => get_elem_in_list s to_vis
    end in
    let aux (x : Node) :=
      match to_vis' with
      | [] => false
      | h :: t => (dfs' g x d t)
      end
    in
    fold_left orb (map aux suc) false.
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
Definition dfs (g: Graph) (o d : Node) := dfs' g o d (nodes g).

(* Exemplo da execução da função de DFS sobre o grafo de exemplo 1 *)
Compute (dfs example_graph_1 1 2).

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
  | (w, v) :: t => if in_nat_list b v then (v, w) :: get_edges_in_list t b else get_edges_in_list t b
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
    let relax (n : (Node*Weight)) :=
      let v := (fst n) in
      let w := (snd n) in
      let new_dist := 
        (get_node_dist dist u inf) + w
      in
      if (new_dist) <? (get_node_dist dist v inf) then update_node_dist dist v new_dist else dist
    in
    let new_dist_list : list (Node*Weight) :=
      dist
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
