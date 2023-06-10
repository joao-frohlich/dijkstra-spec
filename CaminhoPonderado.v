From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section CaminhoPonderado.
    Variable T : finType.
    Variable φ : T -> T -> nat.

    Definition φ' (x y : T) :=
        if x == y then 0
        else φ x y.

    Fixpoint φ_C (c : seq T) : nat :=
        match c with
        | [::] => 0
        | x :: c' => φ' x (head x c') + φ_C c'
        end.
    
    Definition concat_caminho (x1 x2 : T) (s1 s2 C1 C2 : seq T) : seq T :=
        if (C1 == x1 :: s1) && (C2 == x2 :: s2)
            && (last x1 s1 == x2) then C1 ++ s2
        else [::].

    Lemma peso_caminho_positivo (c : seq T) : 0 <= φ_C c.
    Proof. by []. Qed.

    Lemma peso_cons_caminho (x : T) (c : seq T) :
        φ_C (x :: c) = φ' x (head x c) + φ_C (c).
    Proof. by []. Qed.

    Lemma peso_mesmo_vertice (x : T) : φ' x x = 0.
    Proof.
    unfold φ'.
    by rewrite eq_refl.
    Qed.

    Lemma peso_concat_seq (x1 x2 : T) (s1 s2 : seq T) :
        φ_C ((x1 :: s1) ++ (x2 :: s2)) = 
        φ_C (x1 :: s1) +  φ_C (x2 :: s2) + φ' (last x1 s1) x2.
    Proof.
    (* Simplificação inicial do teorema *)
    rewrite /=.
    (* Generalização da variável x1 e indução sobre a sequência s1 *)
    move: s1 x1; elim => [x1 | x1 s1 IH x1'].
        (* Caso base ([::]) *)
        by rewrite /= peso_mesmo_vertice addnC.
    (* Passo indutivo *)
    by rewrite /= IH !addnA.
    Qed.

    Lemma peso_concat_caminho (x1 x2 : T) (s1 s2 C1 C2 : seq T) :
        C1 = x1 :: s1 -> C2 = x2 :: s2 -> last x1 s1 == x2 ->
        φ_C (concat_caminho x1 x2 s1 s2 C1 C2) =
        φ_C C1 + φ_C C2.
    Proof.
    move => H1 H2 H3.
    (* Permitir a reescrita de H3 *)
    have H : last x1 s1 == x2 <-> last x1 s1 = x2.
        split.
        apply/eqP.
        by move => ->; rewrite eq_refl.
    (* Descartar a hipótese H *)
    apply H in H3.
    (* Simplificar concat_caminho para C1 ++ s2 *)
    unfold concat_caminho.
    rewrite -H1 -H2 H3 !eq_refl /=.
    rewrite H1 H2 cat_cons.
    (* Análise de caso sobre s2 *)
    move: H2; case: s2 => [H2 | x2' s2 H2].
        (* Caso s2 = [::] *)
        by rewrite cats0 /= peso_mesmo_vertice !addn0.
    (* Caso s2 = x2' :: s2' *)
    (* Remoção da concatenação pelo teorema peso_concat_seq *)
    rewrite peso_concat_seq.
    (* Manipulação da sequência de 2 ou mais elementos pelo teorema
    peso_cons_caminho *)
    rewrite [φ_C [:: x2, x2' & s2]]peso_cons_caminho.
    (* Manipulação da soma e aplicação da hipótese H3 *)
    rewrite addnCAC addnC addnA H3.
    (* Reescrita da associatividade da soma e finalização da prova *)
    by rewrite [in RHS]addnA.
    Qed.
    
End CaminhoPonderado.

    