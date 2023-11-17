import qualified Prelude

false_rect :: a1
false_rect =
  Prelude.error "absurd case"

data Bool =
   True
 | False

data Nat =
   O
 | S Nat
  deriving Prelude.Show

nat_rect :: a1 -> (Nat -> a1 -> a1) -> Nat -> a1
nat_rect f f0 n =
  case n of {
   O -> f;
   S n0 -> f0 n0 (nat_rect f f0 n0)}

nat_rec :: a1 -> (Nat -> a1 -> a1) -> Nat -> a1
nat_rec =
  nat_rect

data Option a =
   Some a
 | None

data Prod a b =
   Pair a b
   deriving Prelude.Show

data List a =
   Nil
 | Cons a (List a)
  deriving Prelude.Show

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
data SigT a p =
   ExistT a p

proj1_sig :: a1 -> a1
proj1_sig e0 =
  e0

projT1 :: (SigT a1 a2) -> a1
projT1 x =
  case x of {
   ExistT a _ -> a}

projT2 :: (SigT a1 a2) -> a2
projT2 x =
  case x of {
   ExistT _ h -> h}

data Sumbool =
   Left
 | Right

add :: Nat -> Nat -> Nat
add n m =
  case n of {
   O -> m;
   S p -> S (add p m)}

leb :: Nat -> Nat -> Bool
leb n m =
  case n of {
   O -> True;
   S n' -> case m of {
            O -> False;
            S m' -> leb n' m'}}

ltb :: Nat -> Nat -> Bool
ltb n m =
  leb (S n) m

eq_dec :: Nat -> Nat -> Sumbool
eq_dec n =
  nat_rec (\m -> case m of {
                  O -> Left;
                  S _ -> Right}) (\_ iHn m ->
    case m of {
     O -> Right;
     S n0 -> iHn n0}) n

type Assoc_list t u = List (Prod t u)

lookup :: (a1 -> a1 -> Sumbool) -> (List (Prod a1 a2)) -> a1 -> Option a2
lookup t_eq_dec al key =
  case al of {
   Nil -> None;
   Cons y cdr ->
    case y of {
     Pair t u ->
      case t_eq_dec key t of {
       Left -> Some u;
       Right -> lookup t_eq_dec cdr key}}}

delete_key :: (a1 -> a1 -> Sumbool) -> (List (Prod a1 a2)) -> a1 ->
              Assoc_list a1 a2
delete_key t_eq_dec al key =
  case al of {
   Nil -> Nil;
   Cons y cdr ->
    case y of {
     Pair t u ->
      case t_eq_dec key t of {
       Left -> delete_key t_eq_dec cdr key;
       Right -> Cons (Pair t u) (delete_key t_eq_dec cdr key)}}}

get_weight :: (a1 -> a1 -> Option Nat) -> a1 -> a1 -> Nat
get_weight e0 v0 u =
  case e0 v0 u of {
   Some n -> n;
   None -> O}

type Distance vertex = Assoc_list vertex Nat

set :: (a1 -> a1 -> Sumbool) -> (List (Prod a1 Nat)) -> a1 -> Nat -> Distance
       a1
set vertex_eq_dec d v0 n =
  Cons (Pair v0 n) (delete_key vertex_eq_dec d v0)

get :: (a1 -> a1 -> Sumbool) -> (Distance a1) -> a1 -> Nat -> Nat
get vertex_eq_dec d v0 w =
  case lookup vertex_eq_dec d v0 of {
   Some x -> x;
   None -> w}

take_shortest_func :: (a1 -> a1 -> Sumbool) -> (SigT (List a1) (Distance a1))
                      -> a1
take_shortest_func vertex_eq_dec x =
  let {q = projT1 x} in
  let {d = proj1_sig (projT2 x)} in
  let {
   take_shortest0 = \q0 d0 ->
    let {y = ExistT q0 d0} in take_shortest_func vertex_eq_dec (proj1_sig y)}
  in
  case q of {
   Nil -> false_rect;
   Cons v0 q' ->
    case q' of {
     Nil -> v0;
     Cons u wildcard' ->
      let {q'0 = Cons u wildcard'} in
      let {u' = take_shortest0 q'0 d} in
      let {
       filtered_var = Pair (lookup vertex_eq_dec d v0)
        (lookup vertex_eq_dec d u')}
      in
      case filtered_var of {
       Pair wildcard'0 o ->
        case wildcard'0 of {
         Some x0 ->
          case o of {
           Some y -> case ltb x0 y of {
                      True -> v0;
                      False -> u'};
           None -> v0};
         None -> case o of {
                  Some _ -> u';
                  None -> v0}}}}}

take_shortest :: (a1 -> a1 -> Sumbool) -> (List a1) -> (Distance a1) -> a1
take_shortest vertex_eq_dec q d =
  take_shortest_func vertex_eq_dec (ExistT q d)

remove :: (a1 -> a1 -> Sumbool) -> (List a1) -> a1 -> List a1
remove vertex_eq_dec q v0 =
  case q of {
   Nil -> Nil;
   Cons u us ->
    case vertex_eq_dec v0 u of {
     Left -> us;
     Right -> Cons u (remove vertex_eq_dec us v0)}}

neighbors :: (a1 -> a1 -> Option Nat) -> (List a1) -> a1 -> List a1
neighbors e0 q u =
  case q of {
   Nil -> Nil;
   Cons v0 q' ->
    case e0 u v0 of {
     Some _ -> Cons v0 (neighbors e0 q' u);
     None -> neighbors e0 q' u}}

b2 :: (a1 -> a1 -> Option Nat) -> (a1 -> a1 -> Sumbool) -> (List a1) ->
      (Distance a1) -> a1 -> Distance a1
b2 e0 vertex_eq_dec n d u =
  case n of {
   Nil -> d;
   Cons v0 n' ->
    let {alt = add (get vertex_eq_dec d u O) (get_weight e0 u v0)} in
    case ltb alt (get vertex_eq_dec d v0 (add (S O) alt)) of {
     True ->
      let {d' = set vertex_eq_dec d v0 alt} in b2 e0 vertex_eq_dec n' d' u;
     False -> b2 e0 vertex_eq_dec n' d u}}

b0_func :: (List a1) -> (a1 -> a1 -> Option Nat) -> a1 -> (a1 -> a1 ->
           Sumbool) -> (SigT (List a1) (Distance a1)) -> Distance a1
b0_func v0 e0 s vertex_eq_dec x =
  let {q = projT1 x} in
  let {d = projT2 x} in
  let {
   b1 = \q0 d0 ->
    let {y = ExistT q0 d0} in b0_func v0 e0 s vertex_eq_dec (proj1_sig y)}
  in
  case q of {
   Nil -> d;
   Cons _ _ ->
    let {u = take_shortest vertex_eq_dec q d} in
    let {q' = remove vertex_eq_dec q u} in
    case lookup vertex_eq_dec d u of {
     Some _ ->
      let {n = neighbors e0 q' u} in
      let {d' = b2 e0 vertex_eq_dec n d u} in b1 q' d';
     None -> b1 q' d}}

b0 :: (List a1) -> (a1 -> a1 -> Option Nat) -> a1 -> (a1 -> a1 -> Sumbool) ->
      (List a1) -> (Distance a1) -> Distance a1
b0 v0 e0 s vertex_eq_dec q d =
  b0_func v0 e0 s vertex_eq_dec (ExistT q d)

dijkstra :: (List a1) -> (a1 -> a1 -> Option Nat) -> a1 -> (a1 -> a1 ->
            Sumbool) -> Distance a1
dijkstra v0 e0 s vertex_eq_dec =
  b0 v0 e0 s vertex_eq_dec v0 (Cons (Pair s O) Nil)

v :: List Nat
v =
  Cons (S O) (Cons (S (S O)) (Cons (S (S (S O))) (Cons (S (S (S (S O))))
    Nil)))

e :: Nat -> Nat -> Option Nat
e v0 u =
  case v0 of {
   O -> None;
   S n1 ->
    case n1 of {
     O ->
      case u of {
       O -> None;
       S n2 ->
        case n2 of {
         O -> None;
         S n3 ->
          case n3 of {
           O -> Some (S (S (S (S O))));
           S n4 ->
            case n4 of {
             O -> Some (S (S (S O)));
             S n5 -> case n5 of {
                      O -> Some (S (S O));
                      S _ -> None}}}}};
     S n2 ->
      case n2 of {
       O ->
        case u of {
         O -> None;
         S n3 -> case n3 of {
                  O -> Some (S (S O));
                  S _ -> None}};
       S n3 ->
        case n3 of {
         O ->
          case u of {
           O -> None;
           S n4 ->
            case n4 of {
             O -> None;
             S n5 ->
              case n5 of {
               O -> Some (S O);
               S n6 ->
                case n6 of {
                 O -> None;
                 S n7 ->
                  case n7 of {
                   O -> Some (S (S (S (S (S (S (S (S (S O)))))))));
                   S _ -> None}}}}};
         S _ -> None}}}}

example :: Distance Nat
example =
  dijkstra v e (S O) eq_dec


