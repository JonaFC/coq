(** Semántica y Verificación
    Ejemplo 4
    Manuel Soto Romero
    Luis F. Benítez Lluis 
    
    Contenido:
    1 Pares
      1.1 Ejercicios  de pares
    2 Listas de números 
	  	2.1 Definiciones básicas
	  	2.2 Cabeza y cola
		  2.3 Propiedades de concatenación y longitud
	  	2.4 Reversa y sus propiedades
  	3 Mas funciones sobre listas
	  	3.1 Cuenta de elementos
	  	3.2 Eliminación de elementos
	  	3.3 Subconjunto de listas y miembro
	  	3.4 Filtrado básico de listas
  	4 Función n-ésimo de listas y opciones
  	5 Diccionarios

    Para acceder rápidamente a la sección deseada
    buscar la cadena ">n" donde "n" es el número de
    sección. 
    
    Material basado en los scripts 
    correspondientes al libro Logical Foundations en
    Software Foundations- Benjamin C. Pierce, et al. 
    *)

Require Import Coq.Arith.PeanoNat.
Require Import Bool.Bool.


(** >1 Pares *)

Inductive natprod : Type :=
  | pair (n1 n2 : nat).

Check (pair 3 5) : natprod.

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Compute (fst (pair 3 5)).
(* ==> 3 *)

Notation "( x , y )" := (pair x y).

Compute (fst (3,5)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.

Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

(* Veamos también algunas propiedades: *)

Theorem pares1 : forall (n m :nat), (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity.
Qed.

Theorem pares2 : forall (p : natprod), p = (fst p, snd p).
Proof.
  simpl.
Abort.

Theorem pares2' : forall (p: natprod), p = (fst p, snd p).
Proof.
  intros p.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.

(** > 1.1 Ejercicios  de pares**)
Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
intros.
destruct p.
simpl.
reflexivity.
Qed.


Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
intros.
destruct p.
simpl.
reflexivity.
Qed.

(** [] *) 



(** >2 Listas de números *)
(** >2.1 Definiciones básicas*)
 
(* Usando la definición anterior de pares, podemos definir listas tal y como se hace en otros lenguajes de programación. *)

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Definition l1 := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l) (at level 60, right associativity).

Notation "[ ]" := nil.

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition l2 := 1 :: (2 :: (3 :: nil)).
Definition l3 := 1 :: 2 :: 3 :: nil.
Definition l4 := [1;2;3].

(*Funciones básicas*)
Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | 0 => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l : natlist) : nat :=
  match l with
  | nil => 0
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y) (right associativity, at level 60).

Example prueba_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example prueba_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example prueba_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

(** >2.2 Cabeza y cola*)
Definition hd (default : nat) (l : natlist)  :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example prueba_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example prueba_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example prueba_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

(** >2.3 Propiedades de concatenación y longitud*)
Theorem concat_vacia : forall l : natlist, [] ++ l = l.
Proof.
  reflexivity.
Qed.

Theorem cola_longitud_pred : forall l : natlist, pred (length l) = length (tl l).
Proof.
  intros l.
  destruct l as [| n l' ].
  - simpl. (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity.
Qed.

Theorem concat_asoc : forall l_1 l_2 l_3 : natlist, (l_1 ++ l_2) ++ l_3 = l_1 ++ (l_2 ++ l_3).
Proof.
 intros l_1 l_2 l_3.
 induction l_1 as [| n l' IHl1'].
 - (* l = nil *)
   reflexivity.
 - (* l = cons n l_1' *)
   simpl.
   rewrite -> IHl1'.
   reflexivity.
Qed.

(** 2.4 Reversa y sus propiedades*)
Fixpoint rev (l : natlist) : natlist :=
 match l with
 | nil => nil
 | h :: t => rev t ++ [h]
 end.

Example prueba_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example prueba_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Theorem rev_length_1 : forall l : natlist, length (rev l) = length l.
Proof.
 intros l.
 induction l as [| n l' IHl'].
 - (* l = nil *)
   reflexivity.
 - (* l = n :: l' *)
   simpl.
   rewrite <- IHl'.
   (* ???????? *)
Abort.

(* Para probar rev_length_1 necesitamos otro teorema. *)
Theorem concat_length: forall l_1 l_2 : natlist, 
 length (l_1 ++ l_2) = (length l_1) + (length l_2).
Proof.
 intros l_1 l_2.
 induction l_1 as [| n l_1' IHl1'].
 - reflexivity.
 - simpl. rewrite -> IHl1'. reflexivity.
Qed.

Theorem rev_length : forall l : natlist, length (rev l) = length l.
Proof.
 intros l.
 induction l as [| n l' IHl'].
 - (* l = nil *)
   reflexivity.
 - (* l = n :: l' *)
   simpl.
   rewrite -> concat_length.
   simpl.
   rewrite -> IHl'.
   rewrite -> Nat.add_comm.
   reflexivity.
Qed.


(** >3 Mas funciones sobre listas*)
(** >3.1 Cuenta de elementos*)
(* Función que cuenta las apariciones de un elemento en la lista*)
Fixpoint count (v : nat) (s : natlist) : nat:= 
  match s with 
    | [] => 0
    | h::t => if (v =? h) then S(count v t)
              else count v t 
  end.


Example test_count1:              
  count 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity. Qed.

Example test_count2:              
  count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed.

(** 3.2 Eliminación de elementos*)
(* Función que remueve la primera aprarición del elemento dado*)
Fixpoint remove_one (v : nat) (s : natlist) : natlist:=
 match s with 
  | []=> []
  | h::t => match (v=? h) with 
              | true => t
              | false => h:: (remove_one v t)
            end
 end.

 

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.

Compute (remove_one 5 [2;1;4;5;1;4]).

Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.

Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.
(* match s with
  | nil => nil
  | h::t => match ( v =? h ) with
          |true => t
          |false => h::(remove_one v t)
          end
  end. *)
  
  
(* Función que remueve todas las apariciones de un elemento dado*)
Fixpoint remove_all (v:nat) (s:natlist) : natlist:=
match s with 
  | []=> []
  | h::t => match (v=? h) with 
              | true => (remove_all v t)
              | false => h:: (remove_all v t)
            end
 end.


Example test_remove_all1:  count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all2:  count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all3:  count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_all4:  count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.

(** 3.3 Subconjunto de listas y miembros*)

Fixpoint member (v : nat) (s : natlist) : bool :=
  match s with 
    | [] => false 
    | h::t =>  match (v =? h) with
                | false => (member v t)
                | true => true
               end
    end.
Definition member' (v : nat) (s : natlist) : bool :=
  negb ((count v s)=? 0).

Example test_member1:             member 1 [1;4;1] = true.
Proof. reflexivity. Qed.

Example test_member2:             member 2 [1;4;1] = false.
Proof. reflexivity. Qed.

(* Función booleana que afirma si una lista es subconjunto 
  de otra contando repeticiones *)
Fixpoint subset (s1 : natlist) (s2 : natlist) : bool:=
  match s1 with 
  |[] => true
  | h::t=> if (member h s2) then (subset t (remove_one h s2)) 
          else false
end.

(* 
  (*match s1, s2 with 
    | [], _=> true
    | h::t , []=> false
    | h::t1, h::t2 => subset t1 t2
    | h1::t1, h2::t2 => false
  end.*) *)
Example test_subset1:              
  subset [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.
Example test_subset2:              
  subset [1;2;2] [2;1;4;1] = false.
Proof. reflexivity. Qed.


  
(** 3.4 Filtrado básico de listas*)
(*  Función que remueve todos los ceros*)

Print Nat.odd.
Print Nat.even.
Print Nat.Odd.
Print Nat.Even.
(* Función que obtiene todos los elementos impares. Hint usar Nat.odd*)
Fixpoint oddmembers (l:natlist) : natlist:=
match l with 
  | []=> []
  | h::t => match (Nat.odd h) with 
              | false => oddmembers t
              | true => h :: (oddmembers t)
            end
 end.
Fixpoint nonzeros (l:natlist) : natlist:=
match l with
  | [] => []
  | h::t => if (0 =? h) then nonzeros t else h::(nonzeros t)
end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.
Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.


Definition countoddmembers (l:natlist) : nat:=
 length (oddmembers l).

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.


Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.


Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof. reflexivity. Qed.

(* nonezeros abre concatenación*)
Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
intros.
induction l5.
- simpl. reflexivity.
- destruct n.
  + simpl. assumption.
  + simpl. rewrite IHl5. reflexivity.
  Qed.





Lemma oddmembers_app : forall l1 l2 : natlist,
  oddmembers (l1 ++ l2) = (oddmembers l1) ++ (oddmembers l2).
Proof.
intros.
induction l5.
- simpl. reflexivity.
- simpl. destruct (Nat.odd n).
-- simpl. rewrite IHl5. reflexivity.
-- simpl. rewrite IHl5.  reflexivity.
Qed.



(** >4 Función n-ésimo de listas y opciones*)

Fixpoint nesimo1 (l:natlist) (n:nat) : nat :=
  match l with
  | nil => 1
  | a :: l' => match n with
               | 0 => a
               | S n' => nesimo1 l' n'
               end
  end.
  
 Inductive natoption : Type :=
  | Some (n : nat)
  | None.
  
Fixpoint nesimo (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match n with
               | 0 => Some a
               | S n' => nesimo l' n'
               end
  end.

Example prueba_nesimo_1 : nesimo [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example prueba_nesimo_2 : nesimo [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example prueba_nesimo_3 : nesimo [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.


(** >5 Diccionarios*)
Inductive id : Type :=
  | Id (n : nat).

Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n_1, Id n_2 => n_1 =? n_2
  end.

Module Diccionarios.


Inductive diccionario : Type :=
  | empty
  | record (i : id) (v : nat) (m : diccionario).

Definition actualiza (d : diccionario) (x : id) (value : nat) : diccionario :=
  record x value d.

Fixpoint busca (x : id) (d : diccionario) : natoption :=
  match d with
  | empty => None
  | record y v d' => if eqb_id x y then
                        Some v
                     else
                        busca x d'
  end.  