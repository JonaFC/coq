[`Introducción a la Verificación Formal con Coq`](../README.md) > `Tema 4`

## Estructuras de Datos

### Pares de números

En las definiciones inductivas, cada constructor puede tomar cualquier números de argumentos. Además, las notaciones que
definimos pueden usarse pefectamente con la técnica de reconocimiento de patrones. Por ejemplo:

```coq
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

Compute (fst (pair 3 5))
(* ==> 3 *)

Notation "( x , y )" := (pair x y)

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
```

Veamos también algunas propiedades:

```coq
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
Qued.
```

### Listas de números

Usando la definición anterior de pares, podemos definir listas tal y como se hace en otros lenguajes de programación.

```coq
Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Definition l1 = cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l) (at level 60, right associativity).

Notation "[ ]" := nil.

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition l2 := 1 :: (2 :: (3 :: nil)).
Definition l3 := 1 :: 2 :: 3 :: nil.
Definition l4 := [1;2;3].

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

Definition hd (default : nat) (l : natlist) := nat :=
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
```

### Propiedades sobre listas

- De la misma forma en que hicimos con los números, podemos probar algunas propiedades sobre listas usando el método de
  simplificación. Por ejemplo:

  ```coq
  Theorem concat_vacia : forall l : natlist, [] ++ l = l.
  Proof.
    reflexivity.
  Qed.
  ```

- Por supuesto, también hay casos dónde realizar un análisis de casos nos es de gran utilidad, en este caso sobre la 
  estructura de las listas.

  ```coq
  Theorem cola_longitud_pred : forall l : natlist, pred (length l) = length (tl l).
  Proof.
    intros l.
    destruct l as [| n l '].
    - (* l = nil *)
      reflexivity.
    - (* l = cons n l' *)
      reflexivity.
  Qed.
  ```

- Por supuesto, como la persona lectora está acostumbrada, muchos de los teoremas sobre listas se prueban por inducción
  estructural.

#### Inducción sobre listas

- Primero, recordemos el principio de Inducción Estructural sobre Listas:

  - Sea *P* la propiedad a probar.

  - Primero, mostramos que *P* es verdadera cuando la lista es vacía.

  - Después, mostramos que *P* es verdadera cuando la lista tiene cabeza y cola (`cons n l'`) suponiendo que `l` cumple
    *P*.

- Por ejemplo.

   ```coq
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
   Theorem contat_length: forall l_1 l_2 : natlist, 
    lenght (l_1 ++ l_2) = (length l_1) + (length l_2).
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
      rewrite -> add_comm.
      reflexivity.
   Qed.
   ```


[`Anterior`](../tema01/README.md) | [`Siguiente`](../tema03/README.md)
