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

### Opciones

Supongamos que necesitamos escribir una función que regrese el n-ésimo elemento de una lista, una posible definición
es la siguiente:

```coq
Fixpoint nesimo1 (l:natlist) (n:nat) : nat :=
  match l with
  | nil => -1
  | a :: l' => match n with
               | 0 => a
               | S n' => nesimo1 l' n'
               end
  end.
```

Esta solución tiene el defecto de que al llegar a la lista vacía regresa -1 lo cual puede ser confuso, pues no sabríamos
si el elemento -1 está contenido en la lista o si en efecto se usó la definición con la lista vacía.

El principal problema viene dado por el tipo de la función: `nat -> natlist -> nat`. Una mejor alternativa es cambiar
el tipo de regreso de la función de manera que incluya un valor de error en casos similares al de nuestra función. 
Veamos la definición de dicho tipo al cual llamaremos `natoption`.

```coq
Inductive natoption : Type :=
  | Some (n : nat)
  | None.
```

De esta forma podemos cambiar la definición de `nesimo` como sigue:

```coq
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
```

Por supuesto, para fines prácticos, necesitaremos sacar el número que envuelve a `Some`, para ello necesitaremos un 
valor por defecto a devolver en caso de obtener `None`, podemos usar la siguiente función:

```coq
Definition getoption (d : nat) (o : natoption) : nat :=
  match 0 with
  | Some n' => n'
  | None => d
  end.
```

### Diccionarios

Como ejemplo final, veamos cómo es posible definir otras estructuras de datos en __Coq__. En esta caso definiremos un
simple diccionario. Para ello necesitamos definir nuestras llaves, en este caso considerando que sólo podemos tener
llaves numéricas, de la misma forma, necesitaremos una función que nos permita comparar dichas llaves.

```coq
Inductive id : Type :=
  | Id (n : nat).

Definition eqb_id (x_1 x_2 : id) :=
  match x1, x2 with
  | Id n_1, Id n_2 => n_1 =? n_2
  end.
```

Con esta definición podemos definir nuestros diccionarios como sigue junto con algunas funciones:

```coq
Module Diccionarios.
Export NatList.

Inductive diccionario : Type :=
  | empty
  | record (i : id) (v : nat) (m : diccionario).

Definition actualiza (d : diccionario) (x : id) (value : nat) : diccionario :=
  record v value d.

Fixpoint busca (x : id) (d : diccionario) : natoption :=
  match d with
  | empty => None
  | record y v d' => if eqb_id x y then
                        Some v
                     else
                        find x d'
  end.  
```






[`Anterior`](../tema01/README.md) | [`Siguiente`](../tema03/README.md)
