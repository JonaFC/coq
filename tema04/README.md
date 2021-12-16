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

[`Anterior`](../tema01/README.md) | [`Siguiente`](../tema03/README.md)
