(*Inductive nat : Type :=
   | 0
   | S (n : nat).*)

Definition pred (n : nat) : nat :=
   match n with
   | 0    => 0
   | S n' => n'
   end.

Check (S (S (S (S 0)))).

Definition menosdos (n : nat) : nat :=
   match n with
   | 0        => 0
   | S 0      => 0
   | S (S n') => n'
   end.
   
Compute (menosdos 4).

Check S : nat -> nat.
Check pred : nat -> nat.
Check menosdos : nat -> nat.

Fixpoint par (n : nat) : bool :=
   match n with
   | 0 => true
   | S 0 => false
   | S (S n') => par n'
   end.
   
Definition impar (n : nat) : bool :=
   negb (par n).   
   
Example prueba_impar1: impar 1 = true.
Proof. simpl. reflexivity. Qed.
Example prueba_impar2: impar 4 = false.
Proof. simpl. reflexivity. Qed.

Fixpoint suma (n : nat) (m : nat) : nat :=
   match n with
   | 0 => m
   | S n' => S (suma n' m)
   end.
   
Compute (suma 3 2).


(* suma 3 2
   suma (S (S (S 0)))) (S (S 0))
   S (suma (S (S 0)) (S (S 0)))
   S (S (suma (S 0) (S (S 0))))
   S (S (S (suma 0 (S (S 0)))))
   S (S (S (S (S 0)))) *)
   
Fixpoint mult (n m : nat) : nat :=
   match n with
   | 0 => 0
   | S n' => suma m (mult n' m)
   end.
   
Example prueba_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.   

Fixpoint resta (n m : nat) : nat :=
   match n,m with
   | 0, _ => 0
   | S _, 0 => n
   | S n', S m' => resta n' m'
   end.
   
Fixpoint exp (base potencia : nat) : nat :=
   match potencia with
   | 0 => S 0
   | S p => mult base (exp base p)
   end.   
   
(* 2^3 = 2*2^2 = 2*2*2^1 = 2*2*2*2^0 = 2*2*2*1 = 8 *)

Notation "x + y" := (suma x y)
                     (at level 50, left associativity)
                     : nat_scope.
Notation "x - y" := (resta x y)
                     (at level 50, left associativity)
                     : nat_scope.
Notation "x * y" := (mult x y)
                     (at level 40, left associativity)
                     : nat_scope.
Check ((0 + 1) + 1) : nat.

Fixpoint soniguales (n m : nat) : bool :=
   match n with
   | 0 => match m with
          | 0 => true
          | S m' => false
          end
   | S n' => match m with
             | 0 => false
             | S m' => soniguales n' m'
             end
   end.
   
Fixpoint menorigual (n m : nat) : bool :=
   match n with
   | 0 => true
   | S n' =>
       match m with
       | 0 => false
       | S m' => menorigual n' m'
       end
   end.   
   
Example prueba_menor1: menorigual 2 2 = true.
Proof. simpl. reflexivity. Qed.
Example prueba_menor2: menorigual 2 4 = true.
Proof. simpl. reflexivity. Qed.
Example prueba_menor_3: menorigual 4 2 = false.
Proof. simpl. reflexivity. Qed.

Notation "x =? y" := (soniguales x y) (at level 70) : nat_scope.
Notation "x <=? y" := (menorigual x y) (at level 70) : nat_scope.

Example prueba_menor_3': (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.