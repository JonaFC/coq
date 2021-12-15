(** Semántica y Verificación
    Ejemplo 2
    Manuel Soto Romero
    Luis F. Benítez Lluis 
    
    Contenido:
    1 Números
    2 Pruebas por Simplificación
    3 Pruebas por reescritura
    4 Pruebas por inducción
    
    Para acceder rápidamente a la sección deseada
    buscar la cadena ">n" donde "n" es el número de
    sección. 
    
    Material basado en los scripts 
    correspondientes al libro Logical Foundations en
    Software Foundations- Benjamin C. Pierce, et al. 
    *)


(** ** >1 Números **)
Print nat.
Module Naturales.

Inductive nat : Type :=
   | O
   | S (n : nat).

Definition pred (n : nat) : nat :=
   match n with
   | O    => O
   | S n' => n'
   end.

End Naturales.

Check (S (S (S (S 0)))).
(* ==> 4 : nat *)

Definition menosdos (n : nat) : nat :=
   match n with
   | 0        => 0
   | S 0      => 0
   | S (S n') => n'
   end.

Compute (menosdos 4).
(* ==> 2 : nat *)

Check S : nat -> nat.
Check pred : nat -> nat.
Check menosdos .


Fixpoint par (n : nat) : bool :=
   match n with
   | 0 => true
   | S 0 => false
   | S (S n') => par n'
   end.

Definition impar (n : nat) : bool :=
   negb (par n).

(* par S (S (S (S 0)))
   par (S (S 0))
   par 0
   true *)

Example prueba_impar1: impar 1 = true.
Proof. simpl. reflexivity. Qed.
Example prueba_impar2: impar 4 = false.
Proof. simpl. reflexivity. Qed.

Module Naturales2.

Fixpoint suma (n : nat) (m : nat) : nat :=
   match n with
   | 0 => m
   | S n' => S (suma n' m)
   end.

Compute (suma 3 2).
(* ==> 5 : nat *)

(* suma 3 2
   suma (S (S (S 0)))) (S (S 0))
   S (suma (S (S 0)) (S (S 0)))
   S (S (suma (S 0) (S (S 0))))
   S (S (S (suma 0 (S (S 0)))))
   S (S (S (S (S 0)))) *)

Fixpoint mult (n m: nat) : nat :=
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


(** Ex *)
(* Podemos definr la función recursiva exponencial
de manera natural. Es importante señalar que esta versión
regresa 1 si la potencia es 0 independientemente de si 
la base es cero. *)
Fixpoint exp (base potencia : nat) : nat :=
   match potencia with
   | 0 => S 0
   | S p => mult base (exp base p)
   end.
(* Podemos hacer una versión alternativa que revise el valor de la base
para decidir si devuelve cero o uno. Aún con esto, tomamos la decición de 
regrsar cero cuando la base y la potencia son 0. Nos gustaría que
devolviese un error. Esto se podrá solvetar con el tipo opción que veremos
mas adelante. *)
Fixpoint exp2 (base potencia : nat) : nat :=
   match potencia with
   | 0 => match base with 
            | 0 => 0
            | _ => 1
          end
   | S p => mult base (exp2 base p)
   end.
(** Con la primer definición podemos mostrar unas propiedades 
básicas que no requieren más que simplificar los cálculos. *)
Lemma pot_cero: forall b: nat, exp b 0 = 1.
Proof.
intro.
simpl.
reflexivity.
Qed.

(* Esta versión impone que la potencia no sea cero, esto es,
sea el sucesor de alguien para que con base cero se devuelva cero. 
Coq no puede detectacr automáticamente que la potencia no es cero, 
por lo que no puede solventar automáticamente el resultado. De aquí requeriremos 
hacer un análisis de casos sobre la potencia. *)
Lemma base_cero: forall p:nat, exp 0 (p+1) = 0.
Proof.
intro.
destruct p.
- simpl. reflexivity.
- simpl. reflexivity.
Qed.


(** Ex*)
(* Podemos definir dos factoriales. Una de la forma usaul y otra usando recursión de
cola con una función auxiliar. Ambas versiones deben evaluar a lo mismo. *)
Fixpoint factorial (n:nat) : nat:=
  match n with 
    | 0 => 1
    | S n' => mult (S n') (factorial n')
   end.
(* Esta versión usa un acumulador para almacenar el valor del factorial previo 
y por ende hacer mas eficiente la evaluación. *)
Fixpoint factorial_tail_aux (n acc:nat) : nat:=
  match n with 
    | 0 => acc
    | S n' => factorial_tail_aux n' (mult (S n') acc)
   end.
(* La versión de recursión de cola ya no requiere ser recursiva en un sentido estricto
pues se puede poner en términos de la función auxiliar. *)
Definition factorial_tail (n :nat) :=
      factorial_tail_aux n 1.
Example prueba_factorial1:  (factorial 3) = 6.
Proof.
simpl.
reflexivity.
Qed.

(* Verificar que las definiciones cumplen con pruebas se realiza de la manera usual. *)
Example prueba_factorial2: (factorial 5) = (mult 10 12).
Proof.
simpl.
reflexivity.
Qed.

Example prueba_factorial3:  (factorial_tail 3) = 6.
Proof.
simpl.
unfold factorial_tail.
simpl.
reflexivity.
Qed.

Example prueba_factorial4: (factorial_tail 5) = (mult 10 12).
Proof.
reflexivity.
Qed.

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

End Naturales2.

Module ComparacionNat.
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
(* eqb*)

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
Proof.  reflexivity. Qed.
Example prueba_menor2: menorigual 2 4 = true.
Proof.  reflexivity. Qed.
Example prueba_menor_3: menorigual 4 2 = false.
Proof.  reflexivity. Qed.

Notation "x =? y" := (soniguales x y) (at level 70) : nat_scope.
Notation "x <=? y" := (menorigual x y) (at level 70) : nat_scope.

Example prueba_menor_3': (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.


(** Ex*)
(* Una vez dada la definición de menor o igual, podemos plantear el operador 
de orden estricto. A pesar de que este operador se puede definir de forma 
recursiva, optamos por ponerlo en términos del orden reflexivo.*)

Definition ltb (n m : nat) : bool := menorigual (S n) m.

(* De igual forma podemos hacer la notación correspondiete a este operador.*)
Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

(* Que cumpla con algunas pruebas sencillas se puede hacer de la forma usual 
al computar la función.*)
Example test_ltb1: (ltb 2 2) = false.
Proof.  reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof.  reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof.  reflexivity. Qed.

End ComparacionNat.



(** ** >2 Pruebas por simplificación **)

Theorem suma_0_n : forall n : nat, 0 + n = n.
Proof.
   intros n. simpl. reflexivity. Qed.
Theorem suma_0_n' : forall n : nat, 0 + n = n.
Proof.
   intros n. reflexivity. Qed.
   
(** ** >3 Pruebas por Reescritura **)
Theorem suma_ig : forall n m : nat, n = m -> n + n = m + m.
Proof.
   intros n m.
   intros H.
   rewrite H.
   reflexivity.
Qed.
Check mult_n_O.
(* ===> forall n : nat, 0 = n * 0 *)
Check mult_n_Sm.
(* ===> forall n m : nat, n * m + n = n * S m *)

Theorem mult_n_0_m_0 : forall p q : nat, (p * 0) + (q * 0) = 0.
Proof.
   intros p q.
   rewrite <- mult_n_O.
   rewrite <- mult_n_O.
   reflexivity.
Qed.


(** ** >4 Pruebas por Análisis de Casos **)
(* Dado que hay bibliotecas estándar con las definiciones correspondientes 
de operadores aritméticos y booleanos, optamos por usar estas versiones. 
Es importante señalar que las versiones antes presentantes están fuertemente
inspiradas en las versiones de estas bibliotecas por lo que se puede esprar un 
comportamiento semejente. *)
From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.

(* En comando "Locate" sirve para hallar la el nombre de alguna notación planteada *)
Locate "=?".
(* Una vez sabiendo el nombre se puede consultar la definición del operador correspondiente.*)
Print eqb.

Theorem suma_1_neq_0_1 : forall n : nat,
  ((n + 1) =? 0 ) = false.
Proof.
  intros n.
  simpl.
Abort. 

Theorem suma_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity. 
Qed.

(** Ex*)
(* Un simple analisis de casos sobre el valor del booleano sirve para resolver este caso. 
Obsérvese como se usa las secuencia de tácticas "destruct b; reflexivity.". El punto y coma
sirve para a cada rama que surja de aplicar la táctica "destruct b" se le aplique la táctica
"relfexivity". Esto simplifica las pruebas pues cada rama se resuelve con  el mismo proceso.  *)
Theorem negb_involutive : forall b: bool,
  negb (negb b) = b.
Proof.
intros.
destruct b; reflexivity.
Qed.
(* De nuevo "destruct b c; reflexivity." nos ayuda a reolver todos los casos de un sólo golpe. 
Esta estrategia puede ser riesgosa si no todos los casos se resuelven igual. Hay maneras
de solvetar casos que se resulevan por otros medios, las cuales veremos mas adelante. *)
Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
intros.
destruct b,c;reflexivity.
Qed.
(** ** >5 Pruebas por Inducción **)

Theorem suma_0_derecha_1 : forall n:nat, n + 0 = n.

Proof.
   intros n.
   simpl.
Abort.

Theorem suma_0_derecha_2 : forall n:nat, n + 0 = n.
Proof.
  intros n. 
  Locate "+".
  Print Nat.add.
  destruct n as [| n'] eqn:E.
  - reflexivity.
  - simpl.
Abort.

Theorem suma_0_derecha : forall n:nat, n + 0 = n.

Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem mult_0_suma' : forall n m : nat, (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity. 
Qed.

(** Ex*)
(* Con una prueba por inducción podemos tener un medio más poderoso para probar 
afirmaciones sobre naturales. Nótese que elegimos hacer induccion sobre n
para facilitar el caso base y que los cómputos fueran más naturales. 
Elegir adecuadamente sobre qué termino se hace inducción es fundamental en la 
búsqueda de pruebas. *)
Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

(* Es común que haya pruebas que requieran de teoremas previos. Si estos teoremas
afirman igualdades se puede usar la táctica rewrite para hacer substituciones adecuadeas. *)
Theorem add_comm: forall n m : nat, n + m = m + n.
Proof.
intros.
induction n.
- simpl. rewrite suma_0_derecha. reflexivity.
- simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity.
Qed.


 
Theorem suma_conm_1 : forall n m p q : nat, (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  rewrite add_comm.
Abort.
  
Theorem suma_conm_2 : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite add_comm. reflexivity. }
  rewrite H. reflexivity. Qed.
  
(** Ex*)  
Theorem eqb_refl : forall n : nat,
  true = (n =? n).
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.


