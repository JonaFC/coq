(** Semántica y Verificación
    Ejemplo 5
    Manuel Soto Romero
    Luis F. Benítez Lluis 
    
    Contenido:
    1 Definiciones de listas polimórficas
    2 Pares Polimórficos
      2.1 La función split
    3 Opcioes polimórficos
      3.1 Función head para listas polimóficas
    4 La táctica discriminate
    5 Manejo de la hipótesis inductiva 
    6 Desdoblando definiciones 
    7 Resumen de téctias (extracto citado del libro) 
    

    Para acceder rápidamente a la sección deseada
    buscar la cadena ">n" donde "n" es el número de
    sección. 
    
    Material basado en los scripts 
    correspondientes al libro Logical Foundations en
    Software Foundations- Benjamin C. Pierce, et al. 
    *)

Require Import Coq.Arith.PeanoNat.
Require Import Bool.Bool.

(** >1 Definiciones de listas polimórficas*)

Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).
Arguments nil {X}.
Arguments cons {X} _ _.

Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil      => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.
Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

(** >2 Pares Polimórficos *)

(* Generalizemos la noción de par *)

Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).

(* Definimos lor argumentos implicitos *)
Arguments pair {X} {Y} _ _.


(* Definomos la notación usual de par *)

Notation "( x , y )" := (pair x y).

(* Podemos usar también notación para el producto de tipos*)

Notation "X * Y" := (prod X Y) : type_scope.

(* La anotación [: type_scope] le dice a Coq que la anotación de 
    tipos sólo aplica en el parsing de tipos, más no para expresiones. 
    Gracias a esta restricción evitamos conflicto con la notación
    de multiplicación. *)


(* Es importante hacer hincapié en que (x,y) representa la notación 
  de expresiones que representan parejas ordenadas y que 
  X*Y representan el producto de tipos. Si x:X y y:Y entonces
  (x,y):X*Y*)


Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

(*Función que combina dos listas en parejas de entradas 
  de cada lista respectivamente *)
(* [1,2,3], [4,5,6]=> [(1,4),(2,5),(3,6)]*)

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y):=
  match lx,ly with
    | [], _ => []
    | _, [] => []
    | x::tx, y ::ty => (x,y):: (combine tx ty)           
    end.
          
Example test_combine: combine [1;2;3] [4;5;6]=[(1,4);(2,5);(3,6)].
Proof.
simpl.
reflexivity.
Qed.



(** >2.1 La función split*) 
(*  La función [split] es la inversa derecha de [combine], desdoblando
    listas de parejas en una pareja de listas con los elementos
    respectivos.*)
(*    [(1,4);(2,5);(3,6)]
   
   (1,4)
   ([2;3],[5;6]) *)
Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y):=
match l with
  | [] => ([],[])
  | h::t => ((fst h)::fst (split t), (snd h)::snd(split t))
end.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof.
reflexivity.
Qed.





(** >3 Opcioes polimórficos *)

(* Hagamos la definición en un módulo pues coq ya posee 
    el tipo opción que buscamos*)
Module OptionPlayground.

Inductive option (X:Type) : Type :=
  | Some (x : X)
  | None.

Arguments Some {X} _.
Arguments None {X}.

End OptionPlayground.

(* Recordemos que nth-error es una función que devuelve el 
    n-ésimo elemento de una lista. Dado que se puede elegir 
    n ue supere la longitud de la lista, es conveniente que 
    devolvamos un tipo opción para ajustar para este error.  *)

Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = None.
Proof. reflexivity. Qed.



(** >3.1 Función head para listas polimóficas *)

Definition hd_error {X : Type} (l : list X) : option X:=
  match l with 
    | [] => None
    | h::t=> Some h
  end. 


Check @hd_error : forall X : Type, list X -> option X.

Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof.
reflexivity.
Qed.

Example test_hd_error2 : hd_error  [[1];[2]]  = Some [1].
Proof.
reflexivity.
Qed.
 
 
 
 
(** >4 La táctica discriminate*)

(*  La táctica [discriminate] sirve para detectar hipótesis inválidas
    sobre igualdadades. Para que la táctica funcione, es inminente
    que los términos sean sintácticamente distintos. Por ejemplo
    cuando se tiene iguadad entre un sucesor y cero [S n = O]. *)

Theorem eqb_0_l : forall n,
   0 =? n = true -> n = 0.
Proof.
  intros.
  destruct n.
  -  simpl in H. reflexivity.
  - simpl in H.
    discriminate H.
Qed.



(*  El razonamiento lógico a esta solución sigue el principio de
    explosión que afirma que de cosas falsas se sigue 
    lo que sea. En este caso la falsedad se encarna como 
    igualdades insatisfacibles. *)

Theorem discriminate_ex1 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros.
  discriminate H.
Qed.


Theorem discriminate_ex2 : forall (n m : nat),
  false = true ->
  [n] = [m].
Proof.
intros.
discriminate H.
Qed.


Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof.
  intros.
  discriminate H.
Qed.


Example inversion_ex :
  forall (n:nat), S n <=0-> 2+2=5.
Proof.
  intros.
  inversion H.  
Qed.


(** >5 Manejo de la hipótesis inductiva *)
Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.



Theorem double_injective_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction n as [| n' IHn'].
  - (* n = O *) simpl. intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *) intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) discriminate eq.
    + (* m = S m' *) apply f_equal.

Abort.


Theorem double_injective : forall  n m,
     double n = double m ->
     n = m.
Proof.
intro.

induction n.
- intros. destruct m.
  -- reflexivity.
  -- discriminate H.
- intros. destruct m.
  -- discriminate H.
  -- apply f_equal.
      apply IHn.
      inversion H.
      reflexivity.
Qed.


(* intros  n. induction n as [| n' IHn'].
  - (* n = O *) simpl. intros m eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *) simpl.
    intros m eq.
    destruct m as [| m'] eqn:E.
    + (* m = O *)
    discriminate eq.
    + (* m = S m' *)
      apply f_equal.
      apply IHn'. simpl in eq. injection eq as goal. apply goal. 
Qed. 
 *)


(* intro.
induction n.
- intros. destruct m.
-- reflexivity.
-- simpl in H. discriminate H.
- intros. simpl in H.
destruct m.
-- simpl in H. discriminate H.
-- simpl in H. apply f_equal. 
  apply IHn. 
  injection H.
  intro.
  assumption.
  
  (*  inversion H.
   reflexivity. *)
Qed. *)
  







Theorem eqb_true : forall n m,
    n =? m = true -> n = m.
Proof.
intro.
induction n.
- destruct m.
-- intros. reflexivity.
--  intros. discriminate H.
- destruct m.
-- intros. discriminate H.
-- intros. apply f_equal.
  apply IHn.
  simpl in H.
  assumption.
  Qed.



(* Hint: usar [plus_n_Sm] *)
Check plus_n_Sm.
Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
intro.
induction n.
- intros. simpl in H. destruct m.
-- reflexivity.
-- simpl in H.
discriminate H.
- intros.
destruct m. 
-- discriminate H.
-- apply f_equal.
   apply IHn.
   simpl in H.
   inversion H.
   rewrite <-plus_n_Sm in H1.
   rewrite <-plus_n_Sm in H1.
   inversion H1.
   reflexivity.
Qed.


(* A veces hay que reorganizar las variables para que al generalizar
las pruebas salgas adecuadamente*)

Theorem double_injective_take2_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction m as [| m' IHm'].
  - (* m = O *) simpl. intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) apply f_equal.

Abort.


Theorem double_injective_take2 : forall m n,
     double n = double m ->
     n = m.
Proof.
intros.
generalize dependent m.
induction n.
- intros. destruct m.
  -- reflexivity.
  -- discriminate H.
- intros. destruct m.
  -- discriminate H.
  -- apply f_equal.
      apply IHn.
      inversion H.
      reflexivity.
Qed.






(*   intros n m.
  generalize dependent n.
  induction m as [| m' IHm'].
  - (* m = O *) simpl. intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) apply f_equal.
      apply IHm'. injection eq as goal. apply goal. Qed. *)



(* Probemos por inducción sobre l*)

Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     nth_error l n = None.
Proof.
Admitted.




(** >6 Desdoblando definiciones *)
Require Import Coq.Arith.PeanoNat.

Definition square n := n * n.


Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
intros.
unfold square.
rewrite Nat.mul_assoc.
assert (H : n * m * n = n * n * m).
    { rewrite Nat.mul_comm. apply Nat.mul_assoc. }
  rewrite H. rewrite Nat.mul_assoc. reflexivity.
Qed.








(*  Algunas tácticas como [apply][simpl] y [reflexivity]
    simplifican términos cuando se usan, y particularmente 
    desdoblan definiciones de algunas funciones.
    Por lo que en algunos casos no hace falta desdoblar
    las deficniciones pues se hace automáticamente *)

Definition foo (x: nat) := 5.

Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  simpl.
  reflexivity.
Qed.

(*  No obstante, este desdoblamiento no siempre se ejecuta
    sobretodo si la expresión es algo compleja. *)

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

Fact silly_fact_2_FAILED : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  simpl. 
Abort.
(* [simpl] no siempre logra progreso pues la cláusula match 
   impide que se simplifique a su última expresión, ya que
   la entrada no se puede catalogar en la búsqueda de patrones.
   Es hasta que se desestructura la entrad que se puede resolver
   el match y simplificar la expresión*)

Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  destruct m eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(* Esto funciona pero si alguna parte de la expresión no se puede
  detectar para caza de patrones puede que requiramos más 
  desestructuración. Otra forma es literalmente desdoblando la 
  definición.*)


Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
Admitted.



(*   intros m.
  unfold bar.
  destruct m eqn:E.
  - reflexivity.
  - reflexivity.
Qed. *)





(** >7 Resumen de téctias (extracto citado del libro) *)
(* 

      - [intros]: move hypotheses/variables from goal to context

      - [reflexivity]: finish the proof (when the goal looks like [e =
        e])

      - [apply]: prove goal using a hypothesis, lemma, or constructor

      - [apply... in H]: apply a hypothesis, lemma, or constructor to
        a hypothesis in the context (forward reasoning)

      - [apply... with...]: explicitly specify values for variables
        that cannot be determined by pattern matching

      - [simpl]: simplify computations in the goal

      - [simpl in H]: ... or a hypothesis

      - [rewrite]: use an equality hypothesis (or lemma) to rewrite
        the goal

      - [rewrite ... in H]: ... or a hypothesis

      - [symmetry]: changes a goal of the form [t=u] into [u=t]

      - [symmetry in H]: changes a hypothesis of the form [t=u] into
        [u=t]

      - [transitivity y]: prove a goal [x=z] by proving two new subgoals,
        [x=y] and [y=z]

      - [unfold]: replace a defined constant by its right-hand side in
        the goal

      - [unfold... in H]: ... or a hypothesis

      - [destruct... as...]: case analysis on values of inductively
        defined types

      - [destruct... eqn:...]: specify the name of an equation to be
        added to the context, recording the result of the case
        analysis

      - [induction... as...]: induction on values of inductively
        defined types

      - [injection]: reason by injectivity on equalities
        between values of inductively defined types

      - [discriminate]: reason by disjointness of constructors on
        equalities between values of inductively defined types

      - [assert (H: e)] (or [assert (e) as H]): introduce a "local
        lemma" [e] and call it [H]

      - [generalize dependent x]: move the variable [x] (and anything
        else that depends on it) from the context back to an explicit
        hypothesis in the goal formula

      - [f_equal]: change a goal of the form [f x = f y] into [x = y] *)


