(** Semántica y Verificación
    Ejemplo 3
    Manuel Soto Romero
    Luis F. Benítez Lluis 
    
    Contenido:
    1 Repaso a inducción
    2 Determinación de análisis de casos, simplificación o inducción
    3 Mas ejercicios
    
    Para acceder rápidamente a la sección deseada
    buscar la cadena ">n" donde "n" es el número de
    sección. 
    
    Material basado en los scripts 
    correspondientes al libro Logical Foundations en
    Software Foundations- Benjamin C. Pierce, et al. 
    *)
(** ** >1 Hagamos un repaso rápido de inducción*)
Print Nat.add.
Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite <-IHn. reflexivity.
Qed.
  

Print minus.
Print Nat.sub.

Theorem minus_n_n : forall n,
  minus n n = 0.
Proof.
induction n.
- simpl. reflexivity.
- simpl. assumption.
Qed.

    
Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
induction n.
- simpl. reflexivity.
- intros. simpl.
  rewrite IHn. reflexivity.
Qed.



Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  induction n.
  - simpl. apply plus_n_O.
  - intros. simpl.
    rewrite IHn. 
    apply plus_n_Sm.
Qed.



Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  induction n.
(*   generalize m si m fue introducido con el induction  *)
  - simpl. reflexivity.
  - simpl. intros. rewrite IHn. reflexivity.
Qed.  


Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.


Lemma double_plus : forall n, double n = n + n .
Proof.
induction n.
- reflexivity.
- simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity.
Qed.



From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.

(** **>2 Predecir si los siguientes teoremas sólo requieren de simplifiación
y rescritura; de análisis de casos o de inducción.*)


Locate "<=?".
Print Nat.leb.

(* usar rewrite con entradas para ser específico
usar el <do n tactic> para repetir tácticas.*)
(* Iducción*)
Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
induction n.
- simpl. reflexivity.
- intros. simpl. rewrite IHn. simpl.
apply plus_n_Sm.
Qed.

  
  
  
Theorem leb_refl : forall n:nat,
  true = (n <=? n).
Proof.
induction n.
- reflexivity.
- simpl. assumption.
Qed.




Theorem zero_nbeq_S : forall n:nat,
  0 =? (S n) = false.
Proof.
intros.
reflexivity.
Qed.




Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
destruct b; reflexivity.
Qed.

Theorem andb_false_l : forall b : bool,
  andb false b = false.
Proof.
reflexivity.
Qed.

Theorem plus_ble_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
induction p.
- simpl. tauto.
- intros. simpl.
  apply IHp. apply H.
Qed.



Theorem S_nbeq_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
intros. reflexivity.
Qed.


Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
destruct b, c; reflexivity.
Qed.


(** ** >3 Mas ejercicios *)
Lemma pred_succ n : pred (S n) = n.
Proof.
simpl. reflexivity.
Qed.



Lemma pred_0 : pred 0 = 0.
Proof.
simpl.
reflexivity.
Qed.


Print Nat.pred.
Locate "-".
Print Nat.sub.

Lemma sub_0_r n : n - 0 = n.
Proof.
destruct n;reflexivity.
Qed.

Print Nat.pred.
Locate "-".
Print Nat.sub.

Lemma sub_succ_r: forall n m :nat, n - (S m) = pred (n - m).
Proof. 
induction n.
- intros. simpl. reflexivity.
- simpl. destruct m. 
-- simpl. apply sub_0_r.
-- apply IHn.
Qed.


