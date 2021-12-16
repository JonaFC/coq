Theorem suma_0_n : forall n : nat, 0 + n = n.
Proof.
  intros n.
  reflexivity.
Qed.
  
Theorem suma_ig : forall n m : nat, n = m -> n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity.
Qed.

Check mult_n_O.
Check mult_n_Sm.
Check  suma_0_n.

Theorem mult_n_0_m_0 : forall p q : nat, (p * 0) + (q * 0) = 0.
Proof.
  intros p q.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity.
Qed.

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
   
Notation "x =? y" := (soniguales x y) (at level 70) : nat_scope.

Theorem suma_1_neq_0_1 : forall n : nat,(n + 1) =? 0 = false.
Proof.
  intros n.
  simpl.
Abort.

Theorem suma_1_neq_0 : forall n : nat,(n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity. 
Qed.

(* nat:
   - 0
   - S n' *)
   
Theorem suma_0_derecha_1 : forall n:nat, n + 0 = n.

Proof.
   intros n.
   simpl.
Abort.   

Theorem suma_0_derecha_2 : forall n:nat, n + 0 = n.
  
Proof.
  intros n. 
  destruct n as [| n'] eqn:E.
  - reflexivity.
  - simpl.
Abort.

Theorem suma_0_derecha : forall n:nat, n + 0 = n.

Proof.
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

Theorem add_comm: forall n m : nat, n + m = m + n.
Proof.
  Admitted.
  
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

