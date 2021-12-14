[`Introducción a la Verificación Formal con Coq`](../README.md) > `Tema 3`

## Pruebas por Inducción

### Introducción

Podemos probar que 0 es el neutro de la suma por la izquierda usando `reflexivity`. Sin embargo, al tratar de realizar
la prueba por la derecha, no es posible hacerlo con las tácticas que conocemos hasta ahora.

```coq
Theorem suma_0_derecha_1 : forall n:nat, n + 0 = n.

Proof.
   intros n.
   simpl.
Abort.
```

Otra forma de hacerlo podría ser por un análisis de casos sobre `n`. Sin embargo, esto sólo funciona para el caso donde
`n` es 0. En caso de ser un sucesor, tenemos exactamente el mismo problema.

```coq
Theorem suma_0_derecha_2 : forall n:nat, n + 0 = n.
  
Proof.
  intros n. 
  destruct n as [| n'] eqn:E.
  - reflexivity.
  - simpl.
Abort.
```

En general, para realizar pruebas sobre números, listas y otros conjuntos definidos de manera inductiva, usamos
*inducción*. Recordemos los pasos de una prueba por inducción sobre los naturales:

- Probar que *P(0)* se cumple.
- Suponer que `P(n')` se cumple. Esta es nuestra hipótesis de inudcción.
- Probar usando la hipótesis de inducción que para todo `n'` si `P(n')` entonces `P(S n')`.

Esto es posible en __Coq__ mediante la táctica `induction` que genera dos submetas: Una dónde debemos probar `P(0)` y
otra dónde debemos demostrar `P(n') -> P(S n')`:

```coq
Theorem suma_0_derecha : forall n:nat, n + 0 = n.

Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.
```

---
> :warning: **Observación.** Es posible omitir la parte `as` en `destruct` o `induction` y __Coq__ pondrá el nombre de variables 
> automáticamente, sin embargo, estos nombres no suelen ser intuitivos y pueden causar confusiones, por lo cual se
> recomienda siempre colocarlo nosotros.
---
> :warning: **Observación.** El uso de la táctica `intros` es redundante en este tipo de pruebas.
---
> 🧩 **Actividad.** Prueba que para todo número natural *n*, *n - n = 0*.

<details><summary>Solución</summary>
<p>

```coq
Theorem resta_n_n : ∀ n, minus n n = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite → IHn'. reflexivity. 
Qed.
```

</p>
</details>

---

### Pruebas dentro de Pruebas

Al igual que lo hacemos en las pruebas a papel y lapiz, algunas pruebas requieren descomponerse en una secuencia de
teoremas que se van probando por separado de forma tal que podamos aplicar dichos resultados en la prueba original. 
Sin embargo, hay situaciones donde tenemos hechos tan triviales que resulta innecesario realizar esta separación. Para
este tipo de casos, podemos usar la táctica `assert`.

La táctica `assert` genera dos submetas: (1) una para probar la *aserción* tal cual además de asignarle un nombre de
forma similar a las tácticas `destruct` e `induction` y (2) otra para usar dicha aserción en la prueba global. Por ejemplo:

```coq
Theorem mult_0_suma' : forall n m : nat, (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity. 
Qed.
```

Otro ejemplo donde puede aplicarse esta técnica es en el siguiente teorema. Queremos probar que 
*(n + m) + (p + q) = (m + n) + (p + q)* que a simple vista parece sencillo pues sólo debe usarse la conmutatividad. 
Dicha propiedad se encuentra definida en __Coq__ como `add_comm`, sin embargo al aplicarla con `rewrite`, no parece
funcionar.

```
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
```

[`Anterior`](../tema01/README.md) | [`Siguiente`](../tema03/README.md)
