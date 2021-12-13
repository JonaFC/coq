[`Introducción a la Verificación Formal con Coq`](../README.md) > `Tema 2`

## Programación Funcional en Coq

### Introducción

El estilo de programación funcional, sigue un enfoque matemático que nos permite razonar sobre las funciones definidas
de manera formal. Entre las características que tienen los lenguajes de este estilo tenemos:

1. Si el lenguaje es *puro*, entonces no importa cuantas veces llamemos a una misma función con los mismos argumentos,
   siempre obtendremos el mismo resultado. Llamamos a esto, *transparencia referencial*.

1. Las funciones pueden ser pasadas como argumento a otras funciones, ser devueltas como resultado e incluso almacenarse
   en variables o estructuras de datos. Se dice entonces que las funciones se comportan como *ciudadanos de primera 
   clase*.

1. Es posible definir nuevos *tipos de datos algebraicos* de manera sencilla por medio de sus constructores de manera 
   muy similar a la definición de gramáticas. Estas definiciones permiten además definir estructuras de datos genéricas
   mediante *sistemas de tipos polimóficos* además de aprovechar ampliamente la técnica de *reconocimiento de patrones*.

En este material, estudiaremos las principales característica del lenguaje de programación funcional que provee __Coq__ llamado __Gallina__ así como una serie de *tácticas* básicas  que podemos usar para probar propiedades sobes los 
programas escritos en éste.

![imagen](https://1.bp.blogspot.com/-QzhsYlLiGsg/WDzqnDaJl-I/AAAAAAAALe4/aTQaaOYmzkI4RQcAr-E0csUhT5i6VWwawCLcB/s1600/firstclass.png)

#### :large_orange_diamond: <ins>Tipos de Datos y Funciones</ins>

Una caracteríca de __Coq__ es que provee un conjunto muy limitado de *primitivas* básicas. Por ejemplo, en lugar de
proveer los tipos de datos básicos tipicos (booleanos, enteros, cadenas, etc.), nos permite definir nuevos tipos de 
datos desde cero por medio de dichos tipos básicos aunque sí tiene funciones para una gran cantidad de tipos *comunes*.

Por ejemplo, comencemos con un ejemplo sencillo. Definamos un tipo de datos para los días de la semana:

```coq
Inductive dia : Type :=
   | lunes
   | martes
   | miercoles
   | jueves
   | viernes
   | sabado
   | domingo.
```

Este tipo de dato se llama `dia` y los valores para dicho tipo son justamente los días de la semana. Una vez definido
el tipo de dato, podemos definir funciones sofre dicho tipo. Por ejemplo:

```coq
Definition siguiente_dia (d:dia) : dia :=
   match d with
   | lunes => martes
   | martes => miercoles
   | miercoles => jueves
   | jueves => viernes
   | viernes => sabado
   | sabado => domingo
   | domingo => lunes
   end.
```

Observemos que la función en este caso incluye el tipo de los parámetros y el tipo de regreso. Como casi todos los 
lenguajes funcionales, podemos omitir dichos tipos, de hecho __Coq__ cuenta con algoritmo de inferencia de tipos que nos
ayuda a obtener los tipos. Sin embargo, para hacer legible el código y tener siempre en cuenta estos datos, lo haremos
en casi todas las funciones que definamos.

Para usar la función podemos usar dos comandos: (1) `Compute` o (2) `Example`.

`Compute` simplemente evalúa la expresión:

```coq
Compute (siguiente_dia viernes)
(* ==> sabado : dia *)

Compute (siguiente_dia (siguiente_dia sabado))
(* ==> lunes : dia *)
```

`Example` funciona como una especie de *testing* que además almacena dicha afirmación para usarla después.

```coq
Example prueba_siguiente_dia:
   (siguiente_dia (siguiente_dia sabado)) = lunes.
```

Una vez declarada la afirmación, podemos pedirle a __Coq__ que la verifique usando algo como:

```coq
Proof.
   simpl.
   reflexivity.
Qed.
```

Los detalles de esta prueba no son relevantes de momento. Básicamente lo que dice la prueba es:

*La afirmación que acabamos de declarar se puede probar reduciendo ambos lados y comprobando que llegamos a lo mismo.*

Además, podemos exportar la definición a un lenguaje *más convencional* como OCaml, Scheme o Haskell, por ejemplo. 
Retomaremos y abordaremos los usos de esto, más adelante.

![imagen](https://24.media.tumblr.com/0de7ae9a19f229fbe8484e218bddd255/tumblr_n41tadEQBL1swt01jo1_400.gif)


#### :large_orange_diamond: <ins>Booleanos</ins>

De forma similar podemos definir el tipo de dato `bool`, por su puesto con las respectivas constantes `true` y `false`.

```coq
Inductive bool : Type :=
   | true
   | false.
```

Algunas funciones sobre booleanos:

```coq
Definition negb (b:bool) : bool :=
   match b with
   | true => false
   | false => true
   end.

Definition andb (b1:bool) (b2:bool) : bool :=
   match b1 with
   | true => b2
   | false => false
   end.

Definition orb (b1:bool) (b2:bool) : bool :=
   match b1 with
   | true => true
   | false => b2
   end.
```

Por supuesto este tipo de dato, se encuentra ya definido en __Coq__.

Algunos ejemplos:

```coq
Example prueba_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example prueba_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example prueba_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example prueba_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.
```

Al igual que con otros lenguajes, como __Haskell__ podemos pedirle a __Coq__ que vuelva infijos algunos operadores:

```coq
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example prueba_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.
```

Al igual que con otros lenguajes, tenemos condicionales:

```coq
Definition negb' (b:bool): bool :=
   if b then false
   else true.

Definition andb' (b1:bool) (b2:bool) : bool :=
   if b1 then b2
   else false.

Definition orb' (b1:bool) (b2:bool) : bool :=
   if b1 then true
   esle b2.
```

---
> :point_up: **Observación:** Los condicionales en __Coq__ funciona como en cualquier otro lenguaje, sin embargo, hay una ligera
> diferencia. Notemos que el tipo `bool` fue definido por nosotros, por lo que en esencia *no es un booleano*. Sin 
> embargo, __Coq__ permite definir condicionales sobre tipos definidos inductivamente que tengan exactamente dos 
> constructores en su definición que es justo lo que ocurre con este último ejemplo.
---

![imagen](https://media.baamboozle.com/uploads/images/222104/1608271821_11661)

#### :large_orange_diamond: <ins>Tipos</ins>

Cada expresión en __Coq__ tiene un tipo que describe el tipo de elemento que evalúa. El comando `Check` permite mostrar
el tipo de una expresión.

```coq
Check true.
(* ==> true : bool *)
```

Si después de `Check` se colocan dos puntos y un tipo, __Coq__ realiza la verificación de tipos terminando con un error
en caso de que sea incorrecto.

```coq
Check true
   : bool.
Check (negb true)
   : bool.
Check negb
   : bool -> bool.
```

#### :large_orange_diamond: <ins>Tipos definidos en términos de otros</ins>

Los tipos de datos que hemos definido hasta ahora son básicamente *enumeraciones* donde las definiciones explícitamente
enumeran un conjunto finito de constructores. Otra forma de definir tipos es la siguiente:

```coq
Inductive rgb : Type :=
   | red
   | green
   | blue.

Inductive color : Type :=
   | black
   | white
   | primary (p : rbg).
```

donde el tipo `color` define constructores que pueden recibir un argumento de tipo `rgb`. Además podemos definir funciones
que hagan uso de reconocimiento de patrones usando estas nuevas definiciones:

```coq
Definition monochrome (c : color) : bool :=
   match c with
   | black => true
   | white => true
   | primary p => false
   end.

Definition isred (c : color) : bool := 
   match c with
   | black => false
   | white => false
   | primary red => true
   | primary _ => false
```

El símbolo `_` indica que no importa el valor particular que tome el argumento de `primary`. Coloquialmente lo llamamos *no me importa*.

#### :large_orange_diamond: <ins>Módulos</ins>

__Coq__ provee un sistema modular que permite organizar de mejor manera las definiciones en el código, esto es similar a
otros lenguajes, donde una vez definido un módulo podemos hacer referencia a las funciones definidas en él por medio de
notaciones de la forma `Modulo.foo`. Sin embargo a diferencia de otros lenguajes, esto no debe estar necesariamente en
archivos distintos:

```coq
Module Prueba.
   Definition b : rgb := blue.
End Prueba.

Definition b : bool := true.

Check Prueba.b : rgb.
Check b : bool.
```

#### :large_orange_diamond: <ins>Tuplas</ins>

Un constructor definido para recibir varios parámetros puede ser usados para crear un tipo *tupla*. Por ejemplo, 
consideremos la representación un arreglo de 4 bits ([nibble](https://es.wikipedia.org/wiki/Nibble)). Primero, podemos
definir el tipo `bit` que básicamente es otra forma de llamar a `bool`. Partiendo de este tipo, definimos el tipo 
`nibble`.

```coq
Inductive bit : Type :=
   | B0
   | B1.

Inductive nibble : Type :=
   | bits (b0 b1 b2 b3 : bit)

Check (bits B1 B0 B1 B0)
   : nibble.
```

Como es usual en otros lenguajes, si queremos acceder a cada elemento individualmente, podemos por supuesto, usar a 
nuestro buen amigo el reconocimiento de patrones. Por ejemplo, la función `todos_cero` revisa que en un nibble todos los
bits sean cero. 

```coq
Definition todos_cero (nb : nibble) : bool :=
   match nb with
   | (bits B0 B0 B0 B0) => true
   | (bits _ _ _ _) => false
   end.

Compute (todos_cero (bits B1 B0 B1 B0)).
(* ==> false : bool *)
Compute (todos_cero (bits B0 B0 B0 B0)).
(* ==> false : bool *)
```

#### :large_orange_diamond: <ins>Números</ins>

Otro tipo de dato interesante son los números naturales que muy probablemente nuestros lectores y lectoras ya han definido en otros lenguajes. En __Coq__ podemos definir el tipo de dato como sigue así como una función sobre el mismo:

```coq
module Naturales.

Inductive nat : Type :=
   | 0
   | S (n : nat).

Definition pred (n : nat) : nat :=
   match n with
   | 0    => 0
   | S n' => n'
   end.

End Naturales.
```

Debido a que los números naturales son un tipo de dato tan esencial, __Coq__ imprime los mismos en decimal para facilitar la lectura. 

**Nota:** Esta manera de imprimir funciona sobre el tipo `nat` definido en la biblioteca estándar, no del `nat` definido por nosotros.

```coq
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
```

Al igual que en otros lenguajes, los constructores de un tipo de dato definen funciones, tal y como las ya definidas.

```coq
Check S : nat -> nat.
Check ped : nat -> nat.
Check minustwo : nat -> nat.
```

Dada la naturaleza recursiva de este tipo de dato, es clara la necesidad de contar con un método de definición de funciones recursivas para lo cual se usa la palabra reservada `Fixpoint` en lugar de `Definition`.

```coq
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
Proof. simpl. reflexivity. Que.
```

---
> :warning: **Observación:** Al ejecutar estos *scripts* es probable que la lectora o lector hayan notado que `simpl` realmente no tiene efecto en la meta, todo el trabajo es realmente hecho por `reflexivity`. Platicaremos hacerca de esto, más adelante.
---

También es posible definir funciones con más de un argumento:

```coq
Module Naturales2.

Fixpoint suma (n : nat) (m : nat) : nat :=
   match n with
   | 0 => m
   | s n' => S (suma n' m)
   end.

Compute (suma 3 2)
(* ==> 5 : nat *)

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

End Naturales2.

Fixpoint exp (base potencia : nat) : nat :=
   match potencia with
   | 0 => S 0
   | S p => mult base (exp base p)
   end.
```

Al igual que con los booleanos, podemos definir la presedencia y asociatividad de operadores sobre los naturales:

```coq
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
```

---
> :warning: **Observación:** Las anotaciones `leve`, `associativity` y `nat_scope` dan información adicional al analizador
> sintáctico de __Coq__, básicamente indican la presedencia y asociatitividad y el alcance de estas reglas.
---

Otras funciones de comparación son:

```coq
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
Proof. simple. reflexivity. Qed.
Example prueba_menor2: menorigual 2 4 = true.
Proof. simple. reflexivity. Qed.
Example prueba_menor_3 menorigual 4 2 = false.
Proof. simple. reflexivity. Qed.

Notation "x =? y" := (soniguales x y) (at level 70) : nat_scope.
Notation "x <=? y" := (menorigual x y) (at level 70) : nat_scope.

Example prueba_menor_3' (4 <=? 2) = false.
Proof. simple. reflexivity. Qed.
```

### Pruebas por simplificación

Ahora que hemos definido algunos tipos de datos y funciones, podemos realizar algunas demostraciones sobre propiedades
de los mismos. En realidad ya lo hemos venido haciendo con cada `Example`. Dichas pruebas siempre hacen uso de `simpl`
para simplificar ambos lados de la ecuación y posteriormente usan `reflexivity` para verificar que ambos lados contienen
el mismo valor.

Esta misma técnica puede usarse para probar otras propiedades. Por ejemplo, el hecho de que 0 es el elemento neutro de la
suma puede probarse sólo observando que `0 + n` se reduce a `n` sin importar quién sea dicha `n`. Esto viene de la 
definición de suma que dimos.

```coq
Theorem suma_0_n : forall n : nat, 0 + n = n.
Proof.
   intros n. simpl. reflexivity. Qed.
```

Algo importante y que hemos estado omitiendo es el uso de `reflexivity`. Este comando es mucho más poderoso de lo que 
pareche. En los ejemplos que hemos visto, el uso de `simpl` no es realmente necesario debido a que `reflexivity` puede
realizar la simplificación automáticamente cuando verifica que los dos lados son iguales; lo añadimos para que pudieramos
notar estos pasos intermedios. De esta forma la prueba anterior quedaría como:

```coq
Theorem suma_0_n' : forall n : nat, 0 + n = n.
Proof.
   intros n. reflexivity. Qed.
```

Además, `reflexivity` permite hacer simplificaciones más complejas que las que hace `simpl`. Por ejemplo, intenta 
*desdoblar* términos reemplazandolos por sus lados derechos. La principal razón de esto es que si `reflexivity` tiene
éxito, llegamos a nuestra meta y no necesitamos más otras expresiones expandidas que se hayan creado en proceso de prueba.
Por el contrario `simpl` se utiliza cuando necesitamos comprender la nueva meta que se crea, básicamente nos permite
realizar una especie de depuración. Iremos hablando de esto poco a poco durante el curso.

Notemos además que tenemos una nueva notación llamada `Theorem`. La diferencia entre `Theorem` y `Example` es realmente
una cuestión de estilo, también existen otras como `Lemma`, `Fact`, `Remark` que básicamente significan lo mismo para
__Coq__.

También añadimos el cuantificador `forall n : nat`, lo cual indica a nuestro teorema que aplica para todos los números
naturales. De hecho, de aquí viene el uso de `intros` que básicamente marca el inicio de la prueba. Algo similar a lo que
hacemos en papel: "*Supongamos que...*".

Las palabras reservadas `intros`, `simpl` y `reflexivity` son ejemplos de *tácticas*. Una táctica es un comando que se
usa entre `Proof` y `Qed` para guiar el proceso de verificación de alguna afirmación que hagamos. Conoceremos otras
tácticas más adelante y conforme las vayamos necesitando.

### Pruebas por reescritura

Otro tipo de teorema con el que nos podemos encontrar es el siguiente:

```coq
Theorem suma_ig : forall n m : nat, n = m -> n + n = m + m.
```

Notemos que este teorema impone una restricción que nos indica que esta propiedad sólo se cumple cuando `n = m`. El
símbolo `->`, como es usual, denota una implicación. Llamaremos a esto *hipótesis*. De esta forma, además de suponer
que `n` y `m` son naturales con `intros`, también debemos suponer la hipótesis para lo cual podemos usar `H`.


```coq
Proof.
   intros n m.
   intros H.
   rewrite -> H.
   reflexivity.
Qed.
```

La línea `rewrite -> H` le indica a __Coq__ que reemplace el lado izquierdo de la hipótesis por su respectivo lado 
derecho. La flecha indica cuál de los dos lados queremos reescribir, no es una implicación.

De la misma forma podemos usar `Check` para examinar enunciados de lemas y teoremas previamente definidos, ya sea por
nosotros o por la biblioteca estándar.

```coq
Check mult_n_O.
(* ===> forall n : nat, 0 = n * 0 *)
Check mult_n_Sm.
(* ===> forall n m : nat, n * m + n = n * S m *)
```

Esto nos permitirá usar teoremas previamente demostrados junto a `rewrite`. Por ejemplo:

```coq
Theorem mult_n_0_m_0 : forall p q : nat, (p * 0) + (q * 0) = 0.
Proof.
   intros p q.
   rewrite <- mult_n_O.
   rewrite <- mult_n_O.
   reflexivity.
Qed.
```

### Pruebas por Análisis de Casos

Como la persona que está leyendo este material sabrá de cursos anteriores, no todas las demostraciones pueden realizarse
sólo reescribiendo o simplificando expresiones. Por ejemplo la siguiente prueba no puede resolverse usando las tácticas
que conocemos hasta ahora:

```coq
Theorem suma_1_neq_0_1 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n.
  simpl.
Abort.
```

El problema es que tenemos la expresión `n+1` que evidentemente no puede evaluarse si no sabemos la forma de `n`. Para
hacer esto debemos hacer una especie de reconocimiento de patrones sobre `n` y para ello debemos obtener sus posibles
constructores. Para hacer esto usaremos la táctica `destruct`.

```coq
Theorem suma_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity. 
Qed.
```

La anotación `as [| n']` es llamado *intro pattern*. Le indica a __Coq__ el nombre de las variables que debe introducir
en cada submeta separadas por un `|`. Por ejemplo, al tener dos posibles valores (0 y sucesor de un natural), se generarán dos submetas, la 
primera cuando `n = 0` que como vemos no requiere variables, por lo tanto el primer elemento de `|` es vacío, la segunda
generará un sucesor, dado que sucesor sí requiere variables, nombramos a dicha variable `n'`.

Por otro lado, la anotación `eqn:E` es simplemente el nombre que se le da a la ecuación generada por `destruct`.

Los guiones en la demostración se usan para identificar cada uno de los casos. Estos son opcionales.

[`Anterior`](../tema01/README.md) | [`Siguiente`](../tema03/README.md)
