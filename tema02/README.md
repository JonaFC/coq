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

En este material, estudiaremos las principales característica del lenguaje de programación funcional que provee __Coq__ llamado __Gallina__ así como una serie de *tácticas* básicas  que podemos usar para provar propiedades sobes los 
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
Definition siguiente_dia (d:day) : day :=
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


[`Anterior`](../tema01/README.md) | [`Siguiente`](../tema03/README.md)
