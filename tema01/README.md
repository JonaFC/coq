[`Introducción a la Verificación Formal con Coq`](../README.md) > `Tema 1`

## Introducción

Desarrollar software hoy es una tarea difícil que hoy en día debido a todo lo que implica y que se encuentra en 
crecimiento constante. Entre los objetivos más importantes a tomar en cuenta en un desarrollo se encuentra el cuidado de
la calidad del producto de software. 

---
> :green_book: **Definición (Calidad)**  _La calidad de un producto de software es el grado en que éste satisface las 
> necesidades y expectativas del usuario cuando se usa en las condiciones especificadas._
---

Para obtener software de calidad es necesario que todos los productos que se generen en el desarrollo sean consistentes
y no tengan defectos.

---
> :green_book: **Definición (Defecto)**  _Un defecto es el resultado de un error cometido por un desarrollador al 
> generar un producto._
---

Los defectos, por más pequeños que sean, como faltas de ortografía o de dedo, pueden ocasionar problemas severos en el
software al presentar inconsistencias o respuestas impredecibles. Adicional a esto, el aumento en el volumen de los 
datos e información que manejan los sistemas hoy en día, hacen que cuidar la calidad sea una tarea esencial en cualquier
desarrollo.

El no cuidar la calidad puede ocasionar pérdidas monetarias, falta de precisión en cálculos o incluso muertes. Las 
prácticas que se usan para comprobar la calidad del software son principalmente la *verificación* y la *validación*.

---
> :point_up: _Verificar un producto de software tiene por objetivo asegurar que no tenga defectos introducidos por el
> desarrollador_.
---
> :point_up: _Validar el software es asegurarse de que hace lo que el usuario espera que haga_ 
---

La validación es una tarea que puede asesgurarse con herramientas de *testing* entre las cuales destacan el uso de 
pruebas unitarias. Mismas que los departamentos de Calidad en distintas empresas usan así como el apoyo por medio de
historias de usuario o casos de uso. Sin embargo la verificación es más complicada.

Los Científicos de la Computación y los Ingenieros de Software, han trabajado durante años de la mano desarrollando
técnicas y mecanismos que facilitan la verificación del software tales como el desarrollo de Métodos de trabajo (Scrum 
por ejemplo), diseño de patrones de sieño (El Modelo-Vista-Controlador, por ejemplo), diseño de distintos estilos de
programación, lenguajes de programación de propósito específico así como investigación y técnicas matemáticas que 
permiten especificar y razonar sobre de propiedades que debe cumplir el software y que permitan verificar las mismas. En 
este curso nos concentraremos en el último punto.

![imagen](https://external-content.duckduckgo.com/iu/?u=https%3A%2F%2Fwww.esds.co.in%2Fblog%2Fwp-content%2Fuploads%2F2019%2F03%2Ftesting.gif&f=1&nofb=1)

Nos enfocaremos en el estudio de tres cosas:

- Lógica para justificar afirmaciones sobre programas.
- El uso de asistentes de prueba para construir y probar argumentos lógicos.
- El uso del estilo de programación funcional que nos permita razonar de forma simple sobre los programas así como
  servir como puente entre la lógica y la programación.

### :large_orange_diamond: <ins>Lógica</ins>

La lógica es un campo de estudio que básicamente estudia *pruebas* (probar que una proposición es verdadera partiendo
de otros argumentos que sabemos que son correctos). Durante años, se ha discutido cómo la lógica juega un papel muy
importante en la Ciencia de la Computación:

- Manna y Waldinger lo llamaron "*El Cálculo de las Ciencias de la Computación"*

- Halpern et al, en su artículo *Sobre la eficacia inusual de la lógica en Ciencias de la Computación* catalogca
  descenas de aplicaciones de la lógica a nuestro campo. En particular incluye la siguiente observación:

  > *La lógica ha resultado ser significativamente más útil en las Ciencias de la Computación que en las matemáticas*

En particular, como quién este leyendo esto puede confirmar, las pruebas por inducción se encuentran presenten en casi
todas las ramas de la ciencia de la computación.

Muy probablemente todas estas técnicas se han estudiado en otros cursos como Estructuras Discretas, Lenguajes de 
Programación, Análisis de algoritmos, etc. Sin embargo, en este material, revisaremos estos conceptos con un poco más
de detalle.

![imagen](https://external-content.duckduckgo.com/iu/?u=http%3A%2F%2Fmedia2.intoday.in%2Findiatoday%2Fimages%2Fstories%2F2017April%2Fgifmain_041017061955.gif&f=1&nofb=1)

### :large_orange_diamond: <ins>Asistentes de prueba</ins>

Estas ideas que pretenden conectar a la Lógica con la Computación no van en un único sentido, es decir, las Ciencias de
la Computación también han realizado diversos aportes a la Lógica. Uno de estos aportes es justamente el desarrollo de
herramientas de software que permiten construir pruebas por medio de proposiciones lógicas. 

Este tipo de herramientas se dividen, en general, en dos grandes categorías:

- **Demostradores Automáticos**. El usuario proporciona una proposición y el programa nos devuelve una respuesta (
  verdadero, falso o algún tipo de error). En los últimos años se han creado una gran variedad de demostradores
  automáticos, que aunque son diseñados con un dominio específico, han madurado enormemente y se usan hoy en día en 
  distintas áreas.

  Ejemplos de estas herramientas son:

  - Solucionadores SAT
  - Solucionadores SMT
  - Verificadores de Modelos

- **Asistentes de Prueba**. Son herramientas híbridas que automatizan los aspectos más comunes en la construcción de una
  demostración que requieren de la guía humana para aspectos más complejos.

  Ejemplos de estas herramientas son:

  - Isabelle
  - Agda
  - Twelf
  - ACL2
  - PVS
  - Coq

En este curso trabajaremos con el asistente de pruebas __Coq__. Este asistente ha estado en desarrolo desde los años 80
y en los últimos años, ha mostrado ser de gran utilidad en distintas áreas, tanto de la investigación como de la 
industria. Proporciona además, un excelente entorno para lograr un razonamiento formal verificado por computadora.

Además, el núcleo de __Coq__ porpociona utilerías de alto nivel que permiten desarrollar demostraciones, incluída una
poderosa biblioteca de definiciones y lemas comunes, tácticas para construir pruebas complejas casi de manera 
automática y un lenguaje de programación de propósito específico para definir nuevas tácticas en problemas específicos.

Ejemplos de aplicaciones:

- Como una plataforma para modelar lenguajes de programación.

- Como un ambiente para desarrollar formalmente software y hardware certificado.

- Como un ambiente *real* de programación funcional con tipos dependientes.

- Como un asistente de prueba para la lógica de primer orden.

El nombre de __Coq__ fue elegido pues:

- Muchos lenguajes de programación usan nombres de animales como Caml, Elan, Foc y Phox. En francés Coq significa 
  "Gallo".

- Suena como las iniciales del Cálculo de Construcciones (CoC) en el cuál está basado.

- El gallo es el símbolo nacional de Francia.

- C-o-q son las primeras letras del nombre de Thierry Coquand, uno de los primeros desarrolladores.

![imagen](https://c.tenor.com/_y7rV7tM4XQAAAAM/gallo-claudio.gif)

### :large_orange_diamond: <ins>Programación Funcional</ins>

La programación funcional se basa en el Cálculo Lambda y la Teoría de Categorías. En este estilo la
programación se compone de la definición de funciones que actúan como *miembros de primera clase*, es
decir, que se comportan como cualquier otro valor en el lenguaje.

Los cálculos se dan aplicando reducciones y combinando funciones ya sea pasándose entre ellas como
parámetro, devolviéndolas como resultando o incluso componiéndolas tal y como se hace en matemáticas.
El principal representante de este estilo es __Haskell__. Por ejemplo:

```haskell
module Ejemplo where

suma :: Int -> Int
suma 0 = 0
suma n = n + suma (n-1)
```

El código anterior muestra la definición de una función que suma los primeros `n` naturales. Una forma
de ejecutar la función podría ser `suma 5`. Se aprecia el uso de
definiciones y de la recursión.

Para los propósitos de este curso, la programación funcional juega un rol importante. Funciona justamente como un puente
entre la lógica y las ciencias de la computación. De hecho, Coq se puede ver como una combinación de un lenguaje funcional
con un conjunto de pruebas que permiten declarar y probar condiciones lógica. Más aún, cuando miramos más de cerca, 
podemos notar que en realidad estos dos aspectos son parte de la misma *maquinaria* dicho de otra forma *las pruebas
son programas*.

![imagen](https://external-content.duckduckgo.com/iu/?u=http%3A%2F%2Fcdn.playbuzz.com%2Fcdn%2F6b1cd6a9-4e6f-4b8e-b320-e3b33f8d0a65%2F8e08b3b4-d037-4da5-99f9-de3215ea37c0.gif&f=1&nofb=1)


[`Anterior`](../README.md) | [`Siguiente`](../semana02/README.md)
