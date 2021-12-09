(** Semántica y Verificación
    Ejemplo 1
    Manuel Soto Romero
    Luis F. Benítez Lluis 
    
    Contenido:
    1 Tipos de datos y funciones
    2 Booleanos
    3 Tipos
    4 Tipos de datos definidos en términos de otros
    5 Módulos
    6 Tuplas
    
    Para acceder rápidamente a la sección deseada
    buscar la cadena ">n" donde "n" es el número de
    sección. 
    
    Material basado en los scripts 
    correspondientes al libro Logical Foundations en
    Software Foundations- Benjamin C. Pierce, et al. 
    *)
    

(** ** >1 Tipos de datos y funciones **)
Inductive dia : Type :=
   | lunes
   | martes
   | miercoles
   | jueves
   | viernes
   | sabado
   | domingo.
   
Print dia_rec.

   
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
Compute (siguiente_dia viernes).
(* ==> sabado : dia *)

Compute (siguiente_dia (siguiente_dia sabado)).
(* ==> lunes : dia *)
Example prueba_siguiente_dia:
   (siguiente_dia (siguiente_dia sabado)) = lunes.
Proof.
  simpl.
  reflexivity.
Qed.


(** ** >2 Booleanos *)


Inductive bool : Type :=
   | true
   | false.
(* Primeras versiones de conectivos booleanos*)
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
   
Example prueba_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example prueba_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example prueba_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example prueba_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Example prueba_orbGen: forall b :bool,
  true = (orb true b).
Proof.
destruct b.
  simpl. reflexivity.
  apply prueba_orb1.
Qed.
  

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Check true && false.

Example prueba_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

(*Segunda versión de conectivos booleanos *)
Definition negb' (b:bool): bool :=
   if b then false
   else true.

Definition andb' (b1:bool) (b2:bool) : bool :=
   if b1 then b2
   else false.

Definition orb' (b1:bool) (b2:bool) : bool :=
   if b1 then true
   else b2.

(* No es difícl notar que las dos versiones de los operadores
booleanos son equivalentes como funciones. Esto se podría
verificar sencillamente computando exhaustivamente las entradas
a estras funciones y corroborando que tienen la misma salida. 

Estos cómputos se pueden hacer con el comando 'Compute'. 
No obstante resulta más adecuado hacerlo formalmente. Podemos 
enunciar una aserción que afirme esto justamente. 

Nótese que esta acersión tiene una expresión de la forma
"forall" la cual ayuda a cuantificar sobre todas las posibles 
entradas. Mas adelante se abordará el manejo de expresiones 
lógicas. *)
 
Lemma neg_eq_neg': forall b: bool,
  negb b = negb' b.
Proof.
destruct b.
simpl. reflexivity.
simpl. reflexivity.
Qed.
(*La prueba de esto se puede plantear haciendo 
una búsqueda exhaustiva de sus entradas. La táctica
"destruct b" ayuda a desestructurar los valores que 
puede tener 'b'. Nótese como esto divide la meta en dos submetas,
una por cada caso.*)



(*Análogamente podemos hacer las pruebas para los
demás conectivos. Nótese como se cuantifica sobre dos
valores 'b1' y 'b2'.*)
Example andb_eq_andb': forall b1 b2: bool,
  andb b1 b2 = andb' b1 b2.
Proof.
destruct b1.
destruct b2.
simpl. reflexivity.
simpl. reflexivity.
destruct b2.
simpl. reflexivity.
simpl. reflexivity.
Qed.


Example orb_eq_orb': forall b1 b2: bool,
  orb b1 b2 = orb' b1 b2.
Proof.
destruct b1,b2; simpl; reflexivity.
Qed.



(* La primera versión hizo una caza de patrones únicamente 
en una entrada. No obstanten
el pattern matching se puede extender a más de un valor
anidando cláusulas "match...with...end". *)
Definition andb'' (b1:bool) (b2:bool) : bool :=
   match b1 with
   | true => match b2 with 
                      | true => true
                      | false => false
             end
   | false => false
   end.


(* De nuevo podemos plantear la equivalencia de esta versión
con la original.*)
Example andb_eq_andb'': forall b1 b2: bool,
  andb b1 b2 = andb'' b1 b2.
Proof.
destruct b1,b2; simpl; reflexivity.
Qed.



(* Podemos hacer el equivalente para or y automatizar
repeticiones en tácticas. Esto ayuda para hacer las pruebas
mas tolerantes a cambios pequeños y favorecer la automatización*)
Definition orb'' (b1:bool) (b2:bool) : bool:=
  match b1,b2 with 
    | true, _ => true
    | false, true => true
    | false, false => false
  end. 

Example orb_eq_orb'': forall b1 b2: bool,
  orb b1 b2 = orb'' b1 b2.
Proof.
destruct b1,b2; simpl; reflexivity.
Qed.


(** ** >3 Tipos *)   
Check true.
(* ==> true : bool *)   

Check true
   : bool.
Check (negb true)
   : bool.
Check negb
   : bool -> bool.

Check lunes.

Check bool.

(*Coq tiene algunos tipos innatos que estudiaremos mas fondo en 
clases subsecuentes. Algo interesante es que todo en Coq tiene
un tipo, inclusive tipos. *)
Check Set.
Check Type.


(** ** >4 Tipos definidos en términos de otros*)
   
Inductive rgb : Type :=
   | red
   | green
   | blue.

Inductive color : Type :=
   | black
   | white
   | primary (p : rgb).

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
   end.



(*Otro ejemplo más interesante de tipos dependientes de otros
es quizás los booleanos trivaluados. Estos booleanos corresponden
a una lógica trivaluada que extiene a los operadores de forma 
concorde al agregar un valor boolano llamado 'unknown' o
desconocido. Esta lógica pretende extender la booleana 
extendiendo la definición de sus operadores como sigue. 
Por ejemplo, la negación se puede extender como:
neg 
------
  T| F
  U| U
  F| T
Así como la conjunción:
and | T   U   F
----------------
  T | T   U   F
  U | U   U   F
  F | F   F   F
Finalmente la disyunción:
or  | T   U   F
----------------
  T | T   T   T
  U | T   U   U
  F | T   U   F

Para hacer esta definición requerimos un tipo nuevo llamado 
bool_3vl.*)
Inductive bool_3vl : Type := 
  | bol (b:bool)
  | uk.
(* Nótese que en lugar de definir un tipo completamente nuevo
usamos el tipo bool para mantener cierta correspondencia con los
booleanos definidos anteriormente. Para poder distinguir
entre estos booleanos ternarios y los originales se mantiene
una etiqueta "bol" que distingue uno de otro. Para acceder al 
valor booleano en un booleano ternario se define la función 
proyección. Nótese que esta función requiere definir
un valor para uk, el cual se convino a false. Alternativamente
esto se puede plantear con un tipo opción que ofrezca un valor de
error para este caso, pero esta idea se elaborará mas adelante. 
*)

Definition prj_3vl (c:bool_3vl):bool := 
  match c with 
    | bol b => b
    | uk => false(*error*)
  end.
Compute prj_3vl (bol true).

(*Con este tipo se pueden replantear los conectivos para que 
se ajusten de manera concorde. Si bien esto se puede hacer
con un análisis exhaustivo de casos, resulta natural tomar
pauta de la función negb que ya computa esto para valores 
puramente booleanos. *)
Definition negb_3vl (c: bool_3vl): bool_3vl:=
  match c with
    | bol b => bol (negb b)
    | uk => uk
   end.

Compute negb_3vl (bol true).

(* Ver que negb_3vl en efecto extiende a negb
se puede expresar por medio de una aserción y probar*)
Proposition negb_prj_3vl: forall b: bool,
  prj_3vl (negb_3vl (bol b))= negb b.
Proof.
  destruct b; simpl; reflexivity.
Qed.


(** ** >5 Módulos*)

Module Prueba.
   Definition b : rgb := blue.
   Check b.
End Prueba.

Definition b : bool := true.
Check Prueba.b.
Check b.
  
  
(** ** >6 Tuplas*) 
Inductive bit : Type :=
   | B0
   | B1.

Inductive nibble : Type :=
   | bits (b0 b1 b2 b3 : bit).

Check (bits B1 B0 B1 B0): nibble.
   
Definition todos_cero (nb : nibble) : bool :=
   match nb with
   | (bits B0 B0 B0 B0) => true
   | (bits _ _ _ _) => false
   end.

Compute (todos_cero (bits B1 B0 B1 B0)).
(* ==> false : bool *)
Compute (todos_cero (bits B0 B0 B0 B0)).
(* ==> false : bool *)


(*Podemos definir una función que invierta los valores en 
un nibble  TAREA MORAL*)
Definition rev_nibble (nb : nibble): nibble. Admitted. 

Compute rev_nibble (bits B0 B1 B0 B1).

   
   
  