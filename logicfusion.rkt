#lang eopl
;; =============================================================================
;; Proyecto Final: LogicFusion
;; Curso: Fundamentos de Lenguajes de Programación
;; Integrantes:
;;   - Juan Manuel Muñoz Delgado - Código: 2436424
;;   - Juan Camilo Ramos Hoyos- Código: 2438212
;;   - Andres Felipe Muñoz Moreno - Código: 2438908
;;   - Emmanuel Paez Hurtado - Código: 2419847
;; 
;; Repositorio: https://github.com/juanmunozdelgado-oss/Proyecto-LogicFusion.git
;; Declaración de IA: Se utilizó asistencia de LLM como apoyo de consulta y 
;;                    estructuración según las guías del curso.
;;
;; 
;; Módulo Inicial:
;;  - Especificación Léxica y Gramatical Base (GLOBALS / PROGRAM)[cite: 1, 12]
;;  - Sistema de Ambientes y Referencias con Soporte para Mutabilidad y Constantes[cite: 2, 4, 189]
;;  - Validación Parcial de Tipos Primitivos con Coerción int -> float[cite: 2]
;;  - Sintaxis e Representación Interna del Módulo SAT (Forma Normal Conjuntiva)[cite: 5, 6, 12]
;;  - Evaluador Base de Declaraciones y Expresiones Primarias[cite: 1, 265]
;; =============================================================================

;; =============================================================================
;; 1. ESPECIFICACIÓN LÉXICA (SLLGEN)
;; =============================================================================
(define scanner-spec-logicfusion
  '(
    ;; 1. Espacios en blanco (se ignoran)[cite: 20]
    (white-sp (whitespace) skip)

    ;; 2. Comentarios de una sola línea iniciados con % (se ignoran hasta el salto de línea)[cite: 20]
    (comment ("%" (arbno (not #\newline))) skip)

    ;; 3. Identificadores: Comienzan con letra y aceptan letras, dígitos, _ o ?[cite: 1, 20]
    (identifier (letter (arbno (or letter digit "_" "?"))) symbol)

    ;; 4. Flotantes positivos: Requieren al menos un dígito antes y después del punto[cite: 20]
    (float-number (digit (arbno digit) "." digit (arbno digit)) number)

    ;; 5. Enteros positivos: Secuencia de uno o más dígitos[cite: 20]
    (number (digit (arbno digit)) number)

    ;; 6. Cadenas de caracteres: Delimitadas entre comillas dobles[cite: 2, 20]
    (string-lit ("\"" (arbno (not #\")) "\"") string)
   ))

;; =============================================================================
;; 2. ESPECIFICACIÓN GRAMATICAL (SLLGEN)
;; =============================================================================
(define grammar-spec-logicfusion
  '(
    ;; 1. Estructura Principal del Programa (Bloque GLOBALS y función ejecutable main)[cite: 1, 2]
    (program ("GLOBALS" "{" (arbno global-decl) "}" 
              "PROGRAM" "{" "proc" "main" "(" ")" "{" "return" expression ";" "}" "}")
             a-program)

    ;; 2. Declaraciones Globales (Variables mutables y constantes inmutables)[cite: 2]
    (global-decl (type-spec identifier "=" expression ";") var-decl)
    (global-decl ("const" type-spec identifier "=" expression ";") const-decl)

    ;; 3. Especificación de Tipos Primitivos y Tipo SAT[cite: 2]
    (type-spec ("int") int-type)
    (type-spec ("float") float-type)
    (type-spec ("string") string-type)
    (type-spec ("bool") bool-type)
    (type-spec ("void") void-type)
    (type-spec ("sat") sat-type)
    (type-spec ("list" "<" type-spec ">") list-type)
    (type-spec ("vector" "<" type-spec ">") vector-type)

    ;; 4. Expresiones Primarias y Literales[cite: 1, 2]
    (expression (float-number) float-exp)
    (expression (number) lit-exp)
    (expression (string-lit) string-exp)
    (expression (bool-val) bool-exp)
    (expression (identifier) var-exp)
    
    ;; Literales Booleanos True / False[cite: 2]
    (bool-val ("True") true-bool)
    (bool-val ("False") false-bool)

    ;; 5. Asignación con palabra reservada set para mantener gramática LL(1)[cite: 3, 178]
    (expression ("set" identifier "->" expression) assign-exp)

    ;; 6. Operaciones binarias y listas inmutables
    ;; Después de la primera expresión, el operador, la coma o el cierre
    ;; distinguen una operación binaria de un literal de lista.
    (expression ("(" expression paren-tail) paren-exp)

    (paren-tail (primitive-op expression ")") binop-tail)
    (paren-tail ("," expression (arbno "," expression) ")") list-tail)
    (paren-tail (")") singleton-tail)

    ;; Primitivas de listas inmutables del Adendo 5
    (expression ("empty") empty-list-exp)
    (expression ("empty?" "(" expression ")") empty-list-test-exp)
    (expression ("make-list" "(" expression "," expression ")") make-list-exp)
    (expression ("list?" "(" expression ")") list-test-exp)
    (expression ("head" "(" expression ")") list-head-exp)
    (expression ("tail" "(" expression ")") list-tail-exp)
    (expression ("append" "(" expression "," expression ")") list-append-exp)
    (expression ("ref-list" "(" expression "," expression ")") list-ref-exp)
    (expression ("length" "(" expression ")") list-length-exp)

    ;; Literales y primitivas de vectores mutables del Adendo 7
    (expression ("[" expression (arbno "," expression) "]") vector-literal-exp)
    (expression ("vector?" "(" expression ")") vector-test-exp)
    (expression ("make-vector" "(" expression ")") make-vector-exp)
    (expression ("ref-vector" "(" expression "," expression ")") vector-ref-exp)
    (expression ("set-vector" "(" expression "," expression "," expression ")") vector-set-exp)
    (expression ("append-vector" "(" expression "," expression ")") vector-append-exp)
    (expression ("delete-val-vector" "(" expression "," expression ")") vector-delete-exp)
    (expression ("insert-val-vector" "(" expression "," expression "," expression ")") vector-insert-exp)

    ;; Primitivas de cadenas
    (expression ("longitud" "(" expression ")") string-length-exp)
    (expression ("concatenar" "(" expression "," expression ")") string-concat-exp)

    (primitive-op ("+") add-op)
    (primitive-op ("-") sub-op)
    (primitive-op ("*") mul-op)
    (primitive-op ("/") div-op)
    (primitive-op ("==") eq-op)
    (primitive-op ("!=") neq-op)
    (primitive-op (">") gt-op)
    (primitive-op ("<") lt-op)
    (primitive-op (">=") gte-op)
    (primitive-op ("<=") lte-op)

    ;; 7. Sintaxis FNC (Módulo SAT)[cite: 5]
    ;; Permite crear instancias FNC n ( (lit or lit) and (lit) ... )[cite: 5]
    (expression ("FNC" number "(" clausula-sat (arbno "and" clausula-sat) ")") fnc-exp)
    ;; separated-list permite reconocer () y reportar semánticamente
    ;; que una cláusula SAT no puede estar vacía.
    (clausula-sat ("(" (separated-list literal-sat "or") ")") sat-clause)
    (literal-sat (number) pos-literal)
    (literal-sat ("-" number) neg-literal)


    
    ;; 8. Estructuras de control y bloques secuenciales
    (expression ("while" "[" expression "]" "{" expression "}") while-exp)
    (expression ("begin" expression (arbno ";" expression) "end") begin-exp)
    (expression ("if" "[" expression "]" "{" expression "}" "else" "{" expression "}") if-exp)
    (expression ("for" "[" expression ";" expression ";" expression "]" "{" expression "}") for-exp)
    (expression ("switch" "[" expression "]" "{" (arbno "case" expression ":" expression ";") "default" ":" expression "}") switch-exp)
    (expression ("BLOCK" "LOCALS" "{" (arbno identifier "=" expression ";") "}" "{" expression "}") block-exp)

    ;; 9. Procedimientos
    (expression ("lambda" "(" (arbno identifier) ")" expression) lambda-exp)
    (expression ("call" expression "(" (arbno expression) ")") call-exp)
    (expression ("letrec" identifier "=" expression "in" expression) letrec-exp)
    (expression ("solve" "(" expression ")") solve-exp)
   ))

;; Generación automática de tipos de datos abstractos (Datatypes) e Interpretador SLLGEN[cite: 1, 22]
(sllgen:make-define-datatypes scanner-spec-logicfusion grammar-spec-logicfusion)

(define scan&parse
  (sllgen:make-string-parser scanner-spec-logicfusion grammar-spec-logicfusion))

;; =============================================================================
;; 3. GESTIÓN DE MEMORIA Y AMBIENTES (Clase 16 - #lang eopl)[cite: 171, 189, 193]
;; =============================================================================

;; Un tipo puede ser simple, como int, o compuesto, como (list int).
(define type-descriptor?
  (lambda (type)
    (or (symbol? type)
        (and (list? type)
             (not (null? type))))))

;; Indica si un descriptor representa una lista.
(define list-type-descriptor?
  (lambda (type)
    (and (list? type)
         (= (length type) 2)
         (eqv? (car type) 'list))))

;; Obtiene T a partir de un descriptor (list T).
(define list-element-type
  (lambda (type)
    (if (list-type-descriptor? type)
        (cadr type)
        #f)))

;; Reconoce descriptores (vector T) y obtiene el tipo T.
(define vector-type-descriptor?
  (lambda (type)
    (and (list? type)
         (= (length type) 2)
         (eqv? (car type) 'vector))))

(define vector-element-type
  (lambda (type)
    (if (vector-type-descriptor? type)
        (cadr type)
        #f)))

;; Tipo de dato Referencia (Representa un L-valor en memoria con celda mutable en vector)[cite: 185, 189]
;;  - is-const?: Marca #t si es constante (inmutable) o #f si es variable[cite: 2]
;;  - type-sym: Descriptor del tipo declarado ('int, 'float, '(list int), etc.)
;;  - val-cell: Vector de 1 posición para almacenamiento mutable del R-valor[cite: 185, 189]
(define-datatype reference reference?
  (a-ref (is-const? boolean?)
         (type-sym type-descriptor?)
         (val-cell vector?)))

;; Obtiene el R-valor almacenado dentro de la referencia[cite: 187, 190]
(define deref
  (lambda (ref)
    (cases reference ref
      (a-ref (is-const? type-sym val-cell)
        (vector-ref val-cell 0)))))

;; Modifica el valor en memoria verificando inmutabilidad y compatibilidad de tipo[cite: 2, 187, 191]
(define setref!
  (lambda (ref new-val)
    (cases reference ref
      (a-ref (is-const? type-sym val-cell)
        (cond
          (is-const?
           (eopl:error 'setref! "Error: Intento de modificar la constante inmutable"))
          (else
           (let ((final-val (check-and-coerce-type type-sym new-val)))
             (vector-set! val-cell 0 final-val))))))))

;; Tipo de dato Ambiente (Almacena listas paralelas de símbolos e identificadores a referencias)[cite: 193]
(define-datatype environment environment?
  (empty-env-record)
  (extended-env-record
   (syms (list-of symbol?))
   (refs (list-of reference?))
   (env environment?)))

(define empty-env
  (lambda ()
    (empty-env-record)))

(define extend-env
  (lambda (syms refs env)
    (extended-env-record syms refs env)))

;; Busca una variable en el ambiente y retorna su Referencia (L-valor)[cite: 185, 197, 198]
(define apply-env-ref
  (lambda (env search-sym)
    (cases environment env
      (empty-env-record ()
        (eopl:error 'apply-env-ref "Variable no encontrada: ~s" search-sym))
      (extended-env-record (syms refs saved-env)
        (let ((pos (list-index search-sym syms)))
          (if pos
              (list-ref refs pos)
              (apply-env-ref saved-env search-sym)))))))

;; Busca una variable en el ambiente y retorna su R-valor (deref)[cite: 197, 198]
(define apply-env
  (lambda (env search-sym)
    (deref (apply-env-ref env search-sym))))

;; Función auxiliar para obtener el índice de un elemento dentro de una lista
(define list-index
  (lambda (sym lst)
    (cond
      ((null? lst) #f)
      ((eqv? sym (car lst)) 0)
      (else (let ((arg (list-index sym (cdr lst))))
              (if arg (+ arg 1) #f))))))

;; =============================================================================
;; 4. SISTEMA DE TIPOS Y RECONOCEDOR ESTRUCTURAL SAT (#lang eopl)
;; =============================================================================

;; Representación Interna para Instancias SAT (Datatype propio, no cadenas)[cite: 5, 6]
(define-datatype sat-value sat-value?
  (sat-instance (num-vars integer?)
                (clauses list?)))

;; Representación interna de una lista inmutable.
;; element-type guarda el tipo de sus elementos o unknown para empty.
(define-datatype list-value list-value?
  (a-list (element-type type-descriptor?)
          (elements list?)))

;; La celda conserva la identidad mutable aunque cambie el tamaño del vector.
;; Su posición cero contiene el vector de Racket con los elementos actuales.
(define-datatype vector-value vector-value?
  (a-vector (element-type type-descriptor?)
            (cell vector?)))

;; Valida una lista frente a su tipo declarado.
(define check-list-type
  (lambda (expected-type val)
    (if (not (list-value? val))
        (eopl:error 'check-list-type
                    "Error de Tipo: Se esperaba una lista")
        (cases list-value val
          (a-list (actual-type elements)
            (let ((expected-element-type
                   (list-element-type expected-type)))
              (cond
                ;; list<void> permite elementos de cualquier tipo.
                ((eqv? expected-element-type 'void)
                 (a-list 'void elements))

                ;; empty adopta el tipo declarado de la variable.
                ((eqv? actual-type 'unknown)
                 (a-list expected-element-type elements))

                ;; La lista ya tiene el tipo correcto.
                ((equal? expected-element-type actual-type)
                 val)

                (else
                 (eopl:error
                  'check-list-type
                  "Error de Tipo: Se esperaba list<~s> pero se obtuvo list<~s>"
                  expected-element-type
                  actual-type)))))))))

;; Verifica que un valor sea una lista de LogicFusion.
(define require-list
  (lambda (who val)
    (if (list-value? val)
        val
        (eopl:error who
                    "Error de Tipo: Se esperaba una lista"))))

;; Obtiene los elementos y rechaza las listas vacías.
(define require-nonempty-elements
  (lambda (who val)
    (cases list-value (require-list who val)
      (a-list (element-type elements)
        (if (null? elements)
            (eopl:error who "La lista está vacía")
            elements)))))

;; Comprueba que todos los valores tengan el tipo esperado.
;; El tipo void acepta valores heterogéneos.
(define list-elements-have-type?
  (lambda (values expected-type)
    (cond
      ((null? values) #t)
      ((eqv? expected-type 'void) #t)
      ((equal? (get-value-type (car values)) expected-type)
       (list-elements-have-type? (cdr values) expected-type))
      (else #f))))

;; Construye una lista y valida la homogeneidad de sus elementos.
(define make-list-value
  (lambda (values expected-type)
    (let ((element-type
           (cond
             ((list-type-descriptor? expected-type)
              (list-element-type expected-type))
             ((null? values) 'unknown)
             (else
              (get-value-type (car values))))))
      (if (list-elements-have-type? values element-type)
          (a-list element-type values)
          (eopl:error
           'make-list-value
           "Error de Tipo: Los elementos de la lista deben ser homogéneos")))))

;; Construye una nueva lista agregando un elemento al inicio.
(define prepend-list-value
  (lambda (element list-val expected-type)
    (let ((checked-list
           (if (list-type-descriptor? expected-type)
               (check-list-type expected-type
                                (require-list 'make-list list-val))
               (require-list 'make-list list-val))))
      (cases list-value checked-list
        (a-list (actual-type elements)
          (let ((result-type
                 (if (eqv? actual-type 'unknown)
                     (get-value-type element)
                     actual-type)))
            (if (or (eqv? result-type 'void)
                    (equal? result-type (get-value-type element)))
                (a-list result-type (cons element elements))
                (eopl:error
                 'make-list
                 "Error de Tipo: El elemento no coincide con el tipo ~s"
                 result-type))))))))

;; Concatena dos listas sin modificar las originales.
(define append-list-values
  (lambda (left right expected-type)
    (let ((checked-left
           (if (list-type-descriptor? expected-type)
               (check-list-type expected-type (require-list 'append left))
               (require-list 'append left)))
          (checked-right
           (if (list-type-descriptor? expected-type)
               (check-list-type expected-type (require-list 'append right))
               (require-list 'append right))))
      (cases list-value checked-left
        (a-list (left-type left-elements)
          (cases list-value checked-right
            (a-list (right-type right-elements)
              (let ((result-type
                     (cond
                       ((eqv? left-type 'unknown) right-type)
                       ((eqv? right-type 'unknown) left-type)
                       ((or (eqv? left-type 'void)
                            (eqv? right-type 'void))
                        'void)
                       ((equal? left-type right-type) left-type)
                       (else
                        (eopl:error
                         'append
                         "Error de Tipo: Las listas tienen tipos incompatibles")))))
                (a-list result-type
                        (append left-elements right-elements))))))))))

;; Verifica que un valor sea un vector de LogicFusion.
(define require-vector
  (lambda (who val)
    (if (vector-value? val)
        val
        (eopl:error who
                    "Error de Tipo: Se esperaba un vector"))))

;; Comprueba la homogeneidad de los elementos de un vector.
(define vector-elements-have-type?
  (lambda (values expected-type)
    (cond
      ((null? values) #t)
      ((eqv? expected-type 'void) #t)
      ((equal? (get-value-type (car values)) expected-type)
       (vector-elements-have-type? (cdr values) expected-type))
      (else #f))))

;; Convierte una lista de Racket en almacenamiento vectorial mutable.
(define values->vector
  (lambda (values)
    (list->vector values)))

;; Construye un vector literal y valida el tipo de sus elementos.
(define make-vector-literal-value
  (lambda (values expected-type)
    (let ((element-type
           (if (vector-type-descriptor? expected-type)
               (vector-element-type expected-type)
               (get-value-type (car values)))))
      (if (vector-elements-have-type? values element-type)
          (a-vector element-type (vector (values->vector values)))
          (eopl:error
           'vector-literal
           "Error de Tipo: Los elementos del vector deben ser homogéneos")))))

;; Valida un vector frente al tipo declarado vector<T>.
(define check-vector-type
  (lambda (expected-type val)
    (cases vector-value (require-vector 'check-vector-type val)
      (a-vector (actual-type cell)
        (let ((expected-element-type
               (vector-element-type expected-type)))
          (cond
            ;; Una vista vector<void> no debe borrar el tipo real de un
            ;; vector compartido. Así no se puede modificar vector<int>
            ;; con valores de otro tipo mediante un alias vector<void>.
            ((eqv? expected-element-type 'void)
             val)
            ((equal? expected-element-type actual-type)
             val)
            (else
             (eopl:error
              'check-vector-type
              "Error de Tipo: Se esperaba vector<~s> pero se obtuvo vector<~s>"
              expected-element-type
              actual-type))))))))

;; Valor inicial empleado por make-vector según el tipo declarado.
(define default-vector-value
  (lambda (element-type)
    (cond
      ((eqv? element-type 'int) 0)
      ((eqv? element-type 'float) 0.0)
      ((eqv? element-type 'string) "")
      ((eqv? element-type 'bool) #f)
      ((eqv? element-type 'void) 0)
      (else
       (eopl:error
        'make-vector
        "No existe un valor inicial para el tipo ~s"
        element-type)))))

;; Crea un vector de tamaño n usando el tipo declarado como contexto.
(define make-sized-vector-value
  (lambda (count expected-type)
    (cond
      ((not (and (integer? count) (exact? count)))
       (eopl:error 'make-vector
                   "Error de Tipo: El tamaño debe ser un entero"))
      ((< count 0)
       (eopl:error 'make-vector
                   "El tamaño no puede ser negativo: ~s"
                   count))
      ((not (vector-type-descriptor? expected-type))
       (eopl:error 'make-vector
                   "No se puede inferir el tipo del vector"))
      (else
       (let ((element-type (vector-element-type expected-type)))
         (a-vector
          element-type
          (vector
           (make-vector count
                        (default-vector-value element-type)))))))))

;; Comprueba el tipo de un valor antes de almacenarlo en un vector.
(define check-vector-element
  (lambda (who element-type val)
    (if (or (eqv? element-type 'void)
            (equal? element-type (get-value-type val)))
        val
        (eopl:error
         who
         "Error de Tipo: Se esperaba un elemento ~s pero se obtuvo ~s"
         element-type
         (get-value-type val)))))

;; Valida índices. insert-val-vector admite la posición final.
(define validate-vector-index
  (lambda (who position size allow-end?)
    (cond
      ((not (and (integer? position) (exact? position)))
       (eopl:error who
                   "Error de Tipo: El índice debe ser un entero"))
      ((or (< position 0)
           (if allow-end? (> position size) (>= position size)))
       (eopl:error who "Índice fuera de rango: ~s" position))
      (else position))))

;; Agrega un elemento al final conservando la identidad del vector.
(define append-vector-value!
  (lambda (val new-value)
    (cases vector-value (require-vector 'append-vector val)
      (a-vector (element-type cell)
        (let* ((checked
                (check-vector-element
                 'append-vector element-type new-value))
               (elements (vector->list (vector-ref cell 0))))
          (vector-set! cell 0
                       (list->vector (append elements (list checked))))
          val)))))

;; Operaciones auxiliares sobre listas para cambiar el tamaño del vector.
(define remove-list-position
  (lambda (values position)
    (if (= position 0)
        (cdr values)
        (cons (car values)
              (remove-list-position (cdr values) (- position 1))))))

(define insert-list-position
  (lambda (values position new-value)
    (if (= position 0)
        (cons new-value values)
        (cons (car values)
              (insert-list-position
               (cdr values) (- position 1) new-value)))))

;; Elimina una posición y desplaza los elementos siguientes.
(define delete-vector-value!
  (lambda (val position)
    (cases vector-value (require-vector 'delete-val-vector val)
      (a-vector (element-type cell)
        (let* ((old-storage (vector-ref cell 0))
               (old-size (vector-length old-storage))
               (valid-position
                (validate-vector-index
                 'delete-val-vector position old-size #f)))
          (vector-set!
           cell 0
           (list->vector
            (remove-list-position
             (vector->list old-storage) valid-position)))
          val)))))

;; Inserta un elemento y desplaza a la derecha los elementos siguientes.
(define insert-vector-value!
  (lambda (val position new-value)
    (cases vector-value (require-vector 'insert-val-vector val)
      (a-vector (element-type cell)
        (let* ((checked
                (check-vector-element
                 'insert-val-vector element-type new-value))
               (old-storage (vector-ref cell 0))
               (old-size (vector-length old-storage))
               (valid-position
                (validate-vector-index
                 'insert-val-vector position old-size #t)))
          (vector-set!
           cell 0
           (list->vector
            (insert-list-position
             (vector->list old-storage) valid-position checked)))
          val)))))

;; El escáner conserva las comillas del lexema. El intérprete almacena
;; únicamente los caracteres contenidos entre ellas.
(define normalize-string-literal
  (lambda (datum)
    (let ((size (string-length datum)))
      (if (and (>= size 2)
               (char=? (string-ref datum 0) #\")
               (char=? (string-ref datum (- size 1)) #\"))
          (substring datum 1 (- size 1))
          datum))))

;; Valida los argumentos de longitud y concatenar.
(define require-string
  (lambda (who val)
    (if (string? val)
        val
        (eopl:error who
                    "Error de Tipo: Se esperaba una cadena"))))

;; Infiere el tipo dinámico de un R-valor en tiempo de ejecución[cite: 2]
(define get-value-type
  (lambda (val)
    (cond
      ((and (integer? val) (exact? val)) 'int)
      ((real? val) 'float)
      ((string? val) 'string)
      ((boolean? val) 'bool)
      
      ((sat-value? val) 'sat)
      ((proc-val? val) 'proc)
      ((list-value? val)
       (cases list-value val
         (a-list (element-type elements)
           (list 'list element-type))))
      ((vector-value? val)
       (cases vector-value val
         (a-vector (element-type cell)
           (list 'vector element-type))))
      (else 'unknown))))

;; Revisa coincidencia de tipos y realiza conversión implícita de int a float.
(define check-and-coerce-type
  (lambda (expected-type val)
    (if (eqv? expected-type 'void)
        val
        (let ((val-type (get-value-type val)))
          (cond
            ;; Las listas necesitan revisar también el tipo de sus elementos.
            ((list-type-descriptor? expected-type)
             (check-list-type expected-type val))

            ;; Los vectores validan el tipo de sus elementos.
            ((vector-type-descriptor? expected-type)
             (check-vector-type expected-type val))

            ;; Tipos simples iguales.
            ((equal? expected-type val-type)
             val)

            ;; Coerción int -> float para valores primitivos.
            ((and (eqv? expected-type 'float)
                  (eqv? val-type 'int))
             (exact->inexact val))

            (else
             (eopl:error
              'check-and-coerce-type
              "Error de Tipo: Se esperaba ~s pero se obtuvo ~s"
              expected-type
              val-type)))))))

;; Extrae el entero positivo o negativo según la producción de literal FNC[cite: 5]
(define extract-literal-val
  (lambda (lit-ast)
    (cases literal-sat lit-ast
      (pos-literal (num) num)
      (neg-literal (num) (- num)))))

;; Convierte un AST de cláusula SAT a una lista de enteros en Scheme[cite: 5]
(define extract-clause
  (lambda (clause-ast)
    (cases clausula-sat clause-ast
      (sat-clause (literals)
        (map extract-literal-val literals)))))

;; Valida un literal con respecto al número de variables declarado.
(define validate-sat-literal
  (lambda (literal num-vars)
    (cond
      ((not (and (integer? literal) (exact? literal)))
       (eopl:error
        'FNC
        "Error de Tipo: Cada literal SAT debe ser un entero"))
      ((= literal 0)
       (eopl:error
        'FNC
        "Literal SAT inválido: el índice 0 no existe"))
      ((> (if (< literal 0) (- literal) literal) num-vars)
       (eopl:error
        'FNC
        "Literal SAT fuera de rango: ~s para n = ~s"
        literal
        num-vars))
      (else literal))))

;; Una cláusula debe contener al menos un literal válido.
(define validate-sat-clause
  (lambda (clause num-vars)
    (if (null? clause)
        (eopl:error
         'FNC
         "Cláusula SAT inválida: debe contener al menos un literal")
        (let loop ((remaining clause))
          (if (null? remaining)
              clause
              (begin
                (validate-sat-literal (car remaining) num-vars)
                (loop (cdr remaining))))))))

;; Recorre y valida todas las cláusulas de la instancia.
(define validate-sat-clauses
  (lambda (clauses num-vars)
    (if (null? clauses)
        (eopl:error
         'FNC
         "La instancia SAT debe contener al menos una cláusula")
        (let loop ((remaining clauses))
          (if (null? remaining)
              clauses
              (begin
                (validate-sat-clause (car remaining) num-vars)
                (loop (cdr remaining))))))))

;; Construye la estructura interna sat-instance a partir de las cláusulas FNC[cite: 5, 6]
(define parse-fnc-to-sat
  (lambda (num-vars first-clause rest-clauses)
    (if (not (and (integer? num-vars)
                  (exact? num-vars)
                  (> num-vars 0)))
        (eopl:error
         'FNC
         "Número de variables inválido: n debe ser un entero mayor que cero")
        (let ((clauses
               (map extract-clause
                    (cons first-clause rest-clauses))))
          (validate-sat-clauses clauses num-vars)
          (sat-instance num-vars clauses)))))

;; Convierte el nodo AST de un tipo a su descriptor interno.
(define type-spec->symbol
  (lambda (t-spec)
    (cases type-spec t-spec
      (int-type () 'int)
      (float-type () 'float)
      (string-type () 'string)
      (bool-type () 'bool)
      (void-type () 'void)
      (sat-type () 'sat)
      (list-type (element-type)
        (list 'list (type-spec->symbol element-type)))
      (vector-type (element-type)
        (list 'vector (type-spec->symbol element-type))))))

;; Procedimientos: representación de valores proc
(define-datatype proc-val proc-val?
  (procedure (ids (list-of symbol?))
             (body expression?)
             (saved-env environment?)))

;; =============================================================================
;; 5. EVALUADOR PRINCIPAL (GLOBALS + PROGRAM)[cite: 1, 2, 265]
;; =============================================================================

;; Auxiliar para evaluar condiciones en estructuras de control
(define true-value?
  (lambda (val)
    (cond
      ((boolean? val) val)
      ((number? val) (not (zero? val)))
      (else (eopl:error 'true-value? "Condición no válida: ~s" val)))))


;; Evalúa un programa completo: procesa GLOBALS y luego la función main[cite: 1, 2, 265]
(define eval-program
  (lambda (pgm)
    (cases program pgm
      (a-program (g-decls main-exp)
        (let ((global-env (eval-global-decls g-decls (empty-env))))
          (eval-expression main-exp global-env))))))

;; Recorre recursivamente las declaraciones de GLOBALS y extiende el ambiente global[cite: 1, 2]
(define eval-global-decls
  (lambda (decls env)
    (if (null? decls)
        env
        (let ((first-decl (car decls))
              (rest-decls (cdr decls)))
          (cases global-decl first-decl
            ;; Declaración de Variable Mutable (is-const? = #f)[cite: 2]
                        (var-decl (t-spec id exp)
              (let* ((type-sym (type-spec->symbol t-spec))
                     (raw-val
                      (eval-expression/expected exp env type-sym)))
                (let ((val (check-and-coerce-type type-sym raw-val)))
                  (let ((ref (a-ref #f type-sym (vector val))))
                    (eval-global-decls rest-decls 
                                       (extend-env (list id) (list ref) env))))))
            
            ;; Declaración de Constante Inmutable (is-const? = #t)[cite: 2]
                        (const-decl (t-spec id exp)
              (let* ((type-sym (type-spec->symbol t-spec))
                     (raw-val
                      (eval-expression/expected exp env type-sym)))
                (let ((val (check-and-coerce-type type-sym raw-val)))
                  (let ((ref (a-ref #t type-sym (vector val))))
                    (eval-global-decls rest-decls 
                                       (extend-env (list id) (list ref) env)))))))))))

;; =============================================================================
;; 6. EVALUADOR DE EXPRESIONES (eval-expression)[cite: 267]
;; =============================================================================

;; Entrada normal del evaluador, sin un tipo declarado conocido.
(define eval-expression
  (lambda (exp env)
    (eval-expression/expected exp env #f)))

;; Evaluador que también puede recibir el tipo esperado del resultado.
(define eval-expression/expected
  (lambda (exp env expected-type)
    (cases expression exp
      
      ;; Literales Primitivos
      (lit-exp (datum) datum)
      (float-exp (datum) datum)
      (string-exp (datum)
        (normalize-string-literal datum))
      (bool-exp (b-val)
        (cases bool-val b-val
          (true-bool () #t)
          (false-bool () #f)))

      ;; Retorna la cantidad de caracteres de una cadena.
      (string-length-exp (arg-exp)
        (string-length
         (require-string
          'longitud
          (eval-expression arg-exp env))))

      ;; Une dos cadenas y retorna una cadena nueva.
      (string-concat-exp (left-exp right-exp)
        (string-append
         (require-string
          'concatenar
          (eval-expression left-exp env))
         (require-string
          'concatenar
          (eval-expression right-exp env))))

      ;; Búsqueda de variables en el ambiente[cite: 198]
      (var-exp (id)
        (apply-env env id))

      ;; Asignación (operador set id -> expression)[cite: 3, 199]
      (assign-exp (id rhs-exp)
        (let ((ref (apply-env-ref env id)))
          (cases reference ref
            (a-ref (is-const? type-sym val-cell)
              (let ((rhs-val
                     (eval-expression/expected rhs-exp env type-sym)))
                (setref! ref rhs-val)
                (deref ref))))))

      ;; Distingue operaciones binarias y literales de lista.
      (paren-exp (first-exp tail)
        (cases paren-tail tail
          ;; Caso: (exp1 operador exp2)
          (binop-tail (op second-exp)
            (let ((val1 (eval-expression first-exp env))
                  (val2 (eval-expression second-exp env)))
              (apply-primitive-op op val1 val2)))

          ;; Caso: (exp1, exp2, ...)
          (list-tail (second-exp other-exps)
            (let ((values
                   (map
                    (lambda (item)
                      (eval-expression/expected
                       item
                       env
                       (list-element-type expected-type)))
                    (cons first-exp
                          (cons second-exp other-exps)))))
              (make-list-value values expected-type)))

          ;; Caso: (exp)
          (singleton-tail ()
            (make-list-value
             (list
              (eval-expression/expected
               first-exp
               env
               (list-element-type expected-type)))
             expected-type))))

      ;; La lista vacía comienza sin un tipo de elemento conocido.
      (empty-list-exp ()
        (a-list 'unknown '()))

      ;; Retorna #t solamente si el valor es una lista vacía.
      (empty-list-test-exp (arg-exp)
        (let ((value (eval-expression arg-exp env)))
          (if (list-value? value)
              (cases list-value value
                (a-list (element-type elements)
                  (null? elements)))
              #f)))

      ;; Indica si el valor pertenece al tipo list-value.
      (list-test-exp (arg-exp)
        (list-value? (eval-expression arg-exp env)))

      ;; Agrega un elemento al inicio y retorna una lista nueva.
      (make-list-exp (element-exp list-exp)
        (prepend-list-value
         (eval-expression/expected
          element-exp env (list-element-type expected-type))
         (eval-expression/expected list-exp env expected-type)
         expected-type))

      ;; Retorna el primer elemento de una lista no vacía.
      (list-head-exp (arg-exp)
        (car (require-nonempty-elements
              'head
              (eval-expression arg-exp env))))

      ;; Retorna una lista nueva sin el primer elemento.
      (list-tail-exp (arg-exp)
        (let ((value (eval-expression arg-exp env)))
          (cases list-value (require-list 'tail value)
            (a-list (element-type elements)
              (if (null? elements)
                  (eopl:error 'tail "La lista está vacía")
                  (a-list element-type (cdr elements)))))))

      ;; Une dos listas y retorna una lista nueva.
      (list-append-exp (left-exp right-exp)
        (append-list-values
         (eval-expression/expected left-exp env expected-type)
         (eval-expression/expected right-exp env expected-type)
         expected-type))

      ;; Consulta una posición usando índices desde cero.
      (list-ref-exp (list-exp position-exp)
        (let ((value (eval-expression list-exp env))
              (position (eval-expression position-exp env)))
          (cases list-value (require-list 'ref-list value)
            (a-list (element-type elements)
              (cond
                ((not (and (integer? position) (exact? position)))
                 (eopl:error
                  'ref-list
                  "Error de Tipo: El índice debe ser un entero"))
                ((or (< position 0)
                     (>= position (length elements)))
                 (eopl:error
                  'ref-list
                  "Índice fuera de rango: ~s"
                  position))
                (else
                 (list-ref elements position)))))))

      ;; Retorna la cantidad de elementos de una lista.
      (list-length-exp (arg-exp)
        (cases list-value
          (require-list 'length (eval-expression arg-exp env))
          (a-list (element-type elements)
            (length elements))))

      ;; Construye un vector literal mutable [e1, e2, ...].
      (vector-literal-exp (first-exp other-exps)
        (let ((values
               (map
                (lambda (item)
                  (eval-expression/expected
                   item env (vector-element-type expected-type)))
                (cons first-exp other-exps))))
          (make-vector-literal-value values expected-type)))

      ;; Indica si el valor es un vector de LogicFusion.
      (vector-test-exp (arg-exp)
        (vector-value? (eval-expression arg-exp env)))

      ;; Crea un vector inicializado según su tipo declarado.
      (make-vector-exp (size-exp)
        (make-sized-vector-value
         (eval-expression size-exp env)
         expected-type))

      ;; Consulta una posición del vector.
      (vector-ref-exp (vector-exp position-exp)
        (let ((val (eval-expression vector-exp env))
              (position (eval-expression position-exp env)))
          (cases vector-value (require-vector 'ref-vector val)
            (a-vector (element-type cell)
              (let* ((storage (vector-ref cell 0))
                     (valid-position
                      (validate-vector-index
                       'ref-vector
                       position
                       (vector-length storage)
                       #f)))
                (vector-ref storage valid-position))))))

      ;; Modifica una posición existente del vector.
      (vector-set-exp (vector-exp position-exp value-exp)
        (let ((val (eval-expression vector-exp env))
              (position (eval-expression position-exp env))
              (new-value (eval-expression value-exp env)))
          (cases vector-value (require-vector 'set-vector val)
            (a-vector (element-type cell)
              (let* ((storage (vector-ref cell 0))
                     (valid-position
                      (validate-vector-index
                       'set-vector
                       position
                       (vector-length storage)
                       #f))
                     (checked
                      (check-vector-element
                       'set-vector element-type new-value)))
                (vector-set! storage valid-position checked)
                checked)))))

      ;; Agrega un elemento al final del mismo vector.
      (vector-append-exp (vector-exp value-exp)
        (append-vector-value!
         (eval-expression vector-exp env)
         (eval-expression value-exp env)))

      ;; Elimina una posición del mismo vector.
      (vector-delete-exp (vector-exp position-exp)
        (delete-vector-value!
         (eval-expression vector-exp env)
         (eval-expression position-exp env)))

      ;; Inserta un valor en la posición indicada del mismo vector.
      (vector-insert-exp (vector-exp position-exp value-exp)
        (insert-vector-value!
         (eval-expression vector-exp env)
         (eval-expression position-exp env)
         (eval-expression value-exp env)))

      ;; Construcción de la instancia interna SAT (FNC)[cite: 5, 6]
      (fnc-exp (num-vars first-clause rest-clauses)
        (parse-fnc-to-sat num-vars first-clause rest-clauses))

      ;; Estructuras de control y bloques secuenciales
      (while-exp (test-exp body-exp)
        (let loop ((last-val 0))
          (if (true-value? (eval-expression test-exp env))
              (loop (eval-expression/expected body-exp env expected-type))
              last-val)))

      (begin-exp (exp exps)
        (let loop ((current exp) (rest exps))
          (if (null? rest)
              (eval-expression/expected current env expected-type)
              (begin
                (eval-expression current env)
                (loop (car rest) (cdr rest))))))

      (if-exp (test-exp true-exp false-exp)
        (if (true-value? (eval-expression test-exp env))
            (eval-expression/expected true-exp env expected-type)
            (eval-expression/expected false-exp env expected-type)))
      
      (for-exp (init-exp cond-exp step-exp body-exp)
        (begin
          (eval-expression init-exp env)
          (let loop ((last-val 0))
            (if (true-value? (eval-expression cond-exp env))
                (let ((res
                       (eval-expression/expected
                        body-exp env expected-type)))
                  (eval-expression step-exp env)
                  (loop res))
                last-val))))

      
      (switch-exp (target-exp case-vals case-exps default-exp)
        (let ((target (eval-expression target-exp env)))
          (let loop ((vals case-vals) (exps case-exps))
            (cond
              ((null? vals)
               (eval-expression/expected default-exp env expected-type))
              ((equal? target (eval-expression (car vals) env))
               (eval-expression/expected
                (car exps) env expected-type))
              (else (loop (cdr vals) (cdr exps)))))))

      (block-exp (ids exps body-exp)
        (let* ((vals (map (lambda (e) (eval-expression e env)) exps))
               (refs (map (lambda (v) (a-ref #f (get-value-type v) (vector v))) vals)))
          (eval-expression/expected
           body-exp (extend-env ids refs env) expected-type)))

      ;;Procedimientos
      (lambda-exp (ids body)
        (procedure ids body env))

      (call-exp (rator rands)
        (let ((f (eval-expression rator env))
              (args (map (lambda (e) (eval-expression e env)) rands)))
          (apply-procedure f args expected-type)))

      
      (letrec-exp (id rhs body)
        (let* ((cell (vector #f))
               (new-env (extend-env (list id) (list (a-ref #f 'proc cell)) env)))
          (vector-set! cell 0 (eval-expression rhs new-env))
          (eval-expression/expected body new-env expected-type)))

      (solve-exp (e)
        (let ((inst (eval-expression e env)))
          (if (not (sat-value? inst))
              (eopl:error
               'solve
               "Error de Tipo: solve esperaba una instancia SAT")
              (cases sat-value inst
                (sat-instance (n clauses)
                  (if (sat-solvable? n clauses) 1 0))))))
      
      )))


;; Aplicación de procedimientos
(define apply-procedure
  (lambda (f args expected-type)
    (cases proc-val f
      (procedure (ids body saved-env)
        (eval-expression/expected body
          (extend-env ids
                      (map (lambda (v) (a-ref #f (get-value-type v) (vector v))) args)
                      saved-env)
          expected-type)))))

;; Búsqueda exhaustiva sobre todas las asignaciones
(define sat-abs (lambda (x) (if (< x 0) (- x) x)))
(define sat-append
  (lambda (l1 l2)
    (if (null? l1) l2 (cons (car l1) (sat-append (cdr l1) l2)))))
(define sat-all-assignments
  (lambda (n)
    (if (= n 0)
        (list '())
        (let ((rest (sat-all-assignments (- n 1))))
          (sat-append (map (lambda (a) (cons #t a)) rest)
                      (map (lambda (a) (cons #f a)) rest))))))
(define sat-lit-true?
  (lambda (lit assign)
    (let ((v (list-ref assign (- (sat-abs lit) 1))))
      (if (> lit 0) v (not v)))))
(define sat-clause-true?
  (lambda (clause assign)
    (cond ((null? clause) #f)
          ((sat-lit-true? (car clause) assign) #t)
          (else (sat-clause-true? (cdr clause) assign)))))
(define sat-formula-true?
  (lambda (clauses assign)
    (cond ((null? clauses) #t)
          ((sat-clause-true? (car clauses) assign)
           (sat-formula-true? (cdr clauses) assign))
          (else #f))))
(define sat-solvable?
  (lambda (n clauses)
    (let loop ((assigns (sat-all-assignments n)))
      (cond ((null? assigns) #f)
            ((sat-formula-true? clauses (car assigns)) #t)
            (else (loop (cdr assigns)))))))



;; Evaluación de operadores aritméticos y relacionales binarios[cite: 3]
(define apply-primitive-op
  (lambda (op val1 val2)
    (cases primitive-op op
      (add-op () (+ val1 val2))
      (sub-op () (- val1 val2))
      (mul-op () (* val1 val2))
      (div-op () (/ val1 val2))
      (eq-op () (equal? val1 val2))
      (neq-op () (not (equal? val1 val2)))
      (gt-op () (> val1 val2))
      (lt-op () (< val1 val2))
      (gte-op () (>= val1 val2))
      (lte-op () (<= val1 val2)))))

;; Función ejecutora principal
(define run
  (lambda (code-string)
    (eval-program (scan&parse code-string))))

;; =============================================================================
;; 7. PRUEBAS DE EJECUCIÓN (REPL / REPOSITORIO)[cite: 1, 13]
;; =============================================================================

;; Pruebas de Scan & Parse
(scan&parse "GLOBALS { float pi = 3.1415; int a = 10; } PROGRAM { proc main() { return (a-1); } }")
(scan&parse "GLOBALS { int a = 10; } PROGRAM { proc main() { return a; } }")
(scan&parse "GLOBALS { float pi = 3.1415; } PROGRAM { proc main() { return pi; } }")
(scan&parse "GLOBALS { string nombre = \"Robinson\"; bool docente? = True; } PROGRAM { proc main() { return nombre; } }")
(scan&parse "GLOBALS { const int valor = 10; } PROGRAM { proc main() { return (valor + 1); } }")
(scan&parse "GLOBALS { sat x = FNC 2 ( (1 or 2) and (-1) and (-2) ); } PROGRAM { proc main() { return x; } }")

;; Prueba de Ejecución Evaluada con (run ...)
(run "
GLOBALS {
  int a = 10;
  const float pi = 3.1415;
  const float area = 20; % Coerción implícita de int (20) a float (20.0)[cite: 2]
  bool activo = True;
  void dinamica = 5;
  sat mi_formula = FNC 4 (
    (1 or -2 or 3) and
    (2)
  );
}
PROGRAM {
  proc main() {
    return (a + 5);
  }
}
")



;; Pruebas ciclo while (suma de 1 hasta 10 -> 55)
(scan&parse "GLOBALS { int i = 0; int sum = 0; } PROGRAM { proc main() { return while [(i < 10)] { begin set i -> (i + 1); set sum -> (sum + i) end }; } }")
(run "GLOBALS { int i = 0; int sum = 0; } PROGRAM { proc main() { return while [(i < 10)] { begin set i -> (i + 1); set sum -> (sum + i) end }; } }")


;; Pruebas condicional if-else (condición verdadera -> 100, condición falsa -> 200)
(scan&parse "GLOBALS { int x = 10; } PROGRAM { proc main() { return if [(x > 5)] { 100 } else { 200 }; } }")
(run "GLOBALS { int x = 10; } PROGRAM { proc main() { return if [(x > 5)] { 100 } else { 200 }; } }")

(scan&parse "GLOBALS { int x = 2; } PROGRAM { proc main() { return if [(x > 5)] { 100 } else { 200 }; } }")
(run "GLOBALS { int x = 2; } PROGRAM { proc main() { return if [(x > 5)] { 100 } else { 200 }; } }")

;; Prueba ciclo for (suma del 1 al 5 -> 15)
(scan&parse "GLOBALS { int i = 0; int sum = 0; } PROGRAM { proc main() { return for [ set i -> 1 ; (i < 6) ; set i -> (i + 1) ] { set sum -> (sum + i) }; } }")
(run "GLOBALS { int i = 0; int sum = 0; } PROGRAM { proc main() { return for [ set i -> 1 ; (i < 6) ; set i -> (i + 1) ] { set sum -> (sum + i) }; } }")

;; Pruebas switch: coincide en caso 2 -> 200; cae en default -> 999
(scan&parse "GLOBALS { int op = 2; } PROGRAM { proc main() { return switch [op] { case 1: 100; case 2: 200; default: 999 }; } }")
(run "GLOBALS { int op = 2; } PROGRAM { proc main() { return switch [op] { case 1: 100; case 2: 200; default: 999 }; } }")

(scan&parse "GLOBALS { int op = 7; } PROGRAM { proc main() { return switch [op] { case 1: 100; case 2: 200; default: 999 }; } }")
(run "GLOBALS { int op = 7; } PROGRAM { proc main() { return switch [op] { case 1: 100; case 2: 200; default: 999 }; } }")


;; Prueba BLOCK con LOCALS: usa variable local x = 50 dentro del bloque -> devuelve 55
(scan&parse "GLOBALS { int x = 10; } PROGRAM { proc main() { return BLOCK LOCALS { x = 50; } { (x + 5) }; } }")
(run "GLOBALS { int x = 10; } PROGRAM { proc main() { return BLOCK LOCALS { x = 50; } { (x + 5) }; } }")

;; Prueba BLOCK con dos variables locales: a = 2, b = 3 -> devuelve 6
(scan&parse "GLOBALS { int x = 10; } PROGRAM { proc main() { return BLOCK LOCALS { a = 2; b = 3; } { (a * b) }; } }")
(run "GLOBALS { int x = 10; } PROGRAM { proc main() { return BLOCK LOCALS { a = 2; b = 3; } { (a * b) }; } }")


;; Prueba PROC: lambda con un parámetro, llamada con 5 -> devuelve 6
(scan&parse "GLOBALS { int x = 1; } PROGRAM { proc main() { return BLOCK LOCALS { f = lambda (y) (y + 1); } { call f (5) }; } }")
(run "GLOBALS { int x = 1; } PROGRAM { proc main() { return BLOCK LOCALS { f = lambda (y) (y + 1); } { call f (5) }; } }")

;; Prueba PROC: lambda con dos parámetros, llamada con 3 y 4 -> devuelve 12
(scan&parse "GLOBALS { int x = 1; } PROGRAM { proc main() { return BLOCK LOCALS { f = lambda (a b) (a * b); } { call f (3 4) }; } }")
(run "GLOBALS { int x = 1; } PROGRAM { proc main() { return BLOCK LOCALS { f = lambda (a b) (a * b); } { call f (3 4) }; } }")

;; Prueba PROC: factorial recursivo con letrec, factorial de 5 -> devuelve 120
(scan&parse "GLOBALS { int x = 1; } PROGRAM { proc main() { return letrec fact = lambda (n) if [(n < 1)] { 1 } else { (n * call fact ((n - 1))) } in call fact (5); } }")
(run "GLOBALS { int x = 1; } PROGRAM { proc main() { return letrec fact = lambda (n) if [(n < 1)] { 1 } else { (n * call fact ((n - 1))) } in call fact (5); } }")

;; Prueba PROC: factorial recursivo con letrec, factorial de 3 -> devuelve 6
(scan&parse "GLOBALS { int x = 1; } PROGRAM { proc main() { return letrec fact = lambda (n) if [(n < 1)] { 1 } else { (n * call fact ((n - 1))) } in call fact (3); } }")
(run "GLOBALS { int x = 1; } PROGRAM { proc main() { return letrec fact = lambda (n) if [(n < 1)] { 1 } else { (n * call fact ((n - 1))) } in call fact (3); } }")


;; Prueba SAT: instancia satisfactible (x2 = verdadero) -> devuelve 1
(scan&parse "GLOBALS { int x = 1; } PROGRAM { proc main() { return solve(FNC 2 ( (1 or 2) and (-1 or 2) )); } }")
(run "GLOBALS { int x = 1; } PROGRAM { proc main() { return solve(FNC 2 ( (1 or 2) and (-1 or 2) )); } }")

;; Prueba SAT: instancia insatisfactible (x1 y -x1 a la vez) -> devuelve 0
(scan&parse "GLOBALS { int x = 1; } PROGRAM { proc main() { return solve(FNC 2 ( (1 or 2) and (-1 or 2) )); } }")
(run "GLOBALS { int x = 1; } PROGRAM { proc main() { return solve(FNC 1 ( (1) and (-1) )); } }")


;; =============================================================================
;; PRUEBAS DE ANDRÉS: LISTAS INMUTABLES (ADENDO 5)
;; =============================================================================

;; Literales, empty, empty? y list?
(scan&parse "GLOBALS { list<int> xs = (1, 2, 3); } PROGRAM { proc main() { return length(xs); } }")
(run "GLOBALS { list<int> xs = (1, 2, 3); } PROGRAM { proc main() { return length(xs); } }") ; 3
(run "GLOBALS { list<int> xs = empty; } PROGRAM { proc main() { return empty?(xs); } }") ; #t
(run "GLOBALS { int x = 42; } PROGRAM { proc main() { return list?(x); } }") ; #f

;; make-list, head y tail generan resultados nuevos
(run "GLOBALS { list<int> xs = make-list(1, empty); } PROGRAM { proc main() { return head(xs); } }") ; 1
(run "GLOBALS { list<int> xs = (1, 2, 3); } PROGRAM { proc main() { return head(tail(xs)); } }") ; 2

;; append, ref-list y length
(run "GLOBALS { list<int> a = (1, 2); list<int> b = (3, 4); } PROGRAM { proc main() { return ref-list(append(a, b), 3); } }") ; 4
(run "GLOBALS { list<string> xs = (\"a\", \"b\"); } PROGRAM { proc main() { return length(xs); } }") ; 2

;; list<void> permite elementos heterogéneos
(run "GLOBALS { list<void> xs = (1, True, \"texto\"); } PROGRAM { proc main() { return ref-list(xs, 1); } }") ; #t

;; Inmutabilidad: tail produce otra lista y original conserva su primer elemento
(run "GLOBALS { list<int> xs = (10, 20); const list<int> original = xs; } PROGRAM { proc main() { return begin set xs -> tail(xs); head(original) end; } }") ; 10

;; Casos de error para ejecutar individualmente durante la revisión en DrRacket:
;; (run "GLOBALS { list<int> xs = (1, True); } PROGRAM { proc main() { return xs; } }")
;; Error de tipo por elementos heterogéneos.
;;
;; (run "GLOBALS { list<int> xs = empty; } PROGRAM { proc main() { return head(xs); } }")
;; Error por consultar head de una lista vacía.
;;
;; (run "GLOBALS { list<int> xs = empty; } PROGRAM { proc main() { return tail(xs); } }")
;; Error por consultar tail de una lista vacía.
;;
;; (run "GLOBALS { list<int> xs = (1, 2); } PROGRAM { proc main() { return ref-list(xs, 2); } }")
;; Error por índice fuera de rango.
;;
;; (run "GLOBALS { list<int> xs = (1); } PROGRAM { proc main() { return ref-list(xs, 0.5); } }")
;; Error porque el índice no es un entero.
;;
;; (run "GLOBALS { list<int> xs = (1); list<bool> ys = (True); } PROGRAM { proc main() { return append(xs, ys); } }")
;; Error por concatenar listas de tipos incompatibles.


;; =============================================================================
;; PRUEBAS DE ANDRÉS: VECTORES MUTABLES (ADENDO 7)
;; =============================================================================

;; Literal, vector? y acceso desde índice cero
(scan&parse "GLOBALS { vector<int> v = [10, 20, 30]; } PROGRAM { proc main() { return ref-vector(v, 1); } }")
(run "GLOBALS { vector<int> v = [10, 20, 30]; } PROGRAM { proc main() { return ref-vector(v, 1); } }") ; 20
(run "GLOBALS { vector<int> v = [1]; } PROGRAM { proc main() { return vector?(v); } }") ; #t
(run "GLOBALS { int x = 1; } PROGRAM { proc main() { return vector?(x); } }") ; #f

;; make-vector usa el valor inicial correspondiente al tipo declarado
(run "GLOBALS { vector<int> v = make-vector(3); } PROGRAM { proc main() { return ref-vector(v, 2); } }") ; 0
(run "GLOBALS { vector<bool> v = make-vector(2); } PROGRAM { proc main() { return ref-vector(v, 0); } }") ; #f

;; set-vector modifica una posición del vector original
(run "GLOBALS { vector<int> v = [10, 20, 30]; } PROGRAM { proc main() { return begin set-vector(v, 1, 50); ref-vector(v, 1) end; } }") ; 50

;; append-vector cambia el tamaño del mismo vector
(run "GLOBALS { vector<int> v = [10, 20]; } PROGRAM { proc main() { return begin append-vector(v, 30); ref-vector(v, 2) end; } }") ; 30

;; delete-val-vector elimina y desplaza a la izquierda
(run "GLOBALS { vector<int> v = [10, 20, 30]; } PROGRAM { proc main() { return begin delete-val-vector(v, 1); ref-vector(v, 1) end; } }") ; 30

;; insert-val-vector inserta y desplaza a la derecha
(run "GLOBALS { vector<int> v = [10, 20, 30]; } PROGRAM { proc main() { return begin insert-val-vector(v, 1, 15); ref-vector(v, 2) end; } }") ; 20

;; Mutabilidad real: dos variables observan los cambios del mismo vector
(run "GLOBALS { vector<int> v = [1, 2]; void alias = v; } PROGRAM { proc main() { return begin append-vector(v, 3); ref-vector(alias, 2) end; } }") ; 3

;; vector<void> permite elementos heterogéneos
(run "GLOBALS { vector<void> v = [1, True, \"texto\"]; } PROGRAM { proc main() { return begin append-vector(v, 4.5); ref-vector(v, 3) end; } }") ; 4.5

;; Casos de error para ejecutar individualmente durante la revisión en DrRacket:
;; (run "GLOBALS { vector<int> v = [1, True]; } PROGRAM { proc main() { return v; } }")
;; Error por elementos heterogéneos.
;;
;; (run "GLOBALS { vector<int> v = [1, 2]; } PROGRAM { proc main() { return ref-vector(v, 2); } }")
;; Error por índice fuera de rango.
;;
;; (run "GLOBALS { vector<int> v = [1]; } PROGRAM { proc main() { return set-vector(v, 0, True); } }")
;; Error por valor incompatible con vector<int>.
;;
;; (run "GLOBALS { vector<int> v = make-vector(2.5); } PROGRAM { proc main() { return v; } }")
;; Error porque el tamaño debe ser un entero.
;;
;; (run "GLOBALS { vector<int> v = [1]; } PROGRAM { proc main() { return delete-val-vector(v, (0 - 1)); } }")
;; Error por índice negativo.
;;
;; (run "GLOBALS { vector<int> v = [1]; } PROGRAM { proc main() { return insert-val-vector(v, 2, 9); } }")
;; Error porque la posición de inserción supera el tamaño.
;;
;; (run "GLOBALS { vector<int> original = [1]; vector<void> alias = original; } PROGRAM { proc main() { return set-vector(alias, 0, \"texto\"); } }")
;; Error: el alias conserva el tipo real int del vector compartido.


;; =============================================================================
;; PRUEBAS DE ANDRÉS: PRIMITIVAS DE CADENAS
;; =============================================================================

;; longitud cuenta caracteres y no incluye las comillas del literal
(scan&parse "GLOBALS { string texto = \"LogicFusion\"; } PROGRAM { proc main() { return longitud(texto); } }")
(run "GLOBALS { string texto = \"LogicFusion\"; } PROGRAM { proc main() { return longitud(texto); } }") ; 11
(run "GLOBALS { string texto = \"\"; } PROGRAM { proc main() { return longitud(texto); } }") ; 0

;; concatenar funciona con literales, variables y resultados anidados
(run "GLOBALS { string a = \"Logic\"; string b = \"Fusion\"; } PROGRAM { proc main() { return concatenar(a, b); } }") ; "LogicFusion"
(run "GLOBALS { string a = \"A\"; } PROGRAM { proc main() { return concatenar(concatenar(a, \"B\"), \"C\"); } }") ; "ABC"

;; Las cadenas originales permanecen sin cambios
(run "GLOBALS { string a = \"Hola\"; string b = concatenar(a, \" mundo\"); } PROGRAM { proc main() { return a; } }") ; "Hola"

;; Casos de error para ejecutar individualmente durante la revisión en DrRacket:
;; (run "GLOBALS { int x = 10; } PROGRAM { proc main() { return longitud(x); } }")
;; Error de tipo porque longitud requiere una cadena.
;;
;; (run "GLOBALS { string x = \"a\"; } PROGRAM { proc main() { return concatenar(x, 10); } }")
;; Error de tipo porque ambos argumentos de concatenar deben ser cadenas.


;; =============================================================================
;; PRUEBAS DE ANDRÉS: VALIDACIONES SAT Y SOLVE
;; =============================================================================

;; Instancia válida satisfactible
(scan&parse "GLOBALS { sat f = FNC 3 ((1 or -2) and (2 or 3)); } PROGRAM { proc main() { return solve(f); } }")
(run "GLOBALS { sat f = FNC 3 ((1 or -2) and (2 or 3)); } PROGRAM { proc main() { return solve(f); } }") ; 1

;; Instancia válida insatisfactible
(run "GLOBALS { sat f = FNC 1 ((1) and (-1)); } PROGRAM { proc main() { return solve(f); } }") ; 0

;; Literales en los límites positivo y negativo permitidos
(run "GLOBALS { sat f = FNC 3 ((3) and (-3 or 1)); } PROGRAM { proc main() { return solve(f); } }") ; 1

;; Casos de error para ejecutar individualmente durante la revisión en DrRacket:
;; (run "GLOBALS { sat f = FNC 0 ((1)); } PROGRAM { proc main() { return f; } }")
;; Error porque n debe ser mayor que cero.
;;
;; (run "GLOBALS { sat f = FNC 2 ((3)); } PROGRAM { proc main() { return f; } }")
;; Error porque el literal positivo supera n.
;;
;; (run "GLOBALS { sat f = FNC 2 ((-3)); } PROGRAM { proc main() { return f; } }")
;; Error porque el literal negativo supera -n.
;;
;; (run "GLOBALS { sat f = FNC 2 ((0)); } PROGRAM { proc main() { return f; } }")
;; Error porque el índice cero no representa una variable SAT.
;;
;; (run "GLOBALS { sat f = FNC 2 (() and (1)); } PROGRAM { proc main() { return f; } }")
;; Error porque una cláusula no puede estar vacía.
;;
;; (run "GLOBALS { int x = 10; } PROGRAM { proc main() { return solve(x); } }")
;; Error de tipo porque solve requiere una instancia SAT.
;;
;; (run "GLOBALS { list<int> xs = (1, 2); } PROGRAM { proc main() { return solve(xs); } }")
;; Error de tipo porque una lista tampoco es una instancia SAT.
;;
;; (scan&parse "GLOBALS { sat f = FNC 2.5 ((1)); } PROGRAM { proc main() { return f; } }")
;; Error sintáctico porque la gramática de FNC solo admite un entero para n.
