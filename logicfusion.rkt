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
;; =============================================================================



#lang eopl
;; =============================================================================
;; PROYECTO FINAL: LOGICFUSION
;; Curso: Fundamentos de Lenguajes de Programación - Universidad del Valle
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

    ;; 6. Operaciones Aritméticas y Relacionales Binarias[cite: 3]
    (expression ("(" expression primitive-op expression ")") binop-exp)

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
    (clausula-sat ("(" literal-sat (arbno "or" literal-sat) ")") sat-clause)
    (literal-sat (number) pos-literal)
    (literal-sat ("-" number) neg-literal)
   ))

;; Generación automática de tipos de datos abstractos (Datatypes) e Interpretador SLLGEN[cite: 1, 22]
(sllgen:make-define-datatypes scanner-spec-logicfusion grammar-spec-logicfusion)

(define scan&parse
  (sllgen:make-string-parser scanner-spec-logicfusion grammar-spec-logicfusion))

;; =============================================================================
;; 3. GESTIÓN DE MEMORIA Y AMBIENTES (Clase 16 - #lang eopl)[cite: 171, 189, 193]
;; =============================================================================

;; Tipo de dato Referencia (Representa un L-valor en memoria con celda mutable en vector)[cite: 185, 189]
;;  - is-const?: Marca #t si es constante (inmutable) o #f si es variable[cite: 2]
;;  - type-sym: Símbolo del tipo de dato declarado ('int, 'float, etc.)[cite: 2]
;;  - val-cell: Vector de 1 posición para almacenamiento mutable del R-valor[cite: 185, 189]
(define-datatype reference reference?
  (a-ref (is-const? boolean?)
         (type-sym symbol?)
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

;; Infiere el tipo dinámico de un R-valor en tiempo de ejecución[cite: 2]
(define get-value-type
  (lambda (val)
    (cond
      ((and (integer? val) (exact? val)) 'int)
      ((real? val) 'float)
      ((string? val) 'string)
      ((boolean? val) 'bool)
      ((sat-value? val) 'sat)
      ;; NOTA PARA EL GRUPO: Aquí se agregarán los casos para 'list, 'vector, 'dict y 'proc
      (else 'unknown))))

;; Revisa coincidencia de tipos y realiza conversión implícita (coerción) de int a float[cite: 2]
(define check-and-coerce-type
  (lambda (expected-type val)
    (if (eqv? expected-type 'void)
        val  ;; Las variables void permiten cualquier tipo de dato dinámico[cite: 2]
        (let ((val-type (get-value-type val)))
          (cond
            ((eqv? expected-type val-type) val)
            ;; Coerción int -> float para admitir inicializaciones tipo float x = 20;[cite: 2]
            ((and (eqv? expected-type 'float) (eqv? val-type 'int))
             (exact->inexact val))
            (else
             (eopl:error 'check-and-coerce-type 
                         "Error de Tipo: Se esperaba ~s pero se obtuvo ~s" 
                         expected-type val-type)))))))

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
      (sat-clause (first-lit rest-lits)
        (map extract-literal-val (cons first-lit rest-lits))))))

;; Construye la estructura interna sat-instance a partir de las cláusulas FNC[cite: 5, 6]
(define parse-fnc-to-sat
  (lambda (num-vars first-clause rest-clauses)
    (sat-instance num-vars (map extract-clause (cons first-clause rest-clauses)))))

;; Convierte el nodo AST de especificación de tipo a su símbolo correspondiente[cite: 2]
(define type-spec->symbol
  (lambda (t-spec)
    (cases type-spec t-spec
      (int-type () 'int)
      (float-type () 'float)
      (string-type () 'string)
      (bool-type () 'bool)
      (void-type () 'void)
      (sat-type () 'sat))))

;; =============================================================================
;; 5. EVALUADOR PRINCIPAL (GLOBALS + PROGRAM)[cite: 1, 2, 265]
;; =============================================================================

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
              (let ((raw-val (eval-expression exp env))
                    (type-sym (type-spec->symbol t-spec)))
                (let ((val (check-and-coerce-type type-sym raw-val)))
                  (let ((ref (a-ref #f type-sym (vector val))))
                    (eval-global-decls rest-decls 
                                       (extend-env (list id) (list ref) env))))))
            
            ;; Declaración de Constante Inmutable (is-const? = #t)[cite: 2]
            (const-decl (t-spec id exp)
              (let ((raw-val (eval-expression exp env))
                    (type-sym (type-spec->symbol t-spec)))
                (let ((val (check-and-coerce-type type-sym raw-val)))
                  (let ((ref (a-ref #t type-sym (vector val))))
                    (eval-global-decls rest-decls 
                                       (extend-env (list id) (list ref) env)))))))))))

;; =============================================================================
;; 6. EVALUADOR DE EXPRESIONES (eval-expression)[cite: 267]
;; =============================================================================

(define eval-expression
  (lambda (exp env)
    (cases expression exp
      ;; Literales Primitivos
      (lit-exp (datum) datum)
      (float-exp (datum) datum)
      (string-exp (datum) datum)
      (bool-exp (b-val)
        (cases bool-val b-val
          (true-bool () #t)
          (false-bool () #f)))

      ;; Búsqueda de variables en el ambiente[cite: 198]
      (var-exp (id)
        (apply-env env id))

      ;; Asignación (operador set id -> expression)[cite: 3, 199]
      (assign-exp (id rhs-exp)
        (let ((rhs-val (eval-expression rhs-exp env))
              (ref (apply-env-ref env id)))
          (setref! ref rhs-val)
          rhs-val))

      ;; Evaluación de Operaciones Binarias Primarias[cite: 3]
      (binop-exp (exp1 op exp2)
        (let ((val1 (eval-expression exp1 env))
              (val2 (eval-expression exp2 env)))
          (apply-primitive-op op val1 val2)))

      ;; Construcción de la instancia interna SAT (FNC)[cite: 5, 6]
      (fnc-exp (num-vars first-clause rest-clauses)
        (parse-fnc-to-sat num-vars first-clause rest-clauses)))))

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