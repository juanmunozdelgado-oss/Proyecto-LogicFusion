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



(define scanner-spec-logicfusion
  '(
    (white-sp (whitespace) skip)

    (comment ("%" (arbno (not #\newline))) skip)

    (identifier (letter (arbno (or letter digit "_" "?"))) symbol)

    (float-number (digit (arbno digit) "." digit (arbno digit)) number)

    (number (digit (arbno digit)) number)

    (string-lit ("\"" (arbno (not #\")) "\"") string)
   ))

(define grammar-spec-logicfusion
  '(
    (program ("GLOBALS" "{" (arbno global-decl) "}" 
              "PROGRAM" "{" "proc" "main" "(" ")" "{" "return" expression ";" "}" "}")
             a-program)

    (global-decl (type-spec identifier "=" expression ";") var-decl)
    (global-decl ("const" type-spec identifier "=" expression ";") const-decl)

    (type-spec ("int") int-type)
    (type-spec ("float") float-type)
    (type-spec ("string") string-type)
    (type-spec ("bool") bool-type)
    (type-spec ("void") void-type)
    (type-spec ("sat") sat-type)

    (expression (float-number) float-exp)
    (expression (number) lit-exp)
    (expression (string-lit) string-exp)
    (expression (bool-val) bool-exp)
    (expression (identifier) var-exp)
    
    (bool-val ("True") true-bool)
    (bool-val ("False") false-bool)

    (expression ("set" identifier "->" expression) assign-exp)

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

    (expression ("FNC" number "(" clausula-sat (arbno "and" clausula-sat) ")") fnc-exp)
    (clausula-sat ("(" literal-sat (arbno "or" literal-sat) ")") sat-clause)
    (literal-sat (number) pos-literal)
    (literal-sat ("-" number) neg-literal)
   ))

(sllgen:make-define-datatypes scanner-spec-logicfusion grammar-spec-logicfusion)

(define scan&parse
  (sllgen:make-string-parser scanner-spec-logicfusion grammar-spec-logicfusion))


;Pruebas scan&parse
(scan&parse "GLOBALS { float pi = 3.1415; int a = 10; } PROGRAM { proc main() { return (a-1); } }")
(scan&parse "GLOBALS { int a = 10; } PROGRAM { proc main() { return a; } }")
(scan&parse "GLOBALS { float pi = 3.1415; } PROGRAM { proc main() { return pi; } }")
(scan&parse "GLOBALS { string nombre = \"Robinson\"; bool docente? = True; } PROGRAM { proc main() { return nombre; } }")
(scan&parse "GLOBALS { const int valor = 10; } PROGRAM { proc main() { return (valor + 1); } }")
(scan&parse "GLOBALS { sat x = FNC 2 ( (1 or 2) and (-1) and (-2) ); } PROGRAM { proc main() { return x; } }")


(define-datatype reference reference?
  (a-ref (is-const? boolean?)
         (type-sym symbol?)
         (val-cell vector?)))

(define deref
  (lambda (ref)
    (cases reference ref
      (a-ref (is-const? type-sym val-cell)
        (vector-ref val-cell 0)))))

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

(define apply-env
  (lambda (env search-sym)
    (deref (apply-env-ref env search-sym))))

(define list-index
  (lambda (sym lst)
    (cond
      ((null? lst) #f)
      ((eqv? sym (car lst)) 0)
      (else (let ((arg (list-index sym (cdr lst))))
              (if arg (+ arg 1) #f))))))

