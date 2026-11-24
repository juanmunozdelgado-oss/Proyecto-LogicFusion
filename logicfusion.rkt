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
    (number ((arbno digit)) number)
    (float-number ((arbno digit) "." (arbno digit)) float)
    (string-lit ("\"" (arbno (not #\")) "\"") string)
   ))