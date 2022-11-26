#lang forge/core

; This example requires Racket 8.6 or later. If you need to upgrade your Racket version,
; remember to reinstall the forge package afterward. 

(require 
  json 
  (only-in racket hash-map/copy))

; Suppress output on stats, etc. (the default is 1)
(set-option! 'verbose 0)

; Require the Forge model you want to generate output from.
; This will put the model's predicates, etc. in scope. Here, I'm importing
; the tic-tac-toe model from the same directory. 
(require "ttt.frg")

; Run the predicate of interest to get a Run object. A Run object
; represents the context of the run, handles to solver, etc. This 
; will *not* open the visualizer. You can use whatever name you want
; for the run (I chose the very creative "my-run".)
(run my-run
    #:preds [trace]
    #:scope ([Board 9] 
             [Index 3]
             [Player 2]))

; Now the identifier "my-run" can be used to generate results. These
; are embodied by a lazily-expanded tree where nodes are either instances
; (if instances remain) or unsatisfiability (if no instances remain).
; 
; Why a *tree* rather than a *stream*? Because in temporal mode, Forge
; supports multiple kinds of "next". But this example isn't temporal.

(define results (forge:get-result my-run))
(define first-instance (tree:get-value results))
(printf "first instance: ~a~n" first-instance)

; Beware: there's always a _single_ current instance for purposes
; of running the evaluator, etc. So this line gets the second instance,
; but also advances the solver. Attempting to afterward use the evaluator 
; on the first instance will produce undefined behavior.
(define second-instance (tree:get-value (tree:get-child results 'next)))
(printf "second instance: ~a~n" second-instance)

; Instances are just wrapped Racket dictionaries, so we can convert them 
; to JSON or XML via Racket's libraries, and write using a file port.

; https://docs.racket-lang.org/json/index.html
; https://docs.racket-lang.org/reference/file-ports.html

(define (write-instance path inst)
  (cond 
    [(forge:Sat? inst) (write-sat path inst)]
    [(forge:Unsat? inst) (write-unsat path inst)]
    [else (printf "Error, value passed was not a sat/unsat Forge instance: ~a~n" inst)]))

; Unsatisfiable case
; For now, just write a string; if you want statistics, that's another field of 
; the Unsat struct: Unsat-stats. If you want a core, use Unsat-core.
(define (write-unsat path inst)
  (call-with-output-file path
    (lambda (out)
      (write "unsat" out))))

; Satisfiable case
; There is one snag: the values in the dictionaries are symbols, not strings.
; So, if we were to call jsexpr->string directly, we'd get an error at the base
; case. We can fix that by just converting the dictionary to use strings instead.

; process individual tuple (list)
(define (jsonify-tuple tup)
  (map (lambda (atom) 
         (cond [(symbol? atom) (symbol->string atom)]
               [else atom]))
       tup))
; process individual tuple set (list of lists)
(define (jsonify-tuples k v)
  (values k (map jsonify-tuple v)))
; process individual instance (possibly within a temporal trace)
(define (jsonify-dict dict)
  (hash-map/copy dict jsonify-tuples ))
; process entire struct
(define (write-sat path inst)
  (define possibly-temporal-trace (map jsonify-dict (forge:Sat-instances first-instance))) 
  (define json-string (jsexpr->string possibly-temporal-trace))
  (call-with-output-file path #:exists 'append
    (lambda (out)
      (writeln json-string out))))

(define output-path "./instances.json")
(when (file-exists? output-path)
  (delete-file output-path))
(write-instance output-path first-instance)
(write-instance output-path second-instance)





