#lang racket
(require parser-tools/lex
         parser-tools/yacc)
(require "declarations.rkt")
(require "utilities.rkt")


(define (attachr l1 l2)
  (map (lambda (x) (cons x l2)) l1))

(define (union l1 l2)
  (cond [(null? l2) l1 ]
        [(member (car l2) l1) (union l1 (cdr l2))]
        [else (union (append l1 (list (car l2))) (cdr l2))]))

(define (combineFollow l1 l2) 
  (cond [(null? l2) l1]
        [else (combineFollow (if (ormap (lambda (y) (= (car y) (caar l2))) l1)
                                 (map (lambda (y) (cond [(= (car y) (caar l2)) (cons (caar l2) (sort (union (cdar l2) (cdr y)) <))]
                                                    [else y])) l1)
                                 (cons (car l2) l1))  (cdr l2))]))
  

(define (buildNullable t)
  (cond [(Epsilon? t) (list (cons (Epsilon-n t) #t))]
        [(Literal? t) (list (cons (Literal-n t) #f))]
        [(Star? t) (cons (cons (Star-n t) #t) (buildNullable (Star-t t)))]
        [(Or? t) (let* ([x (buildNullable (Or-t1 t))]
                        [y (buildNullable (Or-t2 t))])
                   (cons (cons (Or-n t) (or (cdar x) (cdar y))) (append x y)))]
        [(Then? t) (let* ([x (buildNullable (Then-t1 t))]
                        [y (buildNullable (Then-t2 t))])
                   (cons (cons (Then-n t) (and (cdar x) (cdar y))) (append x y)))]))

(define (buildFirst t)
  (cond [(Epsilon? t) (list (list (Epsilon-n t)))]
        [(Literal? t) (list (list (Literal-n t) (Literal-n t)))]
        [(Star? t) (let* ([x (buildFirst (Star-t t))])
                     (cons (cons (Star-n t) (cdar x)) x))]
        [(Or? t) (let* ([x (buildFirst (Or-t1 t))]
                        [y (buildFirst (Or-t2 t))])
                     (cons (cons (Or-n t) (append (cdar x) (cdar y))) (append x y)))]
        [(Then? t) (let* ([x (buildFirst (Then-t1 t))]
                          [y (buildFirst (Then-t2 t))])
                     (cons (cons (Then-n t) (append (cdar x) (if (cdar (buildNullable (Then-t1 t))) (cdar y) '())))
                           (append x y)))]))

(define (buildLast t)
  (cond [(Epsilon? t) (list (list (Epsilon-n t)))]
        [(Literal? t) (list (list (Literal-n t) (Literal-n t)))]
        [(Star? t) (let* ([x (buildLast (Star-t t))])
                     (cons (cons (Star-n t) (cdar x)) x))]
        [(Or? t) (let* ([x (buildLast (Or-t1 t))]
                        [y (buildLast (Or-t2 t))])
                     (cons (cons (Or-n t) (append (cdar x) (cdar y))) (append x y)))]
        [(Then? t) (let* ([x (buildLast (Then-t1 t))]
                          [y (buildLast (Then-t2 t))])
                     (cons (cons (Then-n t) (append (if (cdar (buildNullable (Then-t2 t))) (cdar x) '()) (cdar y)))
                           (append x y)))]))

(define (buildFollow t)
  (cond [(Then? t) (combineFollow (attachr (cdar (buildLast (Then-t1 t))) (cdar (buildFirst (Then-t2 t))))
                           (combineFollow (buildFollow (Then-t1 t)) (buildFollow (Then-t2 t))))]
        [(Star? t) (combineFollow (attachr (cdar (buildLast t)) (cdar (buildFirst t))) (buildFollow (Star-t t)))]
        [(Or? t) (combineFollow (buildFollow (Or-t1 t)) (buildFollow (Or-t2 t)))]
        [else '()]))

(define (buildGraph regexp)
  (define t1 (maketree regexp))
  (define firstNode (cdar (buildFirst t1)))
  (define follow1 (buildFollow t1))
  
  (define nodeedge1 (nodeedge follow1 firstNode (list firstNode) '() 0 t1))
  (define lastpos1 (lastpos t1))
  (Graph firstNode (car nodeedge1) (cdr nodeedge1) (containing lastpos1 (car nodeedge1)) (elements t1)))

(define (lastpos t) (Literal-n (Then-t2 t)))

(define (elements t)
  (cond [(Epsilon? t) '()]
        [(Literal? t) (list (Literal-c t))]
        [(Star? t) (elements (Star-t t))]
        [(Or? t) (union (elements (Or-t1 t)) (elements (Or-t2 t)))]
        [(Then? t) (union (elements (Then-t1 t)) (elements (Then-t2 t)))]))

  
(define (containing n l)
  (cond [(null? l) '()]
        [(member n (car l)) (cons (car l) (containing n (cdr l)))]
        [else (containing n (cdr l))]))

(define (charelem n t)
  (cond [(and (Literal? t) (= n (Literal-n t))) (Literal-c t)]
        [(Or? t) (let* ([z (charelem n (Or-t1 t))])
                  (cond [(equal? #f z) (charelem n (Or-t2 t))]
                        [else z]))]
        [(Then? t) (let* ([z (charelem n (Then-t1 t))])
                     (cond [(equal? #f z) (charelem n (Then-t2 t))]
                       [else z]))]
        [(Star? t) (charelem n (Star-t t))]
        [else #f]))

(define (followpos follow n)
  (cond [(null? follow) '()]
        [(= (caar follow) n) (cdar follow)]
        [else (followpos (cdr follow) n)]))
  
(define (makeedge onode node follow t edges)
  (cond [(null? node) edges]
        [(= (lastpos t) (car node)) (makeedge onode (cdr node) follow t edges)]
        [(member (charelem (car node) t) (map Trans-sym edges))
         (makeedge onode (cdr node) follow t (updateedge edges (Trans onode (charelem (car node) t) (followpos follow (car node)))))]
        [else (makeedge onode (cdr node) follow t (cons (Trans onode (charelem (car node) t) (followpos follow (car node))) edges))]))

(define (updateedge edges edge)
  (cond [(null? edges) '()]
        [(equal? (Trans-sym edge) (Trans-sym (car edges))) (cons (Trans (Trans-start edge) (Trans-sym edge) (sort (union (Trans-final edge) (Trans-final (car edges))) <))
                                                                 (updateedge (cdr edges) edge))]
        [else (cons (car edges) (updateedge (cdr edges) edge))]))

(define (nodeedge follow fnode totnodes totedges currpos t)
  (cond [(= currpos (length totnodes)) (cons totnodes totedges)]
        [else (let* ([currnode (list-ref totnodes currpos)]
                     [newedges (makeedge currnode currnode follow t '())]
                     [newnodes (map Trans-final newedges)])
              (nodeedge follow fnode (union totnodes newnodes) (union totedges newedges) (+ 1 currpos) t))]))






