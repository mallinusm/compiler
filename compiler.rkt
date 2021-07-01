#lang racket

(require
 cpsc411/compiler-lib
 cpsc411/graph-lib
 cpsc411/2c-run-time)

(provide
  link-paren-x64
  interp-paren-x64
  interp-values-lang
  uniquify
  sequentialize-let
  canonicalize-bind
  select-instructions
  uncover-locals
  undead-analysis
  conflict-analysis
  assign-registers
  replace-locations
  assign-homes-opt
  ;optimize-predicates
  expose-basic-blocks
  resolve-predicates
  flatten-program
  patch-instructions
  implement-fvars
  generate-x64
)

(define (relop? op) (and (member op '(< <= = >= > !=)) #t))
(define (binop? op) (and (member op '(* +)) #t))
(define (addr? x)
  (match x
    [`(,reg - ,offset)
      #:when (and (frame-base-pointer-register? reg) (dispoffset? offset)) #t]
    [_ #f]))
(define (binop->proc op)
  (match op
    ['+ +] 
    ['* *] 
    [_ (error "invalid binop" op)]))
(define (relop->proc op)
  (match op
    ['< <]
    ['<= <=]
    ['= =]
    ['>= >=]
    ['> >]
    ['!= (compose not =)]
    [_ (error "unsupported relop operation" op)]))

(define (generate-x64 p)
  (define (loc? x) (or (register? x) (addr? x)))
  (define (opand? x) (or (int64? x) (register? x)))
  (define (trg? x) (or (register? x) (label? x)))
  (define (triv? x) (or (trg? x) (int64? x)))

  (define (binop->x64 op)
    (match op
      ['+ "add"]
      ['* "imul"]
      [_ (error "unsupported x64 binop instruction" op)]))

  (define (addr->offset addr)
    (match addr
      [`(,_ - ,offset) offset]
      [_ (error "invalid x64 addr instruction" addr)]))

  (define (addr->x64 addr)
    (let ((offset (addr->offset addr)))
      (format "QWORD [~a - ~a]" (current-frame-base-pointer-register) offset)))

  (define (loc->x64 loc)
    (cond 
      [(register? loc) loc]
      [(addr? loc) (addr->x64 loc)]
      [else (error "invalid loc format" loc)]))

  (define (relop->x64 op)
    (match op
      ['< "jl"]
      ['<= "jle"]
      ['= "je"]
      ['>= "jge"]
      ['> "jg"]
      ['!= "jne"]
      [_ (error "unsupported relop instruction" op)]))

  (define (generate-x64-s s)
    (match s
      [`(set! ,addr ,int32-value)
        #:when (and (addr? addr) (int32? int32-value))
        (format "mov ~a, ~a" (addr->x64 addr) int32-value)]
      [`(set! ,addr ,trg)
        #:when (and (addr? addr) (trg? trg))
        (format "mov ~a, ~a" (addr->x64 addr) trg)]
      [`(set! ,reg ,loc)
        #:when (and (register? reg) (loc? loc))
        (format "mov ~a, ~a" reg (loc->x64 loc))]
      [`(set! ,reg ,triv)
        #:when (and (register? reg) (triv? triv))
        (format "mov ~a, ~a" reg triv)]
      [`(set! ,reg (,op ,reg ,int32-value))
        #:when (and (register? reg) (binop? op) (int32? int32-value))
        (format "~a ~a, ~a" (binop->x64 op) reg int32-value)]
      [`(set! ,reg (,op ,reg ,loc))
        #:when (and (register? reg) (binop? op) (loc? loc))
        (format "~a ~a, ~a" (binop->x64 op) reg (loc->x64 loc))]
      [`(with-label ,label ,stmnt)
        #:when (label? label)
        (format "~a:\n~a" label (generate-x64-s stmnt))]
      [`(jump ,trg)
        #:when (trg? trg)
        (format "jmp ~a" trg)]
      [`(compare ,reg ,opand)
        #:when (and (register? reg) (opand? opand))
        (format "cmp ~a, ~a" reg opand)]
      [`(jump-if ,op ,label)
        #:when (and (relop? op) (label? label))
        (format "~a ~a" (relop->x64 op) label)]
      [_ (error "unable to generate x64" s)]))

  (define (generate-x64-ss ss)
    (foldl
      (lambda (s bytecode)
        (format "~a~a\n" bytecode (generate-x64-s s)))
      ""
      ss))

  (match p 
    [`(begin ,ss ...) (generate-x64-ss ss)]
    [_ (error "invalid Parent-x64 v4 program in generate-x64" p)]))

(define (link-paren-x64 p)
  (define (trg? x) (or (register? x) (label? x)))
  (define (loc? x) (or (register? x) (addr? x)))
  (define (triv? x) (or (trg? x) (int64? x)))
  (define (opand? x) (or (int64? x) (register? x)))

  (define label-map (make-hash))

  (define (link-paren-x64-populate-s s pc)
    (match s
      [`(set! ,addr ,int32-value)
        #:when (and (addr? addr) (int32? int32-value))
        pc] 
      [`(set! ,addr ,trg)
        #:when (and (addr? addr) (trg? trg))
        pc] 
      [`(set! ,reg ,loc)
        #:when (and (register? reg) (loc? loc))
        pc] 
      [`(set! ,reg ,triv)
        #:when (and (register? reg) (triv? triv))
        pc] 
      [`(set! ,reg (,op ,reg ,int32-value))
        #:when (and (register? reg) (binop? op) (int32? int32-value))
        pc] 
      [`(set! ,reg (,op ,reg ,loc))
        #:when (and (register? reg) (binop? op) (loc? loc))
        pc] 
      [`(with-label ,label ,stmnt)
        #:when (label? label)
        (begin
          (dict-set! label-map label pc)
          (link-paren-x64-populate-s stmnt (+ pc 1)))]
      [`(jump ,trg)
        #:when (trg? trg)
        pc]
      [`(compare ,reg ,opand)
        #:when (and (register? reg) (opand? opand))
        pc] 
      [`(jump-if ,op ,label)
        #:when (and (relop? op) (label? label))
        pc]
      [_ (error "invalid Parent-x64 v4 expression in link-paren-x64 (populate)" s)]))

  (define (link-paren-x64-replace-s s)
    (match s
      [`(set! ,addr ,int32-value)
        #:when (and (addr? addr) (int32? int32-value))
        s] 
      [`(set! ,addr ,trg)
        #:when (and (addr? addr) (trg? trg))
        (if (label? trg)
          `(set! ,addr ,(dict-ref label-map trg))
          s)]
      [`(set! ,reg ,loc)
        #:when (and (register? reg) (loc? loc))
        s] 
      [`(set! ,reg ,triv)
        #:when (and (register? reg) (triv? triv))
        (if (label? triv)
          `(set! ,reg ,(dict-ref label-map triv))
          s)]
      [`(set! ,reg (,op ,reg ,int32-value))
        #:when (and (register? reg) (binop? op) (int32? int32-value))
        s] 
      [`(set! ,reg (,op ,reg ,loc))
        #:when (and (register? reg) (binop? op) (loc? loc))
        s] 
      [`(with-label ,label ,stmnt)
        #:when (label? label)
        (link-paren-x64-replace-s stmnt)]
      [`(jump ,trg)
        #:when (trg? trg)
        (if (label? trg)
          `(jump ,(dict-ref label-map trg))
          s)]
      [`(compare ,reg ,opand)
        #:when (and (register? reg) (opand? opand))
        s] 
      [`(jump-if ,op ,label)
        #:when (and (relop? op) (label? label))
        `(jump-if ,op ,(dict-ref label-map label))]
      [_ (error "invalid Parent-x64 v4 expression in link-paren-x64 (replace)" s)]))

  (define (link-paren-x64-ss ss)
    (foldl 
      (lambda (s pc)
        (add1 (link-paren-x64-populate-s s pc)))
      0
      ss)
    (foldr
      (lambda (s p)
        (cons (link-paren-x64-replace-s s) p))
      '()
      ss))
  
  (match p 
    [`(begin ,ss ...) `(begin ,@(link-paren-x64-ss ss))]
    [_ (error "invalid Parent-x64 v4 program in link-paren-x64" p)]))

(define (interp-paren-x64 p)
  (define pc-addr? natural-number/c)
  (define (trg? x) (or (register? x) (pc-addr? x)))
  (define (triv? x) (or (trg? x) (int64? x)))
  (define (loc? x) (or (register? x) (addr? x)))
  (define (opand? x) (or (int64? x) (register? x)))

  (define memory (make-hash))

  (define (interp-trg trg)
    (cond
      [(register? trg) (dict-ref memory trg)]
      [(pc-addr? trg) trg]
      [else (error "invalid trg" trg)]))

  (define (interp-triv triv)
    (cond
      [(trg? triv) (interp-trg triv)]
      [(int64? triv) triv]
      [else (error "invalid triv" triv)]))

  (define (interp-opand opand)
    (cond
      [(register? opand) (dict-ref memory opand)]
      [(int64? opand) opand]
      [else (error "invalid opand" opand)]))

  (define (interp-reg reg)
    (if (register? reg)
      (dict-ref memory reg)
      (error "invalid reg" reg)))

  (define (interp-loc loc)
    (if (loc? loc)
      (dict-ref memory loc)
      (error "invalid loc" loc)))
  
  (define (interp-statement code pc)
    (define stmnt (list-ref code pc))
    (match stmnt
      [`(set! ,addr ,int32-value)
        #:when (and (addr? addr) (int32? int32-value))
        (begin 
          (dict-set! memory addr int32-value)
          (interp-loop code (+ pc 1)))]
      [`(set! ,addr ,trg)
        #:when (and (addr? addr) (trg? trg))
        (begin
          (dict-set! memory addr (interp-trg trg))
          (interp-loop code (+ pc 1)))]
      [`(set! ,reg ,loc) 
        #:when (and (register? reg) (loc? loc))
        (begin
          (dict-set! memory reg (interp-loc loc))
          (interp-loop code (+ pc 1)))]
      [`(set! ,reg ,triv) 
        #:when (and (register? reg) (triv? triv))
        (begin
          (dict-set! memory reg (interp-triv triv))
          (interp-loop code (+ pc 1)))]
      [`(set! ,reg (,op ,reg ,int32-value)) 
        #:when (and (register? reg) (binop? op) (int32? int32-value))
        (begin
          (dict-set! memory reg (apply (binop->proc op) (list (interp-reg reg) int32-value)))
          (interp-loop code (+ pc 1)))]
      [`(set! ,reg (,op ,reg ,loc))
        #:when (and (register? reg) (binop? op) (loc? loc))
        (begin
          (dict-set! memory reg (apply (binop->proc op) (list (interp-reg reg) (interp-loc loc))))
          (interp-loop code (+ pc 1)))]
      [`(jump ,trg)
        #:when (trg? trg)
        (if (pc-addr? trg)
          (interp-loop code trg)
          (interp-loop code (dict-ref memory trg)))]
      [`(compare ,reg ,opand)
        #:when (and (register? reg) (opand? opand))
        (interp-loop code (+ pc 1))]
      [`(jump-if ,op ,pc-addr)
        #:when (and (relop? op) (pc-addr? pc-addr))
        (let ([prev-stmnt (list-ref code (- pc 1))])
          (match prev-stmnt
            [`(compare ,reg ,opand)
              #:when (and (register? reg) (opand? opand))
              (if (apply (relop->proc op) (list (interp-reg reg) (interp-opand opand)))
                (interp-loop code pc-addr)
                (interp-loop code (+ pc 1)))]
            [_ (error "no (valid) compare found before jump-if statement" stmnt)]))]
      [_ (error "invalid Paren-x64-rt v4 statement in interp-paren-x64" stmnt)]))

  (define (interp-loop code pc)
    (if (= pc (length code))
      (dict-ref memory 'rax)
      (interp-statement code pc)))

  (match (link-paren-x64 p)
    [`(begin ,ss ...) (interp-loop ss 0)]
    [_ (error "invalid Parent-x64 v4 program in interp-paren-x64" p)]))

(define (implement-fvars p)
  (define (loc? x) (or (register? x) (fvar? x)))
  (define (opand? x) (or (int64? x) (register? x)))
  (define (trg? x) (or (register? x) (label? x)))
  (define (triv? x) (or (trg? x) (int64? x)))

  (define (fvar->reify fvar)
    (if (fvar? fvar) 
      (let ((bptr (current-frame-base-pointer-register)) 
            (indx (* 8 (fvar->index fvar))))
        `(,bptr - ,indx))
      (error "invalid fvar format" fvar)))

  (define (implement-fvars-s s)
    (match s
      [`(set! ,fvar ,int32-value)
        #:when (and (fvar? fvar) (int32? int32-value))
        `(set! ,(fvar->reify fvar) ,int32-value)]
      [`(set! ,fvar ,trg) 
        #:when (and (fvar? fvar) (trg? trg))
        (if (fvar? trg)
          `(set! ,(fvar->reify fvar) ,(fvar->reify trg))
          `(set! ,(fvar->reify fvar) ,trg))]
      [`(set! ,reg ,loc)
        #:when (and (register? reg) (loc? loc))
        (if (fvar? loc)
          `(set! ,reg ,(fvar->reify loc))
          `(set! ,reg ,loc))]
      [`(set! ,reg ,triv)
        #:when (and (register? reg) (triv? triv))
        s] 
      [`(set! ,reg (,op ,reg ,int32-value))
        #:when (and (register? reg) (binop? op) (int32? int32-value))
        s] 
      [`(set! ,reg (,op ,reg ,loc))
        #:when (and (register? reg) (binop? op) (loc? loc))
        (if (fvar? loc)
          `(set! ,reg (,op ,reg ,(fvar->reify loc)))
          `(set! ,reg (,op ,reg ,loc)))]
      [`(with-label ,label ,stmnt)
        #:when (label? label)
        `(with-label ,label ,(implement-fvars-s stmnt))]
      [`(jump ,trg)
        #:when (trg? trg)
        s]
      [`(compare ,reg ,opand)
        #:when (and (register? reg) (opand? opand))
        s]
      [`(jump-if ,op ,label)
        #:when (and (relop? op) (label? label))
        s]
      [_ (error "invalid Paren-x64-fvars v4 statement in implement-fvars" s)]))

  (define (implement-fvars-ss ss)
    (foldr
      (lambda (s accu)
        (cons (implement-fvars-s s) accu))
      '()
      ss))
  
  (match p 
    [`(begin ,ss ...) `(begin ,@(implement-fvars-ss ss))]
    [_ (error "invalid Paren-x64-fvars v4 program in implement-fvars" p)]))

(define (patch-instructions p)
  (define (loc? x) (or (register? x) (fvar? x)))
  (define (opand? x) (or (int64? x) (loc? x)))
  (define (triv? x) (or (opand? x) (label? x)))
  (define (trg? x) (or (label? x) (loc? x)))
  
  (define (negate-relop op)
    (match op
      ['< '>=]
      ['<= '>]
      ['= '!=]
      ['>= '<]
      ['> '<=]
      ['!= '=]
      [_ (error "unsupported relop operation" op)]))
  
  (define (patch-instructions-s s)
    (match s
      [`(halt ,opand)
        #:when (opand? opand)
        (list `(set! ,(current-return-value-register) ,opand))]
      [`(set! ,loc ,triv)
        #:when (and (loc? loc) (triv? triv))
        (if (and (fvar? loc) (or (fvar? triv) (not (int32? triv))))
          (let ((reg (car (current-auxiliary-registers)))) 
            `((set! ,reg ,triv) (set! ,loc ,reg)))
          (list s))]
      [`(set! ,loc (,op ,loc ,opand))
        #:when (and (loc? loc) (binop? op) (opand? opand))
        (if (fvar? loc)
          (let ((reg (car (current-auxiliary-registers)))) 
            `((set! ,reg ,loc) (set! ,reg (,op ,reg ,opand)) (set! ,loc ,reg)))
          (list s))]
      [`(jump ,trg)
        #:when (trg? trg)
        (if (fvar? trg)
          (let ([reg (car (current-patch-instructions-registers))]) 
            `((set! ,reg ,trg) (jump ,reg)))
          (list s))]
      [`(with-label ,label ,stmnt)
        #:when (label? label)
        (let ((res (patch-instructions-s stmnt)))
          `((with-label ,label ,(car res)) ,@(cdr res)))]
      [`(compare ,loc ,opand)
        #:when (and (loc? loc) (opand? opand))
        (if (fvar? loc)
          (let ([reg (car (current-patch-instructions-registers))])
            `((set! ,reg ,loc) (compare ,reg ,opand)))
          (list s))]
      [`(jump-if ,op ,trg)
        #:when (and (relop? op) (trg? trg))
        (if (loc? trg)
          (let ([lbl (fresh-label)]
                [reg (car (current-patch-instructions-registers))]) 
            `((jump-if ,(negate-relop op) ,lbl) (jump ,trg) (with-label ,lbl (set! ,reg ,reg))))
          (list s))]
      [_ (error "invalid Para-asm-lang v4 statement in patch-instructions" s)]))

  (define (patch-instructions-ss ss)
    (append-map patch-instructions-s ss))

  (match p 
    [`(begin ,ss ...) `(begin ,@(patch-instructions-ss ss))]
    [_ (error "invalid Para-asm-lang v4 program in patch-instructions" p)]))

(define (flatten-program p)
  (define (opand? x) (or (int64? x) (loc? x)))
  (define (loc? x) (or (register? x) (fvar? x)))
  (define (trg? x) (or (label? x) (loc? x)))
  (define (triv? x) (or (opand? x) (label? x)))

  (define (flatten-program-s s)
    (match s
      [`(set! ,loc ,triv)
        #:when (and (loc? loc) (triv? triv))
        s]
      [`(set! ,loc (,op ,loc ,opand))
        #:when (and (loc? loc) (binop? op) (opand? opand))
        s]
      [_ (error "invalid Block-asm-lang v4 statement in flatten-program" s)]))

  (define (flatten-program-ss ss)
    (foldr
      (lambda (s accu)
        (cons (flatten-program-s s) accu))
      '()
      ss))

  (define (flatten-program-tail tail)
    (match tail
      [`(halt ,opand)
        #:when (opand? opand)
        (list tail)]
      [`(jump ,trg)
        #:when (trg? trg)
        (list tail)]
      [`(begin ,ss ... ,tail)
        (let ((flattened-tail (flatten-program-tail tail)))
          `(,@(flatten-program-ss ss) ,@flattened-tail))]
      [`(if (,op ,loc ,opand) (jump ,trg1) (jump ,trg2))
        #:when (and (relop? op) (loc? loc) (opand? opand) (trg? trg1) (trg? trg2))
        `((compare ,loc ,opand) (jump-if ,op ,trg1) (jump ,trg2))]
      [_ (error "invalid Block-asm-lang v4 tail in flatten-program" tail)]))

  (define (flatten-program-block block)
    (match block
      [`(define ,label ,tail)
        (let ((flattened-tail (flatten-program-tail tail)))
          `((with-label ,label ,(car flattened-tail)) ,@(cdr flattened-tail)))]
      [_ (error "invalid Block-asm-lang v4 block in flatten-program" block)]))

  (define (flatten-program-blocks blocks)
    (append-map flatten-program-block blocks))

  (match p 
    [`(module ,blocks ... ,block) 
      `(begin ,@(flatten-program-blocks blocks) ,@(flatten-program-block block))]
    [_ (error "invalid Block-asm-lang v4 program in flatten-program" p)]))

(define (resolve-predicates p)
  (define (loc? x) (or (register? x) (fvar? x)))
  (define (opand? x) (or (int64? x) (loc? x)))
  (define (trg? x) (or (label? x) (loc? x)))
  (define (triv? x) (or (opand? x) (label? x)))

  (define (resolve-predicates-s s)
    (match s
      [`(set! ,loc ,triv)
        #:when (and (loc? loc) (triv? triv))
        s]
      [`(set! ,loc (,op ,loc ,opand))
        #:when (and (loc? loc) (binop? op) (opand? opand))
        s]
      [_ (error "invalid Block-pred-lang v4 statement in resolve-predicates" s)]))

  (define (resolve-predicates-ss ss)
    (foldr
      (lambda (s accu)
        (cons (resolve-predicates-s s) accu))
      '()
      ss))

  (define (resolve-predicates-tail tail)
    (match tail
      [`(halt ,opand)
        #:when (opand? opand)
        tail]
      [`(jump ,trg)
        #:when (trg? trg)
        tail]
      [`(begin ,ss ... ,tail)
        `(begin ,@(resolve-predicates-ss ss) ,(resolve-predicates-tail tail))]
      [`(if ,pred (jump ,trg1) (jump ,trg2))
        #:when (and (trg? trg1) (trg? trg2))
        (match pred
          [`(,op ,loc ,opand)
            #:when (and (relop? op) (loc? loc) (opand? opand))
            tail]
          [`(true)
            `(jump ,trg1)]
          [`(false)
            `(jump ,trg2)]
          [`(not ,inner-pred)
            (resolve-predicates-tail `(if ,inner-pred (jump ,trg2) (jump ,trg1)))]
          [_ (error "invalid Block-pred-lang v4 pred in resolve-predicates" pred)])]
      [_ (error "invalid Block-pred-lang v4 tail in resolve-predicates" tail)]))

  (define (resolve-predicates-block block)
    (match block
      [`(define ,label ,tail)
        `(define ,label ,(resolve-predicates-tail tail))]
      [_ (error "invalid Block-pred-lang v4 block in resolve-predicates" block)]))

  (define (resolve-predicates-blocks blocks)
    (foldr
      (lambda (block accu)
        (cons (resolve-predicates-block block) accu))
      '()
      blocks))

  (match p
    [`(module ,blocks ... ,block)
      `(module ,@(resolve-predicates-blocks blocks) ,(resolve-predicates-block block))]
    [_ (error "invalid Block-pred-lang v4 program in resolve-predicates" p)]))

(define (expose-basic-blocks p)
  (define (loc? x) (or (register? x) (fvar? x)))
  (define (triv? x) (or (int64? x) (loc? x)))

  (define (expose-basic-blocks-pred pred lbl-consequent lbl-alternative)
    (match pred
      [`(,op ,loc ,triv)
        #:when (and (relop? op) (loc? loc) (triv? triv))
        (values 
          `(if ,pred (jump ,lbl-consequent) (jump ,lbl-alternative))
          '())]
      [`(true)
        (values
          `(if ,pred (jump ,lbl-consequent) (jump ,lbl-alternative))
          '())]
      [`(false)
        (values
          `(if ,pred (jump ,lbl-consequent) (jump ,lbl-alternative))
          '())]
      [`(not ,inner-pred)
        (expose-basic-blocks-pred inner-pred lbl-alternative lbl-consequent)] 
      [`(begin ,effects ... ,inner-pred)
        (let-values ([(exposed-effects effects-blocks) (expose-basic-blocks-effects effects)]
                     [(exposed-inner-pred inner-pred-blocks) (expose-basic-blocks-pred inner-pred lbl-consequent lbl-alternative)])
          (values
            (if (empty? exposed-effects)
              exposed-inner-pred
              `(begin ,@(append exposed-effects (list exposed-inner-pred))))
            (append effects-blocks inner-pred-blocks)))]
      [`(if ,inner-pred ,inner-pred-consequent ,inner-pred-alternative)
        (let ([lbl-inner-consequent (fresh-label)]
              [lbl-inner-alternative (fresh-label)])
          (let-values ([(exposed-inner-consequent-pred inner-consequent-pred-blocks) 
                        (expose-basic-blocks-pred inner-pred-consequent lbl-consequent lbl-alternative)]
                       [(exposed-inner-alternative-pred inner-alternative-pred-blocks) 
                        (expose-basic-blocks-pred inner-pred-alternative lbl-consequent lbl-alternative)]
                       [(exposed-inner-pred inner-pred-blocks) 
                        (expose-basic-blocks-pred inner-pred lbl-inner-consequent lbl-inner-alternative)])
            (values 
              exposed-inner-pred
              (append
                (append inner-pred-blocks inner-consequent-pred-blocks inner-alternative-pred-blocks)
                (list 
                  `(define ,lbl-inner-consequent ,exposed-inner-consequent-pred)
                  `(define ,lbl-inner-alternative ,exposed-inner-alternative-pred))))))]
      [_ (error "invalid Nested-asm-lang v4 pred in expose-basic-blocks" pred)]))

  (define (expose-basic-blocks-effect effect)
    (match effect
      [`(set! ,loc ,triv) 
        #:when (and (loc? loc) (triv? triv))
        (values (list effect) '())]
      [`(set! ,loc (,op ,loc ,triv))
        #:when (and (loc? loc) (binop? op) (triv? triv))
        (values (list effect) '())]
      [`(begin ,effects ...)
        (expose-basic-blocks-effects effects)]
      [`(if ,pred ,effect-consequent ,effect-alternative) 
        (error "not implemented" effect)]
      [_ (error "invalid Nested-asm-lang v4 effect in expose-basic-blocks" effect)]))

  (define (expose-basic-blocks-effects effects)
    (define exposed-effects 
      (foldl
        (lambda (effect accu)
          (let ([exposed-effects (first accu)]
                [blocks (second accu)])
            (let-values ([(exposed-effect effect-blocks) (expose-basic-blocks-effect effect)])
              (list (append exposed-effects exposed-effect)
                    (append blocks effect-blocks)))))
        (list '() '())
        effects))
    (values (first exposed-effects) (second exposed-effects)))

  (define (expose-basic-blocks-tail tail)
    (match tail
      [`(halt ,triv)
        #:when (triv? triv)
        (values tail '())]
      [`(begin ,effects ... ,inner-tail)
        (let-values ([(exposed-effects effects-blocks) (expose-basic-blocks-effects effects)]
                     [(exposed-inner-tail inner-tail-blocks) (expose-basic-blocks-tail inner-tail)])
          (values
            `(begin ,@(append exposed-effects (list exposed-inner-tail)))
            (append effects-blocks inner-tail-blocks)))]
      [`(if ,pred ,tail-consequent ,tail-alternative)
        (let ([lbl-consequent (fresh-label)]
              [lbl-alternative (fresh-label)])
          (let-values ([(exposed-tail-consequent tail-consequent-blocks) (expose-basic-blocks-tail tail-consequent)]
                       [(exposed-tail-alternative tail-alternative-blocks) (expose-basic-blocks-tail tail-alternative)]
                       [(exposed-pred pred-blocks) (expose-basic-blocks-pred pred lbl-consequent lbl-alternative)])
            (values
              exposed-pred
              (append
                (append pred-blocks tail-consequent-blocks tail-alternative-blocks)
                (list 
                  `(define ,lbl-consequent ,exposed-tail-consequent)
                  `(define ,lbl-alternative ,exposed-tail-alternative))))))]
      [_ (error "invalid Nested-asm-lang v4 tail in expose-basic-blocks" tail)]))
  
  (match p
    [`(module ,tail)
      (let-values ([(new-tail tail-blocks) (expose-basic-blocks-tail tail)])
        `(module (define ,(fresh-label) ,new-tail) ,@tail-blocks))]
    [_ (error "invalid Nested-asm-lang v4 program in expose-basic-blocks" p)]))

; TODO implement
(define (optimize-predicates p)
  #f)

(define (replace-locations p)
  (define (triv? x) (or (int64? x) (aloc? x)))

  (define assignment-map (make-hash))

  (define (triv->home triv)
    (if (aloc? triv)
      (dict-ref assignment-map triv)
      triv))

  (define (replace-locations-pred pred)
    (match pred
      [`(,op ,aloc ,triv)
        #:when (and (relop? op) (aloc? aloc) (triv? triv))
        `(,op ,(dict-ref assignment-map aloc) ,(triv->home triv))]
      [`(true)
        pred]
      [`(false)
        pred]
      [`(not ,inner-pred)
        `(not ,(replace-locations-pred inner-pred))]
      [`(begin ,effects ... ,pred)
        `(begin ,@(replace-locations-effects effects) ,(replace-locations-pred pred))]
      [`(if ,inner-pred ,inner-pred-consequent ,inner-pred-alternative)
        `(if
          ,(replace-locations-pred inner-pred)
          ,(replace-locations-pred inner-pred-consequent)
          ,(replace-locations-pred inner-pred-alternative))]
      [_ (error "invalid Asm-pred-lang v4 pred in replace-locations" pred)]))

  (define (replace-locations-effect effect)
    (match effect
      [`(set! ,aloc ,triv)
        #:when (and (aloc? aloc) (triv? triv))
        `(set! ,(dict-ref assignment-map aloc) ,(triv->home triv))]
      [`(set! ,aloc (,op ,aloc ,triv))
        #:when (and (aloc? aloc) (triv? triv))
        (let ((new-home (dict-ref assignment-map aloc)))
          `(set! ,new-home (,op ,new-home ,(triv->home triv))))]
      [`(begin ,effects ... ,effect)
        `(begin 
          ,@(replace-locations-effects effects) 
          ,(replace-locations-effect effect))]
      [`(if ,pred ,effect-consequent ,effect-alternative)
        `(if
          ,(replace-locations-pred pred)
          ,(replace-locations-effect effect-consequent)
          ,(replace-locations-effect effect-alternative))]
      [_ (error "invalid Asm-pred-lang v4 effect in replace-locations" effect)]))

  (define (replace-locations-effects effects) 
    (foldr
      (lambda (effect accu) 
        (cons (replace-locations-effect effect) accu))
      '()
      effects))

  (define (replace-locations-tail tail)
    (match tail
      [`(halt ,triv)
        #:when (triv? triv)
          `(halt ,(triv->home triv))]
      [`(begin ,effects ... ,tail)
        `(begin 
          ,@(replace-locations-effects effects) 
          ,(replace-locations-tail tail))]
      [`(if ,pred ,tail-consequent ,tail-alternative)
        `(if 
          ,(replace-locations-pred pred) 
          ,(replace-locations-tail tail-consequent) 
          ,(replace-locations-tail tail-alternative))]
      [_ (error "invalid Asm-pred-lang v4 tail in replace-locations" tail)]))

  (match p
    [`(module (,info ...) ,tail)
      (begin
        (for-each 
          (lambda (assignment)
            (dict-set! assignment-map (first assignment) (second assignment)))
          (info-ref info 'assignment))
        `(module () ,(replace-locations-tail tail)))]
    [_ (error "invalid Asm-pred-lang v4 program in replace-locations" p)]))

(define (assign-homes-opt p)
  (replace-locations 
    (assign-registers 
      (conflict-analysis 
        (undead-analysis 
          (uncover-locals p))))))

(define (uncover-locals p)
  (define (triv? x) (or (int64? x) (aloc? x)))
  
  (define locals (mutable-set)) 

  (define (uncover-locals-pred pred)
    (match pred
      [`(,op ,aloc ,triv)
        #:when (and (relop? op) (aloc? aloc) (triv? triv))
        (begin
          (set-add! locals aloc)
          (when (aloc? triv) (set-add! locals triv)))]
      [`(true)
        #t]
      [`(false)
        #t]
      [`(not ,inner-pred)
        (uncover-locals-pred inner-pred)]
      [`(begin ,effects ... ,pred)
        (begin
          (uncover-locals-effects effects)
          (uncover-locals-pred pred))]
      [`(if ,inner-pred ,inner-pred-consequent ,inner-pred-alternative)
        (begin
          (uncover-locals-pred inner-pred)
          (uncover-locals-pred inner-pred-consequent)
          (uncover-locals-pred inner-pred-alternative))]
      [_ (error "invalid Asm-pred-lang v4 pred in uncover-locals" pred)]))

  (define (uncover-locals-effect effect)
    (match effect
      [`(set! ,aloc ,triv)
        #:when (and (aloc? aloc) (triv? triv))
        (begin
          (set-add! locals aloc)
          (when (aloc? triv) (set-add! locals triv)))]
      [`(set! ,aloc (,op ,aloc ,triv))
        #:when (and (aloc? aloc) (triv? triv))
        (begin
          (set-add! locals aloc)
          (when (aloc? triv) (set-add! locals triv)))]
      [`(begin ,effects ... ,effect)
        (begin
          (uncover-locals-effects effects)
          (uncover-locals-effect effect))]
      [`(if ,pred ,effect-consequent ,effect-alternative)
        (begin
          (uncover-locals-pred pred)
          (uncover-locals-effect effect-consequent)
          (uncover-locals-effect effect-alternative))]
      [_ (error "invalid Asm-pred-lang v4 effect in uncover-locals" effect)]))

  (define (uncover-locals-effects effects) 
    (for-each uncover-locals-effect effects))

  (define (uncover-locals-tail tail)
    (match tail
      [`(halt ,triv)
        #:when (triv? triv)
        (when (aloc? triv) (set-add! locals triv))]
      [`(begin ,effects ... ,inner-tail)
        (begin
          (uncover-locals-effects effects)
          (uncover-locals-tail inner-tail))]
      [`(if ,pred ,tail-consequent ,tail-alternative)
        (begin
          (uncover-locals-pred pred)
          (uncover-locals-tail tail-consequent)
          (uncover-locals-tail tail-alternative))]
      [_ (error "invalid Asm-pred-lang v4 tail in uncover-locals" tail)]))

  (match p
    [`(module (,info ...) ,tail)
      (begin
        (uncover-locals-tail tail)
        (let ([new-info (info-set info 'locals (set->list locals))])
          `(module ,new-info ,tail)))]
    [_ (error "invalid Asm-pred-lang v4 program in uncover-locals" p)]))

(define (undead-analysis p)
  (define (triv? x) (or (int64? x) (aloc? x)))

  (define (union-undead-sets xs ys)
    (set->list 
      (set-union
        (list->set (car xs))
        (list->set (car ys)))))

  (define (compute-undead undead-sets assigned-set used-set)
    (unless (list? undead-sets) (error "invalid undead-sets list" undead-sets))
    (let* ([last-undead-set (list->set (car undead-sets))]
           [last-without-assigned-set (set-subtract last-undead-set assigned-set)]
           [last-with-used-set (set-union last-without-assigned-set used-set)]
           [new-undead (set->list last-with-used-set)])
      (cons (sort new-undead symbol<?) undead-sets)))

  (define (undead-analysis-pred pred undead-sets)
    (match pred
      [`(,op ,aloc ,triv)
        #:when (and (relop? op) (aloc? aloc) (triv? triv))
        (if (aloc? triv)
            (compute-undead undead-sets (set aloc) (set triv))
            (compute-undead undead-sets (set aloc) (set)))]
      [`(true)
        (cons (car undead-sets) undead-sets)]
      [`(false)
        (cons (car undead-sets) undead-sets)]
      [`(not ,inner-pred)
        (undead-analysis-pred inner-pred undead-sets)]
      [`(begin ,effects ,inner-pred)
        (let ((new-undead-sets (undead-analysis-pred inner-pred undead-sets)))
          (undead-analysis-effects effects new-undead-sets))]
      [`(if ,inner-pred ,inner-pred-consequent ,inner-pred-alternative)
        (let* ([pred-undead-sets (undead-analysis-pred inner-pred undead-sets)]
               [consequent-undead-sets (undead-analysis-pred inner-pred-consequent undead-sets)]
               [alternative-undead-sets (undead-analysis-pred inner-pred-alternative undead-sets)]
               [union-undead-sets (union-undead-sets consequent-undead-sets alternative-undead-sets)])
          (list union-undead-sets consequent-undead-sets alternative-undead-sets))]
      [_ (error "invalid asm-pred-lang-v4/locals pred in undead-analysis" pred)]))

  (define (undead-analysis-effect effect undead-sets)
    (match effect
      [`(set! ,aloc ,triv)
        #:when (and (aloc? aloc) (triv? triv))
          (if (aloc? triv)
            (compute-undead undead-sets (set aloc) (set triv))
            (compute-undead undead-sets (set aloc) (set)))]
      [`(set! ,aloc (,op ,aloc ,triv))
        #:when (and (aloc? aloc) (binop? op) (triv? triv))
          (if (aloc? triv)
            (compute-undead undead-sets (set aloc) (set aloc triv))
            (compute-undead undead-sets (set aloc) (set)))]
      [`(begin ,effects ... ,effect) 
        (let ((new-undead-sets (undead-analysis-effect effect undead-sets)))
          (undead-analysis-effects effects new-undead-sets))]
      [`(if ,pred ,effect-consequent ,effect-alternative)
        (let* ([pred-undead-sets (undead-analysis-pred pred undead-sets)]
               [consequent-undead-sets (undead-analysis-effect effect-consequent undead-sets)]
               [alternative-undead-sets (undead-analysis-effect effect-alternative undead-sets)]
               [union-undead-sets (union-undead-sets consequent-undead-sets alternative-undead-sets)])
          (list union-undead-sets consequent-undead-sets alternative-undead-sets))]
      [_ (error "invalid asm-pred-lang-v4/locals effect in undead-analysis" effect)]))
  
  (define (undead-analysis-effects effects undead-sets) 
    (foldr 
      (lambda (effect current-undead-sets) 
        (undead-analysis-effect effect current-undead-sets))
      undead-sets
      effects))

  (define (undead-analysis-tail tail undead-sets)
    (match tail
      [`(halt ,triv)
        #:when (triv? triv)
          (if (aloc? triv)
            (compute-undead undead-sets (set) (set triv))
            (cons (car undead-sets) undead-sets))]
      [`(begin ,effects ... ,tail) 
        (let ((new-undead-sets (undead-analysis-tail tail undead-sets)))
          (undead-analysis-effects effects new-undead-sets))]
      [`(if ,pred ,tail-consequent ,tail-alternative)
        (let* ([pred-undead-sets (undead-analysis-pred pred undead-sets)]
               [consequent-undead-sets (undead-analysis-tail tail-consequent undead-sets)]
               [alternative-undead-sets (undead-analysis-tail tail-alternative undead-sets)]
               [union-undead-sets (union-undead-sets consequent-undead-sets alternative-undead-sets)])
          (list union-undead-sets consequent-undead-sets alternative-undead-sets))]
      [_ (error "invalid asm-pred-lang-v4/locals tail in undead-analysis" tail)]))

  (match p
    [`(module (,info ...) ,tail)
      (let* ((undead-sets (undead-analysis-tail tail (list '())))
             (new-info (info-set info 'undead-out (cdr undead-sets))))
        `(module ,new-info ,tail))]
    [_ (error "invalid asm-pred-lang-v4/locals module in undead-analysis" p)]))

(define (conflict-analysis p)
  (define (triv? x) (or (int64? x) (aloc? x)))

  (define (compute-conflict-graph conflict-graph undead-list defined-var . conflict-vars)
    (let ([conflicts (if (null? conflict-vars)
                        (remove defined-var undead-list)
                        (remove* (cons defined-var conflict-vars) undead-list))])
      (if (empty? conflicts)
        conflict-graph
        (add-edges conflict-graph defined-var conflicts))))
  
  (define (conflict-analysis-pred pred undead-sets conflict-graph)
    (match pred
      [`(,op ,aloc ,triv)
        #:when (and (relop? op) (aloc? aloc) (triv? triv))
        (cons (cdr undead-sets) (list conflict-graph))] 
      [`(true)
        (cons (cdr undead-sets) (list conflict-graph))] 
      [`(false)
        (cons (cdr undead-sets) (list conflict-graph))] 
      [`(not ,inner-pred)
        (conflict-analysis-pred inner-pred undead-sets conflict-graph)]
      [`(begin ,effects ... ,inner-pred)
        (let ([res (conflict-analysis-effects effects undead-sets conflict-graph)])
          (conflict-analysis-pred inner-pred (first res) (second res)))]
      [`(if ,inner-pred ,inner-pred-consequent ,inner-pred-alternative)
        (let* ([alternative-res (conflict-analysis-pred inner-pred-alternative undead-sets conflict-graph)]
               [consequent-res (conflict-analysis-pred inner-pred-consequent undead-sets (second alternative-res))]
               [pred-res (conflict-analysis-pred pred undead-sets (second consequent-res))])
          (cons (cdr undead-sets) (list (second pred-res))))]
      [_ (error "invalid asm-pred-lang-v4/undead pred in conflict-analysis" pred)]))

  (define (conflict-analysis-effect effect undead-sets conflict-graph)
    (match effect
      [`(set! ,aloc ,triv)
        #:when (and (aloc? aloc) (triv? triv))
          (let ([new-conflict-graph (compute-conflict-graph
                                      conflict-graph
                                      (car undead-sets)
                                      aloc
                                      triv)])
            (cons (cdr undead-sets) (list new-conflict-graph)))]
      [`(set! ,aloc (,op ,aloc ,triv))
        #:when (and (aloc? aloc) (binop? op) (triv? triv))
          (let ([new-conflict-graph (compute-conflict-graph
                                      conflict-graph
                                      (car undead-sets)
                                      aloc
                                      triv)])
            (cons (cdr undead-sets) (list new-conflict-graph)))]
      [`(begin ,effects ... ,effect)
        (let ([res (conflict-analysis-effects effects undead-sets conflict-graph)])
          (conflict-analysis-effect effect (first res) (second res)))]
      [`(if ,pred ,effect-consequent ,effect-alternative)
        (let* ([alternative-res (conflict-analysis-effect effect-alternative undead-sets conflict-graph)]
               [consequent-res (conflict-analysis-effect effect-consequent undead-sets (second alternative-res))]
               [pred-res (conflict-analysis-pred pred undead-sets (second consequent-res))])
          (cons (cdr undead-sets) (list (second pred-res))))]
      [_ (error "invalid asm-pred-lang-v4/undead effect in conflict-analysis" effect)]))

  (define (conflict-analysis-effects effects undead-sets conflict-graph) 
    (foldl
      (lambda (effect accu) 
        (let* ([undead-sets (first accu)]
               [conflict-graph (second accu)]
               [res (conflict-analysis-effect effect undead-sets conflict-graph)]
               [new-undead-sets (first res)]
               [new-conflict-graph (second res)])
          (cons new-undead-sets (list new-conflict-graph))))
      (cons undead-sets (list conflict-graph))
      effects))

  (define (conflict-analysis-tail tail undead-sets conflict-graph)
    (match tail
      [`(halt ,triv)
        #:when (triv? triv)
          (let ([new-conflict-graph (compute-conflict-graph 
                                      conflict-graph
                                      (car undead-sets)
                                      triv)])
            (cons (cdr undead-sets) (list new-conflict-graph)))]
      [`(begin ,effects ... ,tail) 
        (let ([res (conflict-analysis-effects effects undead-sets conflict-graph)])
          (conflict-analysis-tail tail (first res) (second res)))]
      [`(if ,pred ,tail-consequent ,tail-alternative)
        (let* ([alternative-res (conflict-analysis-tail tail-alternative undead-sets conflict-graph)]
               [consequent-res (conflict-analysis-tail tail-consequent undead-sets (second alternative-res))]
               [pred-res (conflict-analysis-pred pred undead-sets (second consequent-res))])
          (cons (cdr undead-sets) (list (second pred-res))))]
      [_ (error "invalid asm-pred-lang-v4/undead tail in conflict-analysis" tail)]))

  (match p
    [`(module (,info ...) ,tail)
      (let* ([conflict-graph (new-graph (info-ref info 'locals))]
             [undead-sets (info-ref info 'undead-out)]
             [res (conflict-analysis-tail tail undead-sets conflict-graph)]
             [new-info (info-set info 'conflicts (second res))])
        `(module ,(info-remove new-info 'undead-out),tail))]
    [_ (error "invalid asm-pred-lang-v4/undead module in conflict-analysis" p)]))

(define (assign-registers p)
  (define (register-allocator info)
    (define locals (info-ref info 'locals))
    (define conflicts (info-ref info 'conflicts))

    (define conflict-graph 
      (foldl 
        (lambda (conflict graph)
          (let ([aloc (car conflict)]
                [conflicts (cadr conflict)])
            (add-edges graph aloc conflicts)))
        (new-graph locals)
        conflicts))

    (define sorted-locals 
      (sort locals 
        (lambda (local1 local2)
          (< (length (get-neighbors conflict-graph local1))
             (length (get-neighbors conflict-graph local2))))))

    (define (has-conflict? ploc conflicts assignments)
      (if (empty? conflicts)
        #f
        (or (member (list (car conflicts) ploc) assignments)
            (has-conflict? ploc (cdr conflicts) assignments))))
    
    (define fvar-index 0)

    (define (construct-assignments locals graph)
      (if (empty? locals) 
        '()
        (let* ([local (car locals)]
               [conflicts (get-neighbors graph local)]
               [assignments (construct-assignments (cdr locals) (remove-vertex graph local))])
          (let loop ([registers (reverse (current-assignable-registers))]) 
            (if (empty? registers)
              (let ([new-assignments (cons (list local (make-fvar fvar-index)) assignments)])
                (set! fvar-index (+ fvar-index 1)) 
                new-assignments)
              (let ([ploc (car registers)])
                (if (has-conflict? ploc conflicts assignments)
                  (loop (cdr registers))
                  (cons (list local ploc) assignments))))))))

    (construct-assignments sorted-locals conflict-graph)
  )

  (match p
    [`(module (,info ...) ,tail)
      (let ((assignments (register-allocator info)))
        `(module ,(info-set info 'assignment (reverse assignments)) ,tail))]
    [_ (error "invalid Asm-pred-lang v4/assignment module in assign-registers" p)]))

(define (select-instructions p)
  (define (triv? x) (or (int64? x) (aloc? x)))
  (define (value? x) 
    (or (triv? x) 
        (match x
          [`(,op ,triv1 ,triv2)
            #:when (and (binop? op) (triv? triv1) (triv? triv2))
            #t]
          [_ #f])))

  (define (unwrap-begin s)
    (match s
      [`((begin ,ss ...)) ss]
      [_ s]))

  (define (select-instructions-effect effect)
    (match effect 
      [`(set! ,aloc ,value)
        #:when (and (aloc? aloc) (value? value))
        (cond
          [(triv? value) (list effect)]
          [else (match value
                  [`(,op ,triv1 ,triv2)
                    (if (or (eq? aloc triv1) (number? triv1)) 
                      `((set! ,aloc ,triv1) (set! ,aloc (,op ,aloc ,triv2)))
                      (let-values ([(tmp instructions) (select-instructions-binop value)])
                        `((begin ,@instructions (set! ,aloc ,tmp)))))]
                  [_ (error "invalid Imp-cmf-lang v4 value in select-instructions" value)])])]
      [`(begin ,effects ... ,effect)
        `((begin
          ,@(unwrap-begin (select-instructions-effects effects))
          ,@(unwrap-begin (select-instructions-effect effect))))]
      [`(if ,pred ,effect-consequent ,effect-alternative)
        `((if
          ,@(select-instructions-pred pred)
          ,@(select-instructions-effect effect-consequent)
          ,@(select-instructions-effect effect-alternative)))]
      [_ (error "invalid Imp-cmf-lang v4 effect in select-instructions" effect)]))

  (define (select-instructions-pred pred)
    (match pred
      [`(,op ,triv1 ,triv2)
        #:when (and (relop? op) (triv? triv1) (triv? triv2))
        (if (int64? triv1)
          (let ([tmp (fresh)])
            `((begin (set! ,tmp ,triv1) (,op ,tmp ,triv2))))
          (list pred))]
      [`(true)
        (list pred)]
      [`(false)
        (list pred)]
      [`(not ,inner-pred)
        `((not ,@(select-instructions-pred inner-pred)))]
      [`(begin ,effects ... ,inner-pred)
        `((begin 
          ,@(unwrap-begin (select-instructions-effects effects))
          ,@(unwrap-begin (select-instructions-pred inner-pred))))]
      [`(if ,inner-pred ,inner-pred-consequent ,inner-pred-alternative)
        `((if 
          ,@(select-instructions-pred inner-pred) 
          ,@(select-instructions-pred inner-pred-consequent) 
          ,@(select-instructions-pred inner-pred-alternative)))]
      [_ (error "invalid Imp-cmf-lang v4 pred in select-instructions" pred)]))

  (define (select-instructions-effects effects)
    (append-map select-instructions-effect effects))

  (define (select-instructions-binop op)
    (match op
      [`(,op ,triv1 ,triv2)
        #:when (and (binop? op) (triv? triv1) (triv? triv2))
        (let ([tmp (fresh)])
          (values tmp `((set! ,tmp ,triv1) (set! ,tmp (,op ,tmp ,triv2)))))]
      [_ (error "invalid Imp-cmf-lang v4 binop in select-instructions" op)]))

  (define (select-instructions-tail tail)
    (match tail
      [`,value
        #:when (value? value)
        (if (triv? value)
          `((halt ,value))
          (let-values ([(tmp instructions) (select-instructions-binop value)])
            `((begin ,@instructions (halt ,tmp)))))]
      [`(begin ,effects ... ,tail)
        `((begin 
          ,@(unwrap-begin (select-instructions-effects effects)) 
          ,@(unwrap-begin (select-instructions-tail tail))))]
      [`(if ,pred ,tail-consequent ,tail-alternative)
        `((if 
          ,@(select-instructions-pred pred) 
          ,@(select-instructions-tail tail-consequent) 
          ,@(select-instructions-tail tail-alternative)))]
      [_ (error "invalid Imp-cmf-lang v4 tail in select-instructions" tail)]))

  (match p
    [`(module ,tail)
      `(module () ,@(select-instructions-tail tail))]
    [_ (error "invalid Imp-cmf-lang v4 module in select-instructions" p)]))

(define (canonicalize-bind p)
  (define (triv? x) (or (int64? x) (aloc? x)))

  (define (canonicalize-bind-pred pred)
    (match pred
      [`(,op ,triv1 ,triv2)
        #:when (and (relop? op) (triv? triv1) (triv? triv2))
        pred]
      [`(true)
        pred]
      [`(false)
        pred]
      [`(not ,inner-pred)
        `(not ,(canonicalize-bind-pred inner-pred))]
      [`(begin ,effects ... ,inner-pred)
        `(begin ,(canonicalize-bind-effects effects) ,(canonicalize-bind-pred inner-pred))]
      [`(if ,inner-pred ,inner-pred-consequent ,inner-pred-alternative)
        `(if 
          ,(canonicalize-bind-pred inner-pred)
          ,(canonicalize-bind-pred inner-pred-consequent)
          ,(canonicalize-bind-pred inner-pred-alternative))]
      [_ (error "invalid Imp-mf-lang v4 pred in canonicalize-bind" pred)]))

  (define (canonicalize-bind-effect effect)
    (match effect
      [`(set! ,aloc ,value)
        #:when (aloc? aloc)
        (match value
          [`(begin ,effects ... ,inner-value)
            `(begin 
              ,@(canonicalize-bind-effects effects)
              ,(canonicalize-bind-effect `(set! ,aloc ,inner-value)))]
          [`(if ,pred ,value-consequent ,value-alternative)
            `(if ,pred 
              ,(canonicalize-bind-effect `(set! ,aloc ,value-consequent))
              ,(canonicalize-bind-effect `(set! ,aloc ,value-alternative)))]
          [_ effect])]
      [`(if ,pred ,effect-consequent ,effect-alternative)
        `(if 
          ,(canonicalize-bind-pred pred)
          ,(canonicalize-bind-effect effect-consequent)
          ,(canonicalize-bind-effect effect-alternative))]
      [`(begin ,effects ... ,effect)
        `(begin ,@(canonicalize-bind-effects effects) ,(canonicalize-bind-effect effect))]
      [_ (error "invalid Imp-mf-lang v4 effect in canonicalize-bind" effect)]))

  (define (canonicalize-bind-effects effects)
    (map canonicalize-bind-effect effects))

  (define (canonicalize-bind-value value)
    (match value
      [`(,op ,triv1 ,triv2)
        #:when (and (binop? op) (triv? triv1) (triv? triv2))
        value]
      [`(if ,pred ,value-consequent ,value-alternative)
        `(if 
          ,(canonicalize-bind-pred pred) 
          ,(canonicalize-bind-value value-consequent) 
          ,(canonicalize-bind-value value-alternative))]
      [`(begin ,effects ... ,inner-value)
        `(begin ,@(canonicalize-bind-effects effects) ,(canonicalize-bind-value inner-value))]
      [`,triv
        #:when (triv? triv)
        value]
      [_ (error "invalid Imp-mf-lang v4 value in canonicalize-bind" value)]))

  (define (canonicalize-bind-tail tail)
    (match tail
      [`(begin ,effects ... ,value)
        `(begin ,@(canonicalize-bind-effects effects) ,(canonicalize-bind-value value))]
      [`(if ,pred ,tail-consequent ,tail-alternative)
        `(if 
          ,(canonicalize-bind-pred pred) 
          ,(canonicalize-bind-tail tail-consequent)
          ,(canonicalize-bind-tail tail-alternative))]
      [`,value
        (canonicalize-bind-value value)]
      [_ (error "invalid Imp-mf-lang v4 tail in canonicalize-bind" tail)]))

  (match p
    [`(module ,tail)
      `(module ,(canonicalize-bind-tail tail))]
    [_ (error "invalid Imp-mf-lang v4 module in canonicalize-bind" p)]))

(define (sequentialize-let p)
  (define (triv? x) (or (int64? x) (aloc? x)))

  (define (bindings->set!-instructions bindings)
    (foldr
      (lambda (instr accu)
        (let ([aloc (first instr)]
              [val (second instr)])
          (cons `(set! ,aloc ,(sequentialize-let-value val)) accu)))
      '()
      bindings))

  (define (sequentialize-let-value value)
    (match value
      [`,triv
        #:when (triv? triv)
        value]
      [`(,op ,triv1 ,triv2)
        #:when (and (binop? op) (triv? triv1) (triv? triv2))
        value]
      [`(let (,bindings ...) ,inner-value)
        `(begin ,@(bindings->set!-instructions bindings) ,(sequentialize-let-value inner-value))]
      [`(if ,pred ,value-consequent ,value-alternative)
        `(if 
          ,(sequentialize-let-pred pred) 
          ,(sequentialize-let-value value-consequent)
          ,(sequentialize-let-value value-alternative))]
      [_ (error "invalid Values-unique-lang v4 value in sequentialize-let" value)]))

  (define (sequentialize-let-pred pred)
    (match pred
      [`(,op ,triv1 ,triv2)
        #:when (and (relop? op) (triv? triv1) (triv? triv2))
        pred]
      [`(true)
        pred]
      [`(false)
        pred]
      [`(not ,inner-pred)
        `(not ,(sequentialize-let-pred inner-pred))]
      [`(let (,bindings ...) ,inner-pred)
        `(begin ,@(bindings->set!-instructions bindings) ,(sequentialize-let-pred inner-pred))]
      [`(if ,inner-pred ,inner-pred-consequent ,inner-pred-alternative)
        `(if 
          ,(sequentialize-let-pred inner-pred)
          ,(sequentialize-let-pred inner-pred-consequent)
          ,(sequentialize-let-pred inner-pred-alternative))]
      [_ (error "invalid Values-unique-lang v4 pred in sequentialize-let" pred)]))

  (define (sequentialize-let-tail tail)
    (match tail
      [`(let (,bindings ...) ,tail)
        `(begin ,@(bindings->set!-instructions bindings) ,(sequentialize-let-tail tail))]
      [`(if ,pred ,tail-consequent ,tail-alternative)
        `(if
          ,(sequentialize-let-pred pred)
          ,(sequentialize-let-tail tail-consequent)
          ,(sequentialize-let-tail tail-alternative))]
      [`,value
        (sequentialize-let-value value)]
      [_ (error "invalid Values-unique-lang v4 tail in sequentialize-let" tail)]))

  (match p
    [`(module ,tail)
      `(module ,(sequentialize-let-tail tail))]
    [_ (error "invalid Values-unique-lang v4 module in sequentialize-let" p)]))

(define (uniquify p)
  (define (triv? x) (or (int64? x) (name? x)))

  (define ids (make-hash))

  (define (uniquify-bindings bindings)
    (foldr
      (lambda (binding accu)
        (let* ([key (first binding)]
               [frsh (fresh key)]) 
          (dict-set! ids key frsh)
          (cons `(,frsh ,(second binding)) accu)))
      '()
      bindings))

  (define (uniquify-triv triv)
    (cond
      [(int64? triv) triv]
      [(name? triv) (dict-ref ids triv)]
      [else (error "invalid triv" triv)]))

  (define (uniquify-pred pred)
    (match pred
      [`(,op ,triv1 ,triv2)
        #:when (and (relop? op) (triv? triv1) (triv? triv2))
        `(,op ,(uniquify-triv triv1) ,(uniquify-triv triv2))]
      [`(true)
        pred]
      [`(false)
        pred]
      [`(not ,inner-pred)
        `(not ,(uniquify-pred inner-pred))]
      [`(let (,bindings ...) ,inner-pred)
        `(let ,(uniquify-bindings bindings) ,(uniquify-pred inner-pred))]
      [`(if ,inner-pred ,inner-pred-consequent ,inner-pred-alternative)
        `(if 
          ,(uniquify-pred inner-pred)
          ,(uniquify-pred inner-pred-consequent)
          ,(uniquify-pred inner-pred-alternative))]
      [_ (error "invalid Values-lang v4 pred in uniquify" pred)]))

  (define (uniquify-value value)
    (match value
      [`(,op ,triv1 ,triv2)
        #:when (and (binop? op) (triv? triv1) (triv? triv2))
        `(,op ,(uniquify-triv triv1) ,(uniquify-triv triv2))]
      [`(let (,bindings ...) ,inner-value)
        `(let ,(uniquify-bindings bindings) ,(uniquify-value inner-value))]
      [`(if ,pred ,value-consequent ,value-alternative)
        `(if 
          ,(uniquify-pred pred) 
          ,(uniquify-value value-consequent)
          ,(uniquify-value value-alternative))]
      [`,triv
        #:when (triv? triv)
        (uniquify-triv triv)]
      [_ (error "invalid Values-lang v4 value in uniquify" value)]))

  (define (uniquify-tail tail)
    (match tail
      [`(let (,bindings ...) ,inner-tail)
        `(let ,(uniquify-bindings bindings) ,(uniquify-tail inner-tail))]
      [`(if ,pred ,tail-consequent ,tail-alternative)
        `(if
          ,(uniquify-pred pred)
          ,(uniquify-tail tail-consequent)
          ,(uniquify-tail tail-alternative))]
      [`,value
        (uniquify-value value)]
      [_ (error "invalid Values-lang v4 tail in uniquify" tail)]))

  (match p
    [`(module ,tail)
      `(module ,(uniquify-tail tail))]
    [_ (error "invalid Values-lang v4 module in uniquify" p)]))

(define (interp-values-lang p)
  (define (triv? x) (or (int64? x) (name? x)))

  (define (interp-values-lang-triv triv env)
    (if (name? triv)
      (dict-ref env triv)
      triv))

  (define (interp-values-lang-bindings bindings env)
    (for-each
      (lambda (binding)
        (let ([varname (first binding)]
              [val (interp-values-lang-value (second binding) env)])
          (dict-set! env varname val)))
      bindings))

  (define (interp-values-lang-value val env)
    (match val
      [`(if ,pred ,value-consequent ,value-alternative)
        (if (interp-values-lang-pred pred env)
          (interp-values-lang-value value-consequent env)
          (interp-values-lang-value value-alternative env))]
      [`(let (,bindings ...) ,value)
        (begin
          (interp-values-lang-bindings bindings env)
          (interp-values-lang-value value env))]
      [`(,op ,triv1 ,triv2)
        #:when (and (binop? op) (triv? triv1) (triv? triv2))
          ((binop->proc op) (interp-values-lang-triv triv1 env) (interp-values-lang-triv triv2 env))]
      [`,triv
        #:when (triv? triv)
          (interp-values-lang-triv triv env)]
      [_ (error "invalid Values-lang v4 value in interp-values-lang (value)" val)]))

  (define (interp-values-lang-pred pred env)
    (match pred
      [`(,op ,triv1 ,triv2)
        #:when (and (relop? op) (triv? triv1) (triv? triv2))
        ((relop->proc op) (interp-values-lang-triv triv1 env) (interp-values-lang-triv triv2 env))]
      [`(true)
        #t]
      [`(false)
        #f]
      [`(not ,inner-pred)
        (not (interp-values-lang-pred inner-pred))]
      [`(let (,bindings ...) ,inner-pred)
        (begin
          (interp-values-lang-bindings bindings env)
          (interp-values-lang-pred inner-pred env))]
      [`(if ,inner-pred ,inner-pred-consequent ,inner-pred-alternative)
        (if (interp-values-lang-pred inner-pred env)
          (interp-values-lang-pred inner-pred-consequent env)
          (interp-values-lang-pred inner-pred-alternative env))]
      [_ (error "invalid Values-lang v4 pred in interp-values-lang (pred)" pred)]))

  (define (interp-values-lang-tail tail env)
    (match tail
      [`(if ,pred ,tail-consequent ,tail-alternative)
        (if (interp-values-lang-pred pred env)
          (interp-values-lang-tail tail-consequent env)
          (interp-values-lang-tail tail-alternative env))]
      [`(let (,bindings ...) ,tail)
        (begin
          (interp-values-lang-bindings bindings env)
          (interp-values-lang-tail tail env))]
      [`,value 
        (interp-values-lang-value value env)]
      [_ (error "invalid Values-lang v4 tail in interp-values-lang (tail)" tail)]))

  (match p 
    [`(module ,tail) 
      (modulo (interp-values-lang-tail tail (make-hash)) 256)]
    [_ (error "invalid Values-lang v4 module in interp-values-lang" p)]))
