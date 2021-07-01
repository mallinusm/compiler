#lang racket

(require 
  cpsc411/compiler-lib 
  "compiler.rkt")

(module+ test
  (require
   	rackunit
   	rackunit/text-ui
   	cpsc411/test-suite/public/a1)

  ; tests for generate-x64
  (check-equal? (generate-x64 '(begin (set! rax 42))) "mov rax, 42\n")
  (check-equal? 
    (generate-x64 '(begin (set! rax 0) (set! rax (+ rax 42)))) 
    "mov rax, 0\nadd rax, 42\n")
  (check-equal?
    (generate-x64
      '(begin
          (set! rax 170679)
          (set! rdi rax)
          (set! rdi (+ rdi rdi))
          (set! rsp rdi)
          (set! rsp (* rsp rsp))
          (set! rbx 8991)))
    "mov rax, 170679\nmov rdi, rax\nadd rdi, rdi\nmov rsp, rdi\nimul rsp, rsp\nmov rbx, 8991\n")
  (check-equal? 
    (generate-x64 
      '(begin
        (set! (rbp - 0) 0)
        (set! (rbp - 8) 42)
        (set! rax (rbp - 0))
        (set! rax (+ rax (rbp - 8)))))
    "mov QWORD [rbp - 0], 0\nmov QWORD [rbp - 8], 42\nmov rax, QWORD [rbp - 0]\nadd rax, QWORD [rbp - 8]\n")
  (check-exn 
    #rx"unable to generate x64" 
    (thunk (generate-x64 '(begin (set! (rbp - 1) 0))))) ; invalid offset
  (check-exn 
    #rx"unable to generate x64" 
    (thunk (generate-x64 '(begin (set! (rax - 0) 0))))) ; invalid frame base pointer register
  ; v4
  (check-equal? (generate-x64 '(begin (set! (rbp - 0) L.test.1))) "mov QWORD [rbp - 0], L.test.1\n") 
  (check-equal? (generate-x64 '(begin (with-label L.test.1 (set! rax 0)))) "L.test.1:\nmov rax, 0\n") 
  (check-equal? (generate-x64 '(begin (jump rax))) "jmp rax\n")
  (check-equal? (generate-x64 '(begin (compare rax rbx))) "cmp rax, rbx\n")
  (check-equal? (generate-x64 '(begin (jump-if = L.test.1))) "je L.test.1\n")
  (check-equal? (generate-x64 '(begin (jump-if < L.test.1))) "jl L.test.1\n")

  ; tests for link-paren
  (check-equal? (link-paren-x64 '(begin (with-label L.test.1 (set! (rbp - 0) L.test.1)))) '(begin (set! (rbp - 0) 0)))
  (check-equal? (link-paren-x64 '(begin (with-label L.test.1 (set! rax L.test.1)))) '(begin (set! rax 0)))
  (check-equal? (link-paren-x64 '(begin (with-label L.test.1 (jump L.test.1)))) '(begin (jump 0)))
  (check-equal? (link-paren-x64 '(begin (with-label L.test.1 (jump-if = L.test.1)))) '(begin (jump-if = 0)))
  (check-equal? (link-paren-x64 '(begin (set! rax 1) (with-label L.test.1 (jump L.test.1)))) '(begin (set! rax 1) (jump 1))) ; pc = 1
  ; forward jump
  (check-equal? 
    (link-paren-x64 '(begin (jump L.test.1) (with-label L.test.1 (set! rax 42)))) 
    '(begin (jump 1) (set! rax 42)))
  
  ; tests for interp-paren-x64
  (check-equal? 
    (interp-paren-x64 '(begin (set! rax 42)))
    42)
  (check-equal? 
    (interp-paren-x64 '(begin (set! rax 42) (set! rax (+ rax 0))))
    42)
  (check-equal?
    (interp-paren-x64
      '(begin
        (set! (rbp - 0) 0)
        (set! (rbp - 8) 42)
        (set! rax (rbp - 0))
        (set! rax (+ rax (rbp - 8)))))
    42)
  (check-equal?
    (interp-paren-x64
      '(begin
        (set! rax 0)
        (set! rbx 0)
        (set! r9 42)
        (set! rax (+ rax r9))))
    42)
  (check-equal?
    (interp-paren-x64
      '(begin
        (set! (rbp - 0) 42)
        (set! rax (rbp - 0))))
    42)
  ; v4
  (check-equal? 
    (interp-paren-x64 
      '(begin 
        (set! rax 0)
        (with-label L.loop.1 (set! rax (+ rax 1))) ; L.loop.1 should be linked 
        (compare rax 10)
        (jump-if != L.loop.1)))
    10)

  ; tests for implement-fvars
  (check-equal? 
    (implement-fvars '(begin (set! fv0 42)))
    '(begin (set! (rbp - 0) 42)))
  (check-equal? 
    (implement-fvars '(begin (set! fv0 rax)))
    '(begin (set! (rbp - 0) rax)))
  (check-equal? 
    (implement-fvars '(begin (set! rax fv0)))
    '(begin (set! rax (rbp - 0))))
  (check-equal? 
    (implement-fvars '(begin (set! rax rax)))
    '(begin (set! rax rax)))
  (check-equal? 
    (implement-fvars '(begin (set! rax 4294967296))) ; (set! reg triv) where triv can be int64
    '(begin (set! rax 4294967296)))
  (check-equal? 
    (implement-fvars '(begin (set! fv0 42) (set! rax fv0)))
    '(begin (set! (rbp - 0) 42) (set! rax (rbp - 0))))
  (check-equal? ; same but with index offset
    (implement-fvars '(begin (set! fv1 42) (set! rax fv1)))
    '(begin (set! (rbp - 8) 42) (set! rax (rbp - 8))))
  (check-equal? 
    (implement-fvars '(begin (set! fv0 42) (set! rax (+ rax fv0))))
    '(begin (set! (rbp - 0) 42) (set! rax (+ rax (rbp - 0)))))
  (check-equal? ; same but with index offset
    (implement-fvars '(begin (set! fv1 42) (set! rax (+ rax fv1))))
    '(begin (set! (rbp - 8) 42) (set! rax (+ rax (rbp - 8)))))
  ; value needs to be int32
  (check-exn 
    #rx"invalid Paren-x64-fvars v4 statement in implement-fvars" 
    (thunk (implement-fvars '(begin (set! fv0 4294967296)))))
  ; v4
  (check-equal? 
    (implement-fvars '(begin (with-label L.test.1 (set! fv0 42))))
    '(begin (with-label L.test.1 (set! (rbp - 0) 42))))

  ; tests for patch-instructions
  (check-equal? 
    (patch-instructions '(begin (set! rbx 42) (halt rbx)))
    '(begin (set! rbx 42) (set! rax rbx))) ; make sure halt is compiled
  (check-equal? 
    (patch-instructions '(begin (set! fv0 fv1)))
    '(begin (set! r10 fv1) (set! fv0 r10)))
  (check-equal? 
    (patch-instructions 
      '(begin 
        (set! fv0 4294967296) 
        (set! fv0 (+ fv0 1)) 
        (halt fv1)))
    '(begin 
      (set! r10 4294967296)
      (set! fv0 r10)
      (set! r10 fv0)
      (set! r10 (+ r10 1))
      (set! fv0 r10)
      (set! rax fv1)))
  (check-equal? 
    (patch-instructions 
      '(begin 
        (set! fv0 0) 
        (set! fv1 42) 
        (set! fv0 fv1) 
        (halt fv0)))
    '(begin 
      (set! fv0 0) 
      (set! fv1 42) 
      (set! r10 fv1) 
      (set! fv0 r10) 
      (set! rax fv0))) ; make sure fv0 fv1 is compiled to 2 seperate set! statements
  (check-equal? 
    (patch-instructions 
      '(begin 
        (set! rbx 0) 
        (set! rcx 0) 
        (set! r9 42) 
        (set! rbx rcx) 
        (set! rbx (+ rbx r9)) 
        (halt rbx)))
    '(begin 
      (set! rbx 0) 
      (set! rcx 0) 
      (set! r9 42) 
      (set! rbx rcx) 
      (set! rbx (+ rbx r9)) 
      (set! rax rbx)))
  ; v4
  (check-equal? 
    (patch-instructions '(begin (with-label L.test.1 (set! fv0 fv1))))
    '(begin (with-label L.test.1 (set! r10 fv1)) (set! fv0 r10)))
  (check-equal? 
    (patch-instructions '(begin (with-label L.test.1 (halt rbx))))
    '(begin (with-label L.test.1 (set! rax rbx))))
  (check-equal? 
    (patch-instructions '(begin (compare fv0 42)))
    '(begin (set! r10 fv0) (compare r10 42)))
  (check-equal? ; negate the relop and want jump *over* the following jump instruction
    (patch-instructions '(begin (jump-if = rax) (set! rax 0) (set! rax 1)))
    '(begin
      (jump-if != L.tmp.1)
      (jump rax)
      (with-label L.tmp.1 (set! r10 r10))
      (set! rax 0)
      (set! rax 1)))
  ; also jump needs patching in case of fvar
  (check-equal?
    (patch-instructions '(begin (jump fv0) (set! rax 0) (set! rax 1)))
    '(begin (set! r10 fv0) (jump r10) (set! rax 0) (set! rax 1)))

  ; tests for flatten-program
  (check-equal? 
    (flatten-program '(module (define L.test.1 (halt 42))))
    '(begin (with-label L.test.1 (halt 42))))
  (check-equal? 
    (flatten-program 
      '(module 
        (define L.test.1 
          (begin 
            (set! rax L.test.1)
            (jump rax)))))
    '(begin (with-label L.test.1 (set! rax L.test.1)) (jump rax)))
  (check-equal? 
    (flatten-program 
      '(module 
        (define L.test.1 (jump L.test.1))
        (define L.test.2 (jump L.test.2))))
    '(begin (with-label L.test.1 (jump L.test.1)) (with-label L.test.2 (jump L.test.2))))
  (check-equal? 
    (flatten-program 
      '(module (define L.test.1 (begin (begin (halt rax))))))
    '(begin (with-label L.test.1 (halt rax))))
  (check-equal? 
    (flatten-program 
      '(module  
        (define L.setup.0 (begin (set! rax 1) (jump L.test.1)))
        (define L.test.1 (begin (set! rax (+ rax 1)) (if (= rax 42) (jump L.test.2) (jump L.test.1))))
        (define L.test.2 (halt rax))))
    '(begin 
      (with-label L.setup.0 (set! rax 1))
      (jump L.test.1)
      (with-label L.test.1 (set! rax (+ rax 1)))
      (compare rax 42)
      (jump-if = L.test.2)
      (jump L.test.1)
      (with-label L.test.2 (halt rax))))

  ; test for resolve-predicates
  (check-equal? 
    (resolve-predicates
      '(module (define L.test.1 (if (> rax rbx) (jump L.branch.1) (jump L.branch.2)))))
    '(module (define L.test.1 (if (> rax rbx) (jump L.branch.1) (jump L.branch.2)))))
  (check-equal? 
    (resolve-predicates
      '(module (define L.test.1 (if (true) (jump L.branch.1) (jump L.branch.2)))))
    '(module (define L.test.1 (jump L.branch.1))))
  (check-equal? 
    (resolve-predicates
      '(module (define L.test.1 (if (false) (jump L.branch.1) (jump L.branch.2)))))
    '(module (define L.test.1 (jump L.branch.2))))
  (check-equal? 
    (resolve-predicates
      '(module (define L.test.1 (if (not (false)) (jump L.branch.1) (jump L.branch.2)))))
    '(module (define L.test.1 (jump L.branch.1))))
  (check-equal? 
    (resolve-predicates
      '(module (define L.test.1 (if (not (= rax rbx)) (jump L.branch.1) (jump L.branch.2)))))
    '(module (define L.test.1 (if (= rax rbx) (jump L.branch.2) (jump L.branch.1)))))

  ; tests for expose-basic-blocks
  (check-equal? 
    (expose-basic-blocks '(module (halt rax)))
    '(module (define L.tmp.2 (halt rax))))
  (check-equal? 
    (expose-basic-blocks
      '(module (if (= rax rbx) (halt rax) (halt rbx))))
    '(module
      (define L.tmp.5 (if (= rax rbx) (jump L.tmp.3) (jump L.tmp.4)))
      (define L.tmp.3 (halt rax))
      (define L.tmp.4 (halt rbx))))
  (check-equal?
    (expose-basic-blocks
      '(module (begin (set! rax 1) (halt rax))))
    '(module (define L.tmp.6 (begin (set! rax 1) (halt rax)))))
  (check-equal?
    (expose-basic-blocks
      '(module (begin (set! rax 1) (if (true) (halt 1) (halt 0)))))
    '(module
      (define L.tmp.9
        (begin (set! rax 1) (if (true) (jump L.tmp.7) (jump L.tmp.8))))
      (define L.tmp.7 (halt 1))
      (define L.tmp.8 (halt 0))))
  (check-equal? 
    (expose-basic-blocks
      '(module (if (not (true)) (halt rax) (halt rbx))))
    '(module
      (define L.tmp.12 (if (true) (jump L.tmp.11) (jump L.tmp.10)))
      (define L.tmp.10 (halt rax))
      (define L.tmp.11 (halt rbx))))
  (check-equal?
    (expose-basic-blocks
      '(module (if (if (true) (true) (false)) (halt rax) (halt rbx))))
    '(module
      (define L.tmp.17 (if (true) (jump L.tmp.15) (jump L.tmp.16)))
      (define L.tmp.15 (if (true) (jump L.tmp.13) (jump L.tmp.14)))
      (define L.tmp.16 (if (false) (jump L.tmp.13) (jump L.tmp.14)))
      (define L.tmp.13 (halt rax))
      (define L.tmp.14 (halt rbx))))
  (check-equal?
    (expose-basic-blocks
      '(module (if (if (if (true) (true) (false)) (true) (false)) (halt rax) (halt rbx))))
    '(module
      (define L.tmp.24 (if (true) (jump L.tmp.22) (jump L.tmp.23)))
      (define L.tmp.22 (if (true) (jump L.tmp.20) (jump L.tmp.21)))
      (define L.tmp.23 (if (false) (jump L.tmp.20) (jump L.tmp.21)))
      (define L.tmp.20 (if (true) (jump L.tmp.18) (jump L.tmp.19)))
      (define L.tmp.21 (if (false) (jump L.tmp.18) (jump L.tmp.19)))
      (define L.tmp.18 (halt rax))
      (define L.tmp.19 (halt rbx))))
  (check-equal?
    (expose-basic-blocks 
      '(module (begin (set! rax 1) (halt rax))))
    '(module (define L.tmp.25 (begin (set! rax 1) (halt rax)))))
  (check-equal?
    (expose-basic-blocks 
      '(module (begin (set! rax 1) (set! rax (+ rax 1)) (halt rax))))
    '(module (define L.tmp.26 (begin (set! rax 1) (set! rax (+ rax 1)) (halt rax)))))
  (check-equal?
    (expose-basic-blocks
      '(module (begin (begin (set! rax 1) (set! rax (+ rax 1))) (halt rax))))
    '(module (define L.tmp.27 (begin (set! rax 1) (set! rax (+ rax 1)) (halt rax)))))
  (check-equal?
    (expose-basic-blocks
      '(module (if (begin (true)) (halt rax) (halt rbx))))
    '(module
      (define L.tmp.30 (if (true) (jump L.tmp.28) (jump L.tmp.29)))
      (define L.tmp.28 (halt rax))
      (define L.tmp.29 (halt rbx))))
  (check-equal?
    (expose-basic-blocks
      '(module (if (begin (set! rax 1) (true)) (halt rax) (halt rbx))))
    '(module
      (define L.tmp.33
        (begin (set! rax 1) (if (true) (jump L.tmp.31) (jump L.tmp.32))))
      (define L.tmp.31 (halt rax))
      (define L.tmp.32 (halt rbx))))

  ; tests for assign-homes-opt
  (check-equal?
    (replace-locations
      '(module ((assignment ((x.1 r15)))) (halt x.1)))
    '(module () (halt r15)))
  (check-equal?
    (replace-locations
      '(module ((assignment ((x.1 r15)))) (begin (set! x.1 1) (halt x.1))))
    '(module () (begin (set! r15 1) (halt r15))))
  (check-equal?
    (replace-locations
      '(module ((assignment ((x.1 r15) (x.2 r14)))) (begin (set! x.1 1) (set! x.2 x.1) (halt x.2))))
    '(module () (begin (set! r15 1) (set! r14 r15) (halt r14))))
  (check-equal?
    (replace-locations
      '(module ((assignment ((x.1 r15)))) (begin (set! x.1 1) (set! x.1 (+ x.1 1)) (halt x.1))))
    '(module () (begin (set! r15 1) (set! r15 (+ r15 1)) (halt r15))))
  (check-equal?
    (replace-locations
      '(module ((assignment ((x.1 r15) (x.2 r14)))) (begin (set! x.1 1) (set! x.2 1) (set! x.1 (+ x.1 x.2)) (halt x.1))))
    '(module () (begin (set! r15 1) (set! r14 1) (set! r15 (+ r15 r14)) (halt r15))))
  ; v4
  (check-equal?
    (replace-locations
      '(module ((assignment ((x.1 r15) (x.2 r14)))) (if (true) (halt x.1) (halt x.2))))
    '(module () (if (true) (halt r15) (halt r14))))
  (check-equal?
    (replace-locations
      '(module ((assignment ((x.1 r15) (x.2 r14)))) (if (> x.1 x.2) (halt x.1) (halt x.2))))
    '(module () (if (> r15 r14) (halt r15) (halt r14))))
  (check-equal?
    (replace-locations
      '(module ((assignment ((x.1 r15) (x.2 r14)))) (if (not (> x.1 x.2)) (halt x.1) (halt x.2))))
    '(module () (if (not (> r15 r14)) (halt r15) (halt r14))))
  (check-equal?
    (replace-locations
      '(module ((assignment ((x.1 r15) (x.2 r14)))) (if (begin (set! x.1 1) (not (> x.1 x.2))) (halt x.1) (halt x.2))))
    '(module () (if (begin (set! r15 1) (not (> r15 r14))) (halt r15) (halt r14))))
  (check-equal?
    (replace-locations
      '(module ((assignment ((x.1 r15) (x.2 r14)))) (if (if (true) (false) (true)) (halt x.1) (halt x.2))))
    '(module () (if (if (true) (false) (true)) (halt r15) (halt r14))))

  ; tests for uncover-locals
  (check-equal? 
    (uncover-locals
      '(module ()
        (begin
          (set! x.1 0)
          (halt x.1))))
    '(module ((locals (x.1))) (begin (set! x.1 0) (halt x.1))))
  (check-equal?
    (uncover-locals
      '(module ()
        (begin
          (set! x.1 0)
          (set! y.1 x.1)
          (set! y.1 (+ y.1 x.1))
          (halt y.1))))
    '(module 
      ((locals (y.1 x.1))) 
      (begin (set! x.1 0) (set! y.1 x.1) (set! y.1 (+ y.1 x.1)) (halt y.1))))
  ; v4
  (check-equal? 
    (uncover-locals
      '(module ()
        (if (true) (halt x.1) (halt x.2))))
    '(module ((locals (x.1 x.2))) (if (true) (halt x.1) (halt x.2))))
  (check-equal? 
    (uncover-locals
      '(module ()
        (begin 
          (set! a.1 42) 
          (if (= b.1 10)
            (set! c.1 (+ c.1 b.1))
            (set! d.1 (+ d.1 b.1)))
          (halt a.1))))
    '(module 
      ((locals (b.1 c.1 d.1 a.1)))
      (begin 
        (set! a.1 42) 
        (if (= b.1 10)
          (set! c.1 (+ c.1 b.1))
          (set! d.1 (+ d.1 b.1)))
        (halt a.1))))

  ; tests for undead-analysis
  (check-equal? 
    (undead-analysis 
      '(module ((locals (x.1)))
        (begin
          (set! x.1 42)
          (halt x.1))))
    '(module
      ((locals (x.1)) (undead-out ((x.1) ())))
      (begin (set! x.1 42) (halt x.1))))
  (check-equal? 
    (undead-analysis 
      '(module ((locals (v.1 w.2 x.3 y.4 z.5 t.6 p.1)))
        (begin
          (set! v.1 1)
          (set! w.2 46)
          (set! x.3 v.1)
          (set! p.1 7)
          (set! x.3 (+ x.3 p.1))
          (set! y.4 x.3)
          (set! p.1 4)
          (set! y.4 (+ y.4 p.1))
          (set! z.5 x.3)
          (set! z.5 (+ z.5 w.2))
          (set! t.6 y.4)
          (set! p.1 -1)
          (set! t.6 (* t.6 p.1))
          (set! z.5 (+ z.5 t.6))
          (halt z.5))))
    '(module 
        ((locals (v.1 w.2 x.3 y.4 z.5 t.6 p.1))
        (undead-out ((v.1)
          (v.1 w.2)
          (w.2 x.3)
          (p.1 w.2 x.3)
          (w.2 x.3)
          (w.2 x.3 y.4)
          (p.1 w.2 x.3 y.4)
          (w.2 x.3 y.4)
          (w.2 y.4 z.5)
          (y.4 z.5)
          (t.6 z.5)
          (p.1 t.6 z.5)
          (t.6 z.5)
          (z.5) 
          ())))
        (begin
          (set! v.1 1)
          (set! w.2 46)
          (set! x.3 v.1)
          (set! p.1 7)
          (set! x.3 (+ x.3 p.1))
          (set! y.4 x.3)
          (set! p.1 4)
          (set! y.4 (+ y.4 p.1))
          (set! z.5 x.3)
          (set! z.5 (+ z.5 w.2)) ; ...
          (set! t.6 y.4) ; (z.5 t.6) - (t.6) + (y.4)
          (set! p.1 -1) ; (z.5 t.6 p.1) - (p.1) + () : (z.5 t.6)
          (set! t.6 (* t.6 p.1)) ; (z.5 t.6) - (t.6) + (t.6 p.1) : (z.5 t.6 p.1)
          (set! z.5 (+ z.5 t.6)) ; (z.5) - (z.5) + (z.5 t.6) : (z.5 t.6)
          (halt z.5)))) ; () - () + (z.5)
  ; tests undead-analysis (checking unused vars)
  (check-equal? 
    (undead-analysis 
      '(module ((locals (x.1 y.1)))
        (begin (set! y.1 42) (set! x.1 5) (halt x.1))))
    '(module ((locals (x.1 y.1)) (undead-out (() (x.1) ())))
      (begin (set! y.1 42) (set! x.1 5) (halt x.1))))
  (check-equal? 
    (undead-analysis 
      '(module ((locals (x.1 y.1)))
        (begin (set! x.1 5) (set! y.1 42) (halt x.1))))
    '(module
      ((locals (x.1 y.1)) (undead-out ((x.1) (x.1) ())))
      (begin (set! x.1 5) (set! y.1 42) (halt x.1))))
  
  ; tests conflict-analysis
  (check-equal? 
    (conflict-analysis 
      '(module ((locals (x.1))
             (undead-out ((x.1) ())))
        (begin
          (set! x.1 42)
          (halt x.1))))
    '(module
      ((locals (x.1)) (conflicts ((x.1 ()))))
      (begin (set! x.1 42) (halt x.1))))
  (check-equal? 
    (conflict-analysis 
      '(module 
          ((locals (v.1 w.2 x.3 y.4 z.5 t.6 p.1))
          (undead-out ((v.1) (v.1 w.2) (w.2 x.3) (p.1 w.2 x.3) 
            (w.2 x.3) (y.4 w.2 x.3) (p.1 y.4 w.2 x.3) (y.4 w.2 x.3)
            (z.5 y.4 w.2) (z.5 y.4) (t.6 z.5) (t.6 z.5 p.1)
            (t.6 z.5) (z.5) ())))
          (begin
            (set! v.1 1)
            (set! w.2 46)
            (set! x.3 v.1)
            (set! p.1 7)
            (set! x.3 (+ x.3 p.1))
            (set! y.4 x.3)
            (set! p.1 4)
            (set! y.4 (+ y.4 p.1))
            (set! z.5 x.3)
            (set! z.5 (+ z.5 w.2))
            (set! t.6 y.4)
            (set! p.1 -1)
            (set! t.6 (* t.6 p.1))
            (set! z.5 (+ z.5 t.6))
            (halt z.5))))
    '(module
      ((locals (v.1 w.2 x.3 y.4 z.5 t.6 p.1))
        (conflicts
        ((p.1 (z.5 t.6 y.4 x.3 w.2))
          (t.6 (p.1 z.5))
          (z.5 (p.1 t.6 w.2 y.4))
          (y.4 (z.5 x.3 p.1 w.2))
          (x.3 (y.4 p.1 w.2))
          (w.2 (z.5 y.4 p.1 x.3 v.1))
          (v.1 (w.2)))))
      (begin
        (set! v.1 1)
        (set! w.2 46)
        (set! x.3 v.1)
        (set! p.1 7)
        (set! x.3 (+ x.3 p.1))
        (set! y.4 x.3)
        (set! p.1 4)
        (set! y.4 (+ y.4 p.1))
        (set! z.5 x.3)
        (set! z.5 (+ z.5 w.2))
        (set! t.6 y.4)
        (set! p.1 -1)
        (set! t.6 (* t.6 p.1))
        (set! z.5 (+ z.5 t.6))
        (halt z.5))))

  ; tests for assign-registers
  (check-equal?
    (assign-registers
      '(module ((locals (x.1))
                (conflicts ((x.1 ()))))
        (begin
          (set! x.1 42)
          (halt x.1))))
    '(module
      ((locals (x.1)) (conflicts ((x.1 ()))) (assignment ((x.1 r15))))
      (begin (set! x.1 42) (halt x.1))))
  ; with param regs
  (check-equal?
    (parameterize ([current-assignable-registers '(r9)])
      (assign-registers
        '(module ((locals (x.1))
                  (conflicts ((x.1 ()))))
          (begin
            (set! x.1 42)
            (halt x.1)))))
    '(module
      ((locals (x.1)) (conflicts ((x.1 ()))) (assignment ((x.1 r9))))
      (begin (set! x.1 42) (halt x.1))))
  ; without regs (test spilling)
  (check-equal?
    (parameterize ([current-assignable-registers '()])
      (assign-registers
      '(module ((locals (x.1))
                (conflicts ((x.1 ()))))
        (begin
          (set! x.1 42)
          (halt x.1)))))
    '(module
      ((locals (x.1)) (conflicts ((x.1 ()))) (assignment ((x.1 fv0))))
      (begin (set! x.1 42) (halt x.1))))
  ; multiple splling to fvar
  (check-equal?
    (parameterize ([current-assignable-registers '()])
      (assign-registers
      '(module ((locals (x.1 y.1))
                (conflicts ((x.1 ()) (y.1 ()))))
        (begin
          (set! x.1 42)
          (set! y.1 42)
          (set! x.1 (+ x.1 y.1))
          (halt x.1)))))
    '(module
      ((locals (x.1 y.1)) (conflicts ((x.1 ()) (y.1 ()))) (assignment ((y.1 fv0) (x.1 fv1))))
        (begin
          (set! x.1 42)
          (set! y.1 42)
          (set! x.1 (+ x.1 y.1))
          (halt x.1))))
  ; test p1 v1 in same reg, x3 and t6 also
  (check-equal?
    (assign-registers
      '(module ((locals (v.1 w.2 x.3 y.4 z.5 t.6 p.1))
             (conflicts
              ((x.3 (z.5 p.1 y.4 v.1 w.2))
               (w.2 (z.5 p.1 y.4 v.1 x.3))
               (v.1 (w.2 x.3))
               (y.4 (t.6 z.5 p.1 w.2 x.3))
               (p.1 (t.6 z.5 y.4 w.2 x.3))
               (z.5 (t.6 p.1 y.4 w.2 x.3))
               (t.6 (z.5 p.1 y.4)))))
        (begin
          (set! v.1 1)
          (set! w.2 46)
          (set! x.3 v.1)
          (set! p.1 7)
          (set! x.3 (+ x.3 p.1))
          (set! y.4 x.3)
          (set! p.1 4)
          (set! y.4 (+ y.4 p.1))
          (set! z.5 x.3)
          (set! z.5 (+ z.5 w.2))
          (set! t.6 y.4)
          (set! p.1 -1)
          (set! t.6 (* t.6 p.1))
          (set! z.5 (+ z.5 t.6))
          (halt z.5))))
    '(module
      ((locals (v.1 w.2 x.3 y.4 z.5 t.6 p.1))
        (conflicts
        ((x.3 (z.5 p.1 y.4 v.1 w.2))
          (w.2 (z.5 p.1 y.4 v.1 x.3))
          (v.1 (w.2 x.3))
          (y.4 (t.6 z.5 p.1 w.2 x.3))
          (p.1 (t.6 z.5 y.4 w.2 x.3))
          (z.5 (t.6 p.1 y.4 w.2 x.3))
          (t.6 (z.5 p.1 y.4))))
        (assignment
        ((p.1 r15) (z.5 r14) (y.4 r13) (x.3 r9) (w.2 r8) (t.6 r9) (v.1 r15))))
      (begin
        (set! v.1 1)
        (set! w.2 46)
        (set! x.3 v.1)
        (set! p.1 7)
        (set! x.3 (+ x.3 p.1))
        (set! y.4 x.3)
        (set! p.1 4)
        (set! y.4 (+ y.4 p.1))
        (set! z.5 x.3)
        (set! z.5 (+ z.5 w.2))
        (set! t.6 y.4)
        (set! p.1 -1)
        (set! t.6 (* t.6 p.1))
        (set! z.5 (+ z.5 t.6))
        (halt z.5))))

  ; tests for select-instructions
  (check-equal? 
    (select-instructions '(module (+ 2 2)))
    '(module () (begin (set! tmp.1 2) (set! tmp.1 (+ tmp.1 2)) (halt tmp.1))))
  (check-equal? 
    (select-instructions '(module (begin (set! x.1 5) x.1)))
    '(module () (begin (set! x.1 5) (halt x.1))))
  (check-equal? 
    (select-instructions '(module (begin (set! x.1 (+ 2 2)) x.1)))
    '(module () (begin (set! x.1 2) (set! x.1 (+ x.1 2)) (halt x.1))))
  (check-equal? 
    (select-instructions '(module (begin (set! x.1 2) (set! x.2 2) (+ x.1 x.2))))
    '(module
      ()
      (begin
        (set! x.1 2)
        (set! x.2 2)
        (set! tmp.2 x.1)
        (set! tmp.2 (+ tmp.2 x.2))
        (halt tmp.2))))
  (check-equal? 
    (select-instructions 
    '(module 
      (begin 
        (begin 
          (set! x.0 19) 
          (set! y.0 (+ x.0 1))) 
        (* y.0 2))))
    '(module
      ()
      (begin 
        (set! x.0 19)
        (set! tmp.3 x.0)
        (set! tmp.3 (+ tmp.3 1))
        (set! y.0 tmp.3)
        (set! tmp.4 y.0)
        (set! tmp.4 (* tmp.4 2))
        (halt tmp.4))))
  ; v4
  (check-equal?
    (select-instructions '(module (if (= x.1 x.2) y.1 y.2)))
    '(module () (if (= x.1 x.2) (halt y.1) (halt y.2))))
  (check-equal? ; (relop triv triv) => (set! aloc triv) (relop aloc triv)
    (select-instructions '(module (if (= 42 x.2) y.1 y.2)))
    '(module () (if (begin (set! tmp.5 42) (= tmp.5 x.2)) (halt y.1) (halt y.2))))
  (check-equal? 
    (select-instructions '(module (if (= x.1 x.2) (begin (set! y.1 1) y.1) (begin (set! y.1 0) y.1))))
    '(module
      ()
      (if (= x.1 x.2)
        (begin (set! y.1 1) (halt y.1))
        (begin (set! y.1 0) (halt y.1)))))

  ; canonicalize-bind tests
  (check-equal? 
    (canonicalize-bind '(module (begin (set! x.1 (begin (set! x.2 1) x.2)) x.1)))
    '(module (begin (begin (set! x.2 1) (set! x.1 x.2)) x.1)))
  (check-equal? 
    (canonicalize-bind '(module (begin (set! x.1 (if (true) 1 0)) x.1)))
    '(module (begin (if (true) (set! x.1 1) (set! x.1 0)) x.1)))
  (check-equal?
    (canonicalize-bind '(module (begin (set! x.1 (if (true) (begin (set! y.1 1) 1) (begin (set! y.1 0) 0))) x.1)))
    '(module
      (begin
        (if (true)
          (begin (set! y.1 1) (set! x.1 1))
          (begin (set! y.1 0) (set! x.1 0)))
        x.1)))

  ; sequentialize-let tests
  (check-equal? 
    (sequentialize-let '(module (let ((x.1 5)) x.1)))
    '(module (begin (set! x.1 5) x.1)))
  (check-equal? 
    (sequentialize-let '(module (let ((x.1 5) (x.2 4)) (+ x.1 x.2))))
    '(module (begin (set! x.1 5) (set! x.2 4) (+ x.1 x.2))))
  ; v4
  (check-equal? 
    (sequentialize-let '(module (if (let ((x.1 1) (x.2 2)) (if (= x.1 x.2) (true) (false))) 42 0)))
    '(module (if (begin (set! x.1 1) (set! x.2 2) (if (= x.1 x.2) (true) (false))) 42 0)))

  ; uniquify tests
  (check-equal? 
    (uniquify '(module (+ 2 2)))
    '(module (+ 2 2)))
  (check-equal? 
    (uniquify '(module (let ([x 5]) x)))
    '(module (let ((x.6 5)) x.6)))
  (check-equal? 
    (uniquify '(module (let ([x (+ 2 2)]) x)))
    '(module (let ((x.7 (+ 2 2))) x.7)))
  (check-equal? 
    (uniquify '(module (let ([x 2]) (let ([y 2]) (+ x y)))))
    '(module (let ((x.8 2)) (let ((y.9 2)) (+ x.8 y.9)))))
  (check-equal? 
    (uniquify '(module (let ([x 2]) (let ([x 2]) (+ x x)))))
    '(module (let ((x.10 2)) (let ((x.11 2)) (+ x.11 x.11)))))
  ; v4 
  (check-equal? 
    (uniquify '(module (if (let ([x 2]) (true)) 1 0)))
    '(module (if (let ((x.12 2)) (true)) 1 0)))

  ; tests for interp-values-lang
  (check-equal?
    (interp-values-lang
      '(module (+ 2 2)))
    4)
  (check-equal?
    (interp-values-lang
      '(module (let ([x 5]) x)))
    5)
  (check-equal?
    (interp-values-lang
      '(module (let ([x (+ 2 2)]) x)))
    4)
  (check-equal?
    (interp-values-lang
      '(module (let ([x 2]) (let ([y 2]) (+ x y)))))
    4)
  (check-equal?
    (interp-values-lang
      '(module (let ([x 2]) (let ([x 2]) (+ x x)))))
    4)
  ; v4
  (check-equal?
    (interp-values-lang
      '(module (let ([x 20][y 10]) (if (> x y) 1 0))))
    1)
  (check-equal?
    (interp-values-lang
      '(module 
        (let 
          ([x 20][y 10]) 
          (if (> x y) (+ x y) 0))))
    30)
  (check-equal?
    (interp-values-lang
      '(module (if (true) 1 0)))
    1)
  )