open Util.Assert
open X86
open Sim.Simulator
open Gradedtests
open Asm
(* These tests are provided by you -- they will be graded manually *)

(* You should also add additional test cases here to help you   *)
(* debug your program.                                          *)

let test_my =
  let bin =
    [ InsB0 (Movq, Asm.[ ~$42; ~%Rax ])
    ; InsFrag
    ; InsFrag
    ; InsFrag
    ; InsFrag
    ; InsFrag
    ; InsFrag
    ; InsFrag
    ]
  in
  let asm = [ gtext "main" [ Movq, [ ~$42; ~%Rax ] ] ] in
  assert_eqf (fun () -> (assemble asm).text_seg) bin
;;

let mov_ri =
  test_machine
    [ InsB0 (Movq, Asm.[ ~$42; ~%Rax ])
    ; InsFrag
    ; InsFrag
    ; InsFrag
    ; InsFrag
    ; InsFrag
    ; InsFrag
    ; InsFrag
    ]
;;

(* Recursively calculate a^b *)
(* System V gABI and X86-64 psABI *)

(* .text

   .globl power
   power:
   pushq %rbp
   movq %rsp, %rbp
   pushq %rsi
   pushq %rdi

   andq %rsi, %rsi
   jne .nonzero

   movq $1, %rax
   jmp .end

   .nonzero:
   shrq $1, %rsi
   callq power

   imulq %rax, %rax

   andq $1, 8(%rsp)
   jz .end

   imulq (%rsp), %rax

   .end:
   movq %rbp, %rsp
   popq %rbp
   retq

   .section    .note.GNU-stack,"",@progbits *)
let quick_power_rec (a : int) (b : int) =
  [ text
      "power"
      [ Pushq, [ ~%Rbp ]
      ; Movq, [ ~%Rsp; ~%Rbp ]
      ; Pushq, [ ~%Rsi ]
      ; Pushq, [ ~%Rdi ]
      ; Andq, [ ~%Rsi; ~%Rsi ]
      ; J Neq, [ ~$$"nonzero" ]
      ; Movq, [ ~$1; ~%Rax ]
      ; Jmp, [ ~$$"end" ]
      ]
  ; text
      "nonzero"
      [ Shrq, [ ~$1; ~%Rsi ]
      ; Callq, [ ~$$"power" ]
      ; Imulq, [ ~%Rax; ~%Rax ]
      ; Andq, [ ~$1; Ind3 (Lit 8L, Rsp) ]
      ; J Eq, [ ~$$"end" ]
      ; Imulq, [ Ind2 Rsp; ~%Rax ]
      ]
  ; text "end" [ Movq, [ ~%Rbp; ~%Rsp ]; Popq, [ ~%Rbp ]; Retq, [] ]
  ; text
      "main"
      [ Pushq, [ ~%Rbp ]
      ; Movq, [ ~%Rsp; ~%Rbp ]
      ; Movq, [ ~$a; ~%Rdi ]
      ; Movq, [ ~$b; ~%Rsi ]
      ; Callq, [ ~$$"power" ]
      ; Movq, [ ~%Rbp; ~%Rsp ]
      ; Popq, [ ~%Rbp ]
      ; Retq, []
      ]
  ]
;;

(*RDI, RSI, RDX*)
(*
   fib:
   ; Input:
   ; RDI = n (index of Fibonacci number to calculate)
   ; RSI = a (initial first value)
   ; RDX = b (initial second value)

   ; Base case: if n == 0, return a
   cmp     rdi, 0          ; Compare n with 0
   je      .return_a       ; If n == 0, return a (in RSI)

   ; Base case: if n == 1, return b
   cmp     rdi, 1          ; Compare n with 1
   je      .return_b       ; If n == 1, return b (in RDX)

   ; Recursive case: F(n) = F(n-1) + F(n-2)
   ; Call nth_fibonacci(n-1, b, a + b)

   sub     rdi, 1          ; n = n - 1 (decrement n)
   mov     rax, rsi        ; rax = a
   add     rax, rdx        ; rax = a + b (prepare new b = a + b)
   mov     rsi, rdx        ; Move b into a's position (next recursive call)
   mov     rdx, rax        ; Move a + b into b's position (next recursive call)

   call    fib             ; Recursive call nth_fibonacci(n-1, b, a+b)
   ret                     ; Return the result in rax

   .return_a:
   mov     rax, rsi        ; Return a (in RSI)
   ret

   .return_b:
   mov     rax, rdx        ; Return b (in RDX)
   ret
*)
let fib_rec (n : int) =
  [ text
      "fib"
      [ Cmpq, [ ~$0; ~%Rdi ]
      ; J Eq, [ ~$$"return_a" ]
      ; Cmpq, [ ~$1; ~%Rdi ]
      ; J Eq, [ ~$$"return_b" ]
      ; Subq, [ ~$1; ~%Rdi ]
      ; Movq, [ ~%Rsi; ~%Rax ]
      ; Addq, [ ~%Rdx; ~%Rax ]
      ; Movq, [ ~%Rdx; ~%Rsi ]
      ; Movq, [ ~%Rax; ~%Rdx ]
      ; Callq, [ ~$$"fib" ]
      ; Retq, []
      ]
  ; text "return_a" [ Movq, [ ~%Rsi; ~%Rax ]; Retq, [] ]
  ; text "return_b" [ Movq, [ ~%Rdx; ~%Rax ]; Retq, [] ]
  ; text
      "main"
      [ Pushq, [ ~%Rbp ]
      ; Movq, [ ~%Rsp; ~%Rbp ]
      ; Movq, [ ~$n; ~%Rdi ]
      ; Movq, [ ~$0; ~%Rsi ]
      ; Movq, [ ~$1; ~%Rdx ]
      ; Callq, [ ~$$"fib" ]
      ; Movq, [ ~%Rbp; ~%Rsp ]
      ; Popq, [ ~%Rbp ]
      ; Retq, []
      ]
  ]
;;

let provided_tests : suite =
  [ Test ("My Tests", [ "assert", test_my ])
  ; Test
      ( "Student-Provided Big Test for Part III: Score recorded as \
         PartIIITestCase"
      , [ ( "quick power1"
          , program_test (quick_power_rec 23 12) 21914624432020321L )
        ; "quick power2", program_test (quick_power_rec 2 10) 1024L
        ; ( "quick power3"
          , program_test (quick_power_rec 3 36) 150094635296999121L )
        ; "fib1", program_test (fib_rec 1) 1L
        ; "fib2", program_test (fib_rec 10) 55L
        ; "fib3", program_test (fib_rec 50) 12586269025L
        ] )
  ]
;;
