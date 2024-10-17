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

let provided_tests : suite =
  [ Test ("My Tests", [ "assert", test_my ])
  ; Test
      ( "Student-Provided Big Test for Part III: Score recorded as \
         PartIIITestCase"
      , [ "quick power", program_test (quick_power_rec 23 12) 21914624432020321L
        ] )
  ]
;;
