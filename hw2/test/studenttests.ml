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
(* Pass parameters through register Rdi and Rsi *)
let quick_power_rec (a : int) (b : int) =
  [ text
      "power"
      [ Pushq, [ ~%Rbp ]
      ; Movq, [ ~%Rsp; ~%Rbp ]
      ; Subq, [ ~$32; ~%Rsp ]
      ; Movq, [ ~%Rdi; Ind3 (Lit (-24L), Rbp) ]
      ; Movq, [ ~%Rsi; Ind3 (Lit (-32L), Rbp) ]
      ; Cmpq, [ ~$0; Ind1 (Lit (-32L)) ]
      ; J Neq, [ ~$$"calc" ]
      ; Movq, [ ~$1; ~%Rax ]
      ; Jmp, [ ~$$"rec0" ]
      ]
  ; text
      "calc"
      [ Movq, [ Ind3 (Lit (-32L), Rbp); ~%Rax ]
      ; Sarq, [ ~%Rax ]
      ; Movq, [ ~%Rax; ~%Rdx ]
      ; Movq, [ Ind3 (Lit (-24L), Rbp); ~%Rax ]
      ; Movq, [ ~%Rdx; ~%Rsi ]
      ; Movq, [ ~%Rax; ~%Rdi ]
      ; Callq, [ ~$$"power" ]
      ; Movq, [ ~%Rax; Ind3 (Lit (-8L), Rbp) ]
      ; Movq, [ Ind3 (Lit (-32L), Rbp); ~%Rax ]
      ; Andq, [ ~$1; ~%Rax ]
      ; Andq, [ ~%Rax; ~%Rax ]
      ; J Eq, [ ~$$"recn" ]
      ; Movq, [ Ind3 (Lit (-8L), Rbp); ~%Rax ]
      ; Imulq, [ Ind3 (Lit (-24L), Rbp); ~%Rax ]
      ; Movq, [ ~%Rax; Ind3 (Lit (-8L), Rbp) ]
      ]
  ; text "recn" [ Movq, [ Ind3 (Lit (-8L), Rbp); ~%Rax ] ]
  ; text "rec0" [ Movq, [ ~%Rbp; ~%Rsp ]; Popq, [ ~%Rbp ]; Retq, [] ]
  ; text
      "main"
      [ Movq, [ ~$b; ~%Rsi ]
      ; Movq, [ ~$a; ~%Rdi ]
      ; Callq, [ ~$$"power" ]
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
