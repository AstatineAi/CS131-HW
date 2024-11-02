open Util.Assert
open Gradedtests

(* These tests are provided by you -- they will be graded manually *)

(* You should also add additional test cases here to help you   *)
(* debug your program.                                          *)

let builtin_tests =
  [ "llprograms/add_twice.ll", 29L
  ; "llprograms/arith_combo_dce.ll", 4L
  ; "llprograms/arith_combo_fold.ll", 4L
  ; "llprograms/arith_combo.ll", 4L
  ; "llprograms/binary_gcd.ll", 3L
  ; "llprograms/binarysearch.ll", 8L
  ; "llprograms/call7.ll", 7L
  ; "llprograms/call8.ll", 21L
  ; "llprograms/cbr3.ll", 9L
  ; "llprograms/euclid.ll", 2L
  ; "llprograms/gcd_euclidian.ll", 2L
  ; "llprograms/gep10.ll", 3L
  ; "llprograms/gep9.ll", 5L
  ; "llprograms/kaiterry_pi.ll", 0L
  ; "llprograms/kaiterry_pi_opt.ll", 0L
  ; "llprograms/kaiterry_units.ll", 1L
  ; "llprograms/kaiterry_units_opt.ll", 1L
  ; "llprograms/lfsr.ll", 108L
  ; "llprograms/linear_search.ll", 1L
  ; "llprograms/matmul.ll", 0L
  ; "llprograms/max_thomas_test.ll", 120L
  ; "llprograms/max_thomas_test_opt.ll", 120L
  ; "llprograms/naive_factor_nonprime.ll", 0L
  ; "llprograms/naive_factor_prime.ll", 1L
  ; "llprograms/qtree.ll", 3L
  ; "llprograms/regtest1.ll", 254L
  ; "llprograms/return_intermediate_dce.ll", 18L
  ; "llprograms/return_intermediate_fold.ll", 18L
  ; "llprograms/return_intermediate.ll", 18L
  ; "llprograms/sub_neg_dce.ll", 255L
  ; "llprograms/sub_neg_fold.ll", 255L
  ; "llprograms/sub_neg.ll", 255L
  ; "llprograms/sum_tree.ll", 116L
  ]
;;

let provided_tests : suite =
  [ GradedTest ("builtin tests", 33, executed builtin_tests) ]
;;
