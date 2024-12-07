(* The 3 graded student test cases *)

open Testlib
open Util.Assert
module Typechecker = Oat.Typechecker
module Tctxt = Oat.Tctxt

(* Typechecking test cases *)
let subtype_tests =
  [ ( "subtype: struct A <: struct B"
    , fun () ->
        let ctxt : Tctxt.t =
          Typechecker.create_struct_ctxt
            [ Gtdecl
                { elt =
                    ( "A"
                    , [ { fieldName = "x"; ftyp = TInt }
                      ; { fieldName = "y"
                        ; ftyp = TRef (RFun ([ TInt; TInt ], RetVal TInt))
                        }
                      ; { fieldName = "z"; ftyp = TNullRef RString }
                      ; { fieldName = "n"; ftyp = TBool }
                      ] )
                ; loc = "", (1, 0), (6, 1)
                }
            ; Gtdecl
                { elt =
                    ( "B"
                    , [ { fieldName = "x"; ftyp = TInt }
                      ; { fieldName = "y"
                        ; ftyp = TRef (RFun ([ TInt; TInt ], RetVal TInt))
                        }
                      ; { fieldName = "z"; ftyp = TNullRef RString }
                      ] )
                ; loc = "", (8, 0), (12, 1)
                }
            ]
        in
        if Typechecker.subtype ctxt (TRef (RStruct "A")) (TRef (RStruct "B"))
        then ()
        else failwith "should not fail" )
  ; ( "subtype: struct A </: struct B"
    , fun () ->
        let ctxt : Oat.Tctxt.t =
          Typechecker.create_struct_ctxt
            [ Gtdecl
                { elt =
                    ( "A"
                    , [ { fieldName = "x"; ftyp = TInt }
                      ; { fieldName = "y"
                        ; ftyp = TRef (RFun ([ TInt; TInt ], RetVal TInt))
                        }
                      ; { fieldName = "z"; ftyp = TRef RString }
                      ; { fieldName = "n"; ftyp = TBool }
                      ] )
                ; loc = "", (1, 0), (6, 1)
                }
            ; Gtdecl
                { elt =
                    ( "B"
                    , [ { fieldName = "x"; ftyp = TInt }
                      ; { fieldName = "y"
                        ; ftyp = TRef (RFun ([ TInt; TInt ], RetVal TInt))
                        }
                      ; { fieldName = "z"; ftyp = TNullRef RString }
                      ] )
                ; loc = "", (8, 0), (12, 1)
                }
            ]
        in
        if Typechecker.subtype ctxt (TRef (RStruct "A")) (TRef (RStruct "B"))
        then failwith "should fail"
        else () )
  ]
;;

(* Program test case *)
let program_tests =
  [ "hw5programs/studenttest_bst.oat", "", "1064653841854927370" ]
;;

let student_shared_tests : suite =
  [ GradedTest ("student shared subtype tests", 1, subtype_tests)
  ; GradedTest
      ("student shared program tests", 1, executed_oat_file program_tests)
  ]
;;
