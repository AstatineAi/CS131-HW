(* The 3 graded student test cases *)

(* Typechecking test cases *)
let sub_type_case =
  [ ( "subtype: struct A <: struct B"
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
let program_test =
  [ "hw5programs/studenttest_bst.oat", "", "1064653841854927370" ]
;;
