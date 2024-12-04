open Ast
open Astlib
open Tctxt

(* Error Reporting ---------------------------------------------------------- *)
(* NOTE: Use type_error to report error messages for ill-typed programs. *)

exception TypeError of string

let type_error (l : 'a node) (err : string) =
  let _, (s, e), _ = l.loc in
  raise (TypeError (Printf.sprintf "[%d, %d] %s" s e err))
;;

(* initial context: G0 ------------------------------------------------------ *)
(* The Oat types of the Oat built-in functions *)
let builtins =
  [ "array_of_string", ([ TRef RString ], RetVal (TRef (RArray TInt)))
  ; "string_of_array", ([ TRef (RArray TInt) ], RetVal (TRef RString))
  ; "length_of_string", ([ TRef RString ], RetVal TInt)
  ; "string_of_int", ([ TInt ], RetVal (TRef RString))
  ; "string_cat", ([ TRef RString; TRef RString ], RetVal (TRef RString))
  ; "print_string", ([ TRef RString ], RetVoid)
  ; "print_int", ([ TInt ], RetVoid)
  ; "print_bool", ([ TBool ], RetVoid)
  ]
;;

(* binary operation types --------------------------------------------------- *)
let typ_of_binop : Ast.binop -> Ast.ty * Ast.ty * Ast.ty = function
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> TInt, TInt, TInt
  | Lt | Lte | Gt | Gte -> TInt, TInt, TBool
  | And | Or -> TBool, TBool, TBool
  | Eq | Neq -> failwith "typ_of_binop called on polymorphic == or !="
;;

(* unary operation types ---------------------------------------------------- *)
let typ_of_unop : Ast.unop -> Ast.ty * Ast.ty = function
  | Neg | Bitnot -> TInt, TInt
  | Lognot -> TBool, TBool
;;

(* subtyping ---------------------------------------------------------------- *)
(* Decides whether H |- t1 <: t2
   - assumes that H contains the declarations of all the possible struct types

   - you will want to introduce addition (possibly mutually recursive)
     helper functions to implement the different judgments of the subtyping
     relation. We have included a template for subtype_ref to get you started.
     (Don't forget about OCaml's 'and' keyword.)
*)
let rec subtype (c : Tctxt.t) (t1 : Ast.ty) (t2 : Ast.ty) : bool =
  match t1, t2 with
  | TInt, TInt | TBool, TBool -> true
  | TNullRef t1, TNullRef t2 | TRef t1, TRef t2 | TRef t1, TNullRef t2 ->
    subtype_ref c t1 t2
  | _ -> false

(* Decides whether H |-r ref1 <: ref2 *)
and subtype_ref (c : Tctxt.t) (t1 : Ast.rty) (t2 : Ast.rty) : bool =
  match t1, t2 with
  | RString, RString -> true
  | RArray t1, RArray t2 when t1 = t2 -> true
  | RStruct id1, RStruct id2 ->
    let t1 = Tctxt.lookup_struct id1 c in
    let t2 = Tctxt.lookup_struct id2 c in
    subtype_struct c t1 t2
  | RFun (p1, rt1), RFun (p2, rt2) ->
    (try List.for_all2 (subtype c) p2 p1 && subtype_ret c rt1 rt2 with
     | _ -> false)
  | _ -> false

and same_ty (c : Tctxt.t) (t1 : Ast.ty) (t2 : Ast.ty) : bool =
  subtype c t1 t2 && subtype c t2 t1

and subtype_struct (c : Tctxt.t) (a : field list) (b : field list) : bool =
  match a, b with
  | _, [] -> true
  | h1 :: t1, h2 :: t2 ->
    h1.fieldName = h2.fieldName
    && same_ty c h1.ftyp h2.ftyp
    && subtype_struct c t1 t2
  | _ -> false

(* Decides whether H |-rt rt1 <: rt2 *)
and subtype_ret (c : Tctxt.t) (t1 : Ast.ret_ty) (t2 : Ast.ret_ty) : bool =
  match t1, t2 with
  | RetVoid, RetVoid -> true
  | RetVal t1, RetVal t2 -> subtype c t1 t2
  | _ -> false
;;

(* well-formed types -------------------------------------------------------- *)
(* Implement a (set of) functions that check that types are well formed according
   to the H |- t and related inference rules

   - the function should succeed by returning () if the type is well-formed
     according to the rules

   - the function should fail using the "type_error" helper function if the
     type is not well formed

   - l is just an ast node that provides source location information for
     generating error messages (it's only needed for the type_error generation)

   - tc contains the structure definition context
*)
let rec typecheck_ty (l : 'a Ast.node) (tc : Tctxt.t) (t : Ast.ty) : unit =
  match t with
  | TInt | TBool -> ()
  | TRef t | TNullRef t -> typecheck_refty l tc t

and typecheck_refty (l : 'a Ast.node) (tc : Tctxt.t) (t : Ast.rty) : unit =
  match t with
  | RString -> ()
  | RArray t -> typecheck_ty l tc t
  | RStruct id ->
    (match Tctxt.lookup_struct_option id tc with
     | Some _ -> ()
     | None -> type_error l "wf_reftokokstruct")
  | RFun (p, rt) ->
    List.iter (fun t -> typecheck_ty l tc t) p;
    typecheck_retty l tc rt

and typecheck_retty (l : 'a Ast.node) (tc : Tctxt.t) (t : Ast.ret_ty) : unit =
  match t with
  | RetVoid -> ()
  | RetVal t -> typecheck_ty l tc t
;;

(* A helper function to determine whether a type allows the null value *)
let is_nullable_ty (t : Ast.ty) : bool =
  match t with
  | TNullRef _ -> true
  | _ -> false
;;

(* typechecking expressions ------------------------------------------------- *)
(* Typechecks an expression in the typing context c, returns the type of the
   expression.  This function should implement the inference rules given in the
   oat.pdf specification.  There, they are written:

       H; G; L |- exp : t

   See tctxt.ml for the implementation of the context c, which represents the
   four typing contexts: H - for structure definitions G - for global
   identifiers L - for local identifiers

   Returns the (most precise) type for the expression, if it is type correct
   according to the inference rules.

   Uses the type_error function to indicate a (useful!) error message if the
   expression is not type correct.  The exact wording of the error message is
   not important, but the fact that the error is raised, is important.  (Our
   tests also do not check the location information associated with the error.)

   Notes: - Structure values permit the programmer to write the fields in any
   order (compared with the structure definition).  This means that, given the
   declaration struct T { a:int; b:int; c:int } The expression new T {b=3; c=4;
   a=1} is well typed.  (You should sort the fields to compare them.)
*)
let rec typecheck_exp (c : Tctxt.t) (e : Ast.exp node) : Ast.ty =
  match e.elt with
  | CNull t ->
    (try typecheck_ty e c (TRef t) with
     | _ -> type_error e "typ_null");
    TNullRef t
  | CBool _ -> TBool
  | CInt _ -> TInt
  | CStr _ -> TRef RString
  | Id id ->
    (match Tctxt.lookup_local_option id c with
     | Some t -> t
     | _ ->
       (match Tctxt.lookup_global_option id c with
        | Some t -> t
        | _ -> type_error e "typ_local and typ_global"))
  | CArr (t, es) ->
    typecheck_ty e c t;
    let ts =
      try List.map (typecheck_exp c) es with
      | _ -> type_error e "typ_carr"
    in
    if List.for_all (fun t' -> subtype c t' t) ts
    then TRef (RArray t)
    else type_error e "typ_carr"
  | NewArr (t, exp) ->
    typecheck_ty e c t;
    if typecheck_exp c exp <> TInt then type_error e "typ_newarray";
    (match t with
     | TInt | TBool | TNullRef _ -> ()
     | _ -> type_error e "typ_newarray");
    TRef (RArray t)
  | NewArrInit (t, exp1, id, exp2) ->
    typecheck_ty e c t;
    if typecheck_exp c exp1 <> TInt || Tctxt.lookup_local_option id c <> None
    then type_error e "typ_newarrayinit";
    let c' = Tctxt.add_local c id TInt in
    let t' = typecheck_exp c' exp2 in
    if not @@ subtype c' t' t then type_error e "typ_newarrayinit";
    TRef (RArray t)
  | Index (exp1, exp2) ->
    let t1 = typecheck_exp c exp1 in
    let t2 = typecheck_exp c exp2 in
    (match t1 with
     | TRef (RArray t) when t2 = TInt -> t
     | _ -> type_error e "typ_index")
  | Length exp ->
    let _ = typecheck_exp c exp in
    TInt
  | CStruct (id, fs) ->
    (match Tctxt.lookup_struct_option id c with
     | Some ts ->
       let sort_fields =
         List.sort (fun a b -> String.compare a.fieldName b.fieldName)
       in
       let totyp = List.map (fun f -> f.ftyp) in
       let ts = ts |> sort_fields |> totyp in
       let fs =
         try
           List.map
             (fun (id', exp) ->
               { fieldName = id'; ftyp = typecheck_exp c exp })
             fs
         with
         | _ -> type_error e "typ_structex"
       in
       let fs = fs |> sort_fields |> totyp in
       if try List.for_all2 (subtype c) fs ts with
          | _ -> type_error e "typ_structex"
       then TRef (RStruct id)
       else type_error e "typ_structex"
     | None -> type_error e "typ_structex")
  | Proj (exp, id) ->
    (match typecheck_exp c exp with
     | TRef (RStruct s) ->
       (match lookup_field_option s id c with
        | Some t -> t
        | None -> type_error e "typ_field")
     | _ -> type_error e "typ_field")
  | Call (exp, es) ->
    (match typecheck_exp c exp with
     | TRef (RFun (p, RetVal rt)) ->
       let ts = List.map (typecheck_exp c) es in
       if try List.for_all2 (subtype c) ts p with
          | _ -> type_error e "typ_call"
       then rt
       else type_error e "typ_call 0"
     | _ -> type_error e "typ_call")
  | Bop (op, exp1, exp2) when op = Eq || op = Neq ->
    let t1 = typecheck_exp c exp1 in
    let t2 = typecheck_exp c exp2 in
    if subtype c t1 t2 && subtype c t2 t1
    then TBool
    else type_error e "typ_(n)eq"
  | Bop (op, lhs, rhs) ->
    let t1, t2, t = typ_of_binop op in
    let t1' = typecheck_exp c lhs in
    let t2' = typecheck_exp c rhs in
    if t1' = t1 && t2' = t2 then t else type_error e "typ_bop"
  | Uop (op, exp) ->
    let t1, t2 = typ_of_unop op in
    let t = typecheck_exp c exp in
    if t = t1 then t2 else type_error e "typ_uop"
;;

(* statements --------------------------------------------------------------- *)

(* Typecheck a statement
   This function should implement the statment typechecking rules from oat.pdf.

   Inputs:
   - tc: the type context
   - s: the statement node
   - to_ret: the desired return type (from the function declaration)

   Returns:
   - the new type context (which includes newly declared variables in scope
     after this statement)

   - A boolean indicating the return behavior of a statement:
     false:  might not return
     true: definitely returns

   in the branching statements, the return behavior of the branching
   statement is the conjunction of the return behavior of the two
   branches: both both branches must definitely return in order for
   the whole statement to definitely return.

   Intuitively: if one of the two branches of a conditional does not
   contain a return statement, then the entire conditional statement might
   not return.

   looping constructs never definitely return

   Uses the type_error function to indicate a (useful!) error message if the
   statement is not type correct.  The exact wording of the error message is
   not important, but the fact that the error is raised, is important.  (Our
   tests also do not check the location information associated with the error.)

   - You will probably find it convenient to add a helper function that implements the
     block typecheck rules.
*)
let rec typecheck_stmt (tc : Tctxt.t) (s : Ast.stmt node) (to_ret : ret_ty)
  : Tctxt.t * bool
  =
  match s.elt with
  | Assn (exp1, exp2) ->
    (match exp1.elt with
     | Id id ->
       (match lookup_local_option id tc with
        | Some _ -> ()
        | _ ->
          (match lookup_global_option id tc with
           | Some (TRef (RFun _)) -> type_error exp1 "typ_assn"
           | _ -> ()))
     | _ -> ());
    let t = typecheck_exp tc exp1 in
    let t' = typecheck_exp tc exp2 in
    if not @@ subtype tc t' t then type_error s "typ_assn";
    tc, false
  | Decl (id, exp) ->
    let t = typecheck_exp tc exp in
    if Tctxt.lookup_local_option id tc <> None then type_error s "typ_decl";
    let tc' = Tctxt.add_local tc id t in
    tc', false
  | SCall (exp, es) ->
    let t = typecheck_exp tc exp in
    (match t with
     | TRef (RFun (p, RetVoid)) ->
       let ts = List.map (typecheck_exp tc) es in
       if try List.for_all2 (subtype tc) ts p with
          | _ -> type_error s "typ_scall"
       then tc, false
       else type_error s "typ_scall"
     | _ -> type_error s "typ_scall")
  | If (exp, block1, block2) ->
    let t = typecheck_exp tc exp in
    if t <> TBool then type_error s "typ_if";
    let _, r1 = typecheck_block tc block1 to_ret in
    let _, r2 = typecheck_block tc block2 to_ret in
    tc, r1 && r2
  | Cast (rt, id, exp, block1, block2) ->
    let t = typecheck_exp tc exp in
    (match t with
     | TNullRef t' ->
       if not @@ subtype tc (TRef t') (TRef rt) then type_error s "typ_ifq";
       let tc' = Tctxt.add_local tc id t in
       let _, r1 = typecheck_block tc' block1 to_ret in
       let _, r2 = typecheck_block tc block2 to_ret in
       tc', r1 && r2
     | _ -> type_error s "typ_ifq")
  | While (exp, block) ->
    if typecheck_exp tc exp <> TBool then type_error s "typ_while";
    let _ = typecheck_block tc block to_ret in
    tc, false
  | For (vdecls, exp, stmt, block) ->
    let tc' =
      List.fold_left
        (fun tc' ((id, { elt = exp; loc }) as node) ->
          fst @@ typecheck_stmt tc' { elt = Decl node; loc } RetVoid)
        tc
        vdecls
    in
    exp
    |> Option.map (fun t ->
      if typecheck_exp tc' t <> TBool then type_error s "typ_for")
    |> ignore;
    stmt
    |> Option.map (fun t ->
      if snd @@ typecheck_stmt tc' t to_ret then type_error s "typ_for")
    |> ignore;
    typecheck_block tc' block to_ret |> ignore;
    tc, false
  | Ret None ->
    if to_ret <> RetVoid then type_error s "typ_retVoid";
    tc, true
  | Ret (Some exp) ->
    (match to_ret with
     | RetVoid -> type_error s "typ_retT"
     | RetVal t ->
       let t' = typecheck_exp tc exp in
       if not @@ subtype tc t' t then type_error s "typ_retT";
       tc, true)

and typecheck_block (tc : Tctxt.t) (blk : Ast.block) (to_ret : ret_ty)
  : Tctxt.t * bool
  =
  match blk with
  | hd :: [] -> typecheck_stmt tc hd to_ret
  | hd :: tl ->
    let tc', returns = typecheck_stmt tc hd to_ret in
    if returns then type_error hd "typ_block (typ_stmts)";
    typecheck_block tc' tl to_ret
  | [] -> tc, true
;;

(* struct type declarations ------------------------------------------------- *)
(* Here is an example of how to implement the TYP_TDECLOK rule, which is
   is needed elswhere in the type system.
*)

(* Helper function to look for duplicate field names *)
let rec check_dups (fs : field list) =
  match fs with
  | [] -> false
  | h :: t ->
    List.exists (fun x -> x.fieldName = h.fieldName) t || check_dups t
;;

let typecheck_tdecl
  (tc : Tctxt.t)
  (id : id)
  (fs : field list)
  (l : 'a Ast.node)
  : unit
  =
  if check_dups fs
  then type_error l ("Repeated fields in " ^ id)
  else List.iter (fun f -> typecheck_ty l tc f.ftyp) fs
;;

(* function declarations ---------------------------------------------------- *)
(* typecheck a function declaration
   - ensures formal parameters are distinct
   - extends the local context with the types of the formal parameters to the
     function
   - typechecks the body of the function (passing in the expected return type
   - checks that the function actually returns
*)
let typecheck_fdecl (tc : Tctxt.t) (f : Ast.fdecl) (l : 'a Ast.node) : unit =
  let { frtyp; fname; args; body } = f in
  if args
     |> List.map (fun (ftyp, fieldName) -> { fieldName; ftyp })
     |> check_dups
  then type_error l "typ_fdeclok"
  else (
    let tc = List.fold_left (fun tc (ty, id) -> add_local tc id ty) tc args in
    let _, returns = typecheck_block tc body frtyp in
    if not returns then type_error l "typ_fdeclok")
;;

(* creating the typchecking context ----------------------------------------- *)

(* The following functions correspond to the
   judgments that create the global typechecking context.

   create_struct_ctxt: - adds all the struct types to the struct 'H'
   context (checking to see that there are no duplicate fields

   H |-s prog ==> H'

   create_function_ctxt: - adds the the function identifiers and their
   types to the 'G' context (ensuring that there are no redeclared
   function identifiers)

   H ; G1 |-f prog ==> G2

   create_global_ctxt: - typechecks the global initializers and adds
   their identifiers to the 'G' global context

   H ; G1 |-g prog ==> G2

   NOTE: global initializers may mention function identifiers as
   constants, but can mention only other global values that were declared earlier
*)

let create_struct_ctxt (p : Ast.prog) : Tctxt.t =
  List.fold_left
    (fun c decl ->
      match decl with
      | Gtdecl ({ elt = id, fs } as t) ->
        if lookup_struct_option id c <> None
        then type_error t ("multiple definition of struct " ^ id);
        add_struct c id fs
      | _ -> c)
    empty
    p
;;

let create_builtins_ctxt (tc : Tctxt.t) : Tctxt.t =
  List.fold_left
    (fun c (fname, (args, frtyp)) ->
      add_global c fname (TRef (RFun (args, frtyp))))
    tc
    builtins
;;

let create_function_ctxt (tc : Tctxt.t) (p : Ast.prog) : Tctxt.t =
  List.fold_left
    (fun c decl ->
      match decl with
      | Gfdecl ({ elt = { frtyp; fname; args } } as t) ->
        if lookup_global_option fname c <> None
        then type_error t ("multiple definition of function " ^ fname);
        add_global c fname (TRef (RFun (List.map fst args, frtyp)))
      | _ -> c)
    tc
    p
;;

let create_global_ctxt (tc : Tctxt.t) (p : Ast.prog) : Tctxt.t =
  List.fold_left
    (fun c decl ->
      match decl with
      | Gvdecl ({ elt = { name; init } } as t) ->
        if lookup_global_option name c <> None
        then type_error t ("multiple definition of global " ^ name);
        add_global c name (typecheck_exp c init)
      | _ -> c)
    tc
    p
;;

(* This function implements the |- prog and the H ; G |- prog
   rules of the oat.pdf specification.
*)
let typecheck_program (p : Ast.prog) : unit =
  let sc = create_struct_ctxt p in
  let bc = create_builtins_ctxt sc in
  let fc = create_function_ctxt bc p in
  let tc = create_global_ctxt fc p in
  List.iter
    (fun p ->
      match p with
      | Gfdecl ({ elt = f } as l) -> typecheck_fdecl tc f l
      | Gtdecl ({ elt = id, fs } as l) -> typecheck_tdecl tc id fs l
      | _ -> ())
    p
;;
