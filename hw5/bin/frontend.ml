open Ll
open Llutil
open Ast

(* instruction streams ------------------------------------------------------ *)

(* As in the last project, we'll be working with a flattened representation
   of LLVMlite programs to make emitting code easier. This version
   additionally makes it possible to emit elements will be gathered up and
   "hoisted" to specific parts of the constructed CFG
   - G of gid * Ll.gdecl: allows you to output global definitions in the middle
     of the instruction stream. You will find this useful for compiling string
     literals
   - E of uid * insn: allows you to emit an instruction that will be moved up
     to the entry block of the current function. This will be useful for 
     compiling local variable declarations
*)

type elt =
  | L of Ll.lbl (* block labels *)
  | I of uid * Ll.insn (* instruction *)
  | T of Ll.terminator (* block terminators *)
  | G of gid * Ll.gdecl (* hoisted globals (usually strings) *)
  | E of uid * Ll.insn (* hoisted entry block instructions *)

type stream = elt list

let ( >@ ) x y = y @ x
let ( >:: ) x y = y :: x
let lift : (uid * insn) list -> stream = List.rev_map (fun (x, i) -> I (x, i))

(* Build a CFG and collection of global variable definitions from a stream *)
let cfg_of_stream (code : stream) : Ll.cfg * (Ll.gid * Ll.gdecl) list =
  let gs, einsns, insns, term_opt, blks =
    List.fold_left
      (fun (gs, einsns, insns, term_opt, blks) e ->
         match e with
         | L l ->
           (match term_opt with
            | None ->
              if List.length insns = 0
              then gs, einsns, [], None, blks
              else
                failwith
                @@ Printf.sprintf
                     "build_cfg: block labeled %s hasno terminator"
                     l
            | Some term -> gs, einsns, [], None, (l, { insns; term }) :: blks)
         | T t -> gs, einsns, [], Some (Llutil.Parsing.gensym "tmn", t), blks
         | I (uid, insn) -> gs, einsns, (uid, insn) :: insns, term_opt, blks
         | G (gid, gdecl) -> (gid, gdecl) :: gs, einsns, insns, term_opt, blks
         | E (uid, i) -> gs, (uid, i) :: einsns, insns, term_opt, blks)
      ([], [], [], None, [])
      code
  in
  match term_opt with
  | None -> failwith "build_cfg: entry block has no terminator"
  | Some term ->
    let insns = einsns @ insns in
    ({ insns; term }, blks), gs
;;

(* compilation contexts ----------------------------------------------------- *)

(* To compile OAT variables, we maintain a mapping of source identifiers to the
   corresponding LLVMlite operands. Bindings are added for global OAT variables
   and local variables that are in scope. *)

module Ctxt = struct
  type t = (Ast.id * (Ll.ty * Ll.operand)) list

  let empty = []

  (* Add a binding to the context *)
  let add (c : t) (id : id) (bnd : Ll.ty * Ll.operand) : t = (id, bnd) :: c

  (* Lookup a binding in the context *)
  let lookup (id : Ast.id) (c : t) : Ll.ty * Ll.operand = List.assoc id c
end

(* Mapping of identifiers representing struct definitions to 
 * the corresponding name-to-name-to-type map.

   Note:  You will need to use these operations when compiling structures.
*)
module TypeCtxt = struct
  type t = (Ast.id * Ast.field list) list

  let empty = []
  let add c id bnd = (id, bnd) :: c
  let lookup id c = List.assoc id c

  let lookup_field st_name f_name (c : t) =
    let rec lookup_field_aux f_name l =
      match l with
      | [] -> failwith "TypeCtxt.lookup_field: Not_found"
      | h :: t ->
        if h.fieldName = f_name then h.ftyp else lookup_field_aux f_name t
    in
    lookup_field_aux f_name (List.assoc st_name c)
  ;;

  let rec index_of f l i =
    match l with
    | [] -> None
    | h :: t -> if h.fieldName = f then Some i else index_of f t (i + 1)
  ;;

  (* Return the index of a field in the struct. *)
  let index_of_field_opt (st : Ast.id) (f : Ast.id) (c : t) : int option =
    index_of f (List.assoc st c) 0
  ;;

  let index_of_field (st : Ast.id) (f : Ast.id) (c : t) : int =
    match index_of_field_opt st f c with
    | None -> failwith "index_of_field: Not found"
    | Some x -> x
  ;;

  (* Return a pair of base type and index into struct *)
  let rec lookup_field_name (st : Ast.id) (f : Ast.id) (c : t)
    : Ast.ty * Int64.t
    =
    let fields = lookup st c in
    match index_of f fields 0 with
    | None -> failwith "no such field"
    | Some x -> List.(nth fields x).ftyp, Int64.of_int x
  ;;
end

(* compiling OAT types ------------------------------------------------------ *)

(* The mapping of source types onto LLVMlite is straightforward. Booleans and ints
   are represented as the the corresponding integer types. OAT strings are 
   pointers to bytes (I8). Arrays are the most interesting type: they are
   represented as pointers to structs where the first component is the number
   of elements in the following array.

   NOTE: structure types are named, so they compile to their named form
*)

let rec cmp_ty (ct : TypeCtxt.t) : Ast.ty -> Ll.ty = function
  | Ast.TBool -> I1
  | Ast.TInt -> I64
  | Ast.TRef r -> Ptr (cmp_rty ct r)
  | Ast.TNullRef r -> Ptr (cmp_rty ct r)

and cmp_ret_ty ct : Ast.ret_ty -> Ll.ty = function
  | Ast.RetVoid -> Void
  | Ast.RetVal t -> cmp_ty ct t

and cmp_fty ct (ts, r) : Ll.fty = List.map (cmp_ty ct) ts, cmp_ret_ty ct r

and cmp_rty ct : Ast.rty -> Ll.ty = function
  | Ast.RString -> I8
  | Ast.RArray u -> Struct [ I64; Array (0, cmp_ty ct u) ]
  | Ast.RStruct r -> Namedt r
  | Ast.RFun (ts, t) ->
    let args, ret = cmp_fty ct (ts, t) in
    Fun (args, ret)
;;

let typ_of_binop : Ast.binop -> Ast.ty * Ast.ty * Ast.ty = function
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> TInt, TInt, TInt
  | Eq | Neq | Lt | Lte | Gt | Gte -> TInt, TInt, TBool
  | And | Or -> TBool, TBool, TBool
;;

let typ_of_unop : Ast.unop -> Ast.ty * Ast.ty = function
  | Neg | Bitnot -> TInt, TInt
  | Lognot -> TBool, TBool
;;

(* Some useful helper functions *)

(* Generate a fresh temporary identifier. Since OAT identifiers cannot begin
   with an underscore, these should not clash with any source variables *)
let gensym : string -> string =
  let c = ref 0 in
  fun (s : string) ->
    incr c;
    Printf.sprintf "_%s%d" s !c
;;

(* Amount of space an Oat type takes when stored in the stack, in bytes.  
   Note that since structured values are manipulated by reference, all
   Oat values take 8 bytes on the stack.
*)
let size_oat_ty (t : Ast.ty) = 8L

(* Generate code to allocate a zero-initialized array of source type TRef (RArray t) of the
   given size. Note "size" is an operand whose value can be computed at
   runtime *)
let oat_alloc_array ct (t : Ast.ty) (size : Ll.operand)
  : Ll.ty * operand * stream
  =
  let ans_id, arr_id = gensym "array", gensym "raw_array" in
  let ans_ty = cmp_ty ct @@ TRef (RArray t) in
  let arr_ty = Ptr I64 in
  ( ans_ty
  , Id ans_id
  , lift
      [ arr_id, Call (arr_ty, Gid "oat_alloc_array", [ I64, size ])
      ; ans_id, Bitcast (arr_ty, Id arr_id, ans_ty)
      ] )
;;

(* A helper function that allocates an oat structure on the 
   heap and returns a target operand with the appropriate reference.  
   
   - generate a call to 'oat_malloc' and use bitcast to convert the
     resulting pointer to the right type

   - make sure to calculate the correct amount of space to allocate!
*)
let oat_alloc_struct (ct : TypeCtxt.t) (id : Ast.id) : Ll.ty * operand * stream
  =
  let fields = TypeCtxt.lookup id ct in
  let size =
    List.fold_left (fun acc f -> Int64.add acc (size_oat_ty f.ftyp)) 0L fields
  in
  let ans_id, struct_id = gensym "struct", gensym "raw_struct" in
  let ans_ty = Ptr (Namedt id) in
  let alloc_code =
    lift
      [ struct_id, Call (Ptr I64, Gid "oat_malloc", [ I64, Const size ])
      ; ans_id, Bitcast (Ptr I64, Id struct_id, ans_ty)
      ]
  in
  ans_ty, Id ans_id, alloc_code
;;

let str_arr_ty s = Array (1 + String.length s, I8)
let i1_op_of_bool b = Ll.Const (if b then 1L else 0L)
let i64_op_of_int i = Ll.Const (Int64.of_int i)

let cmp_binop t (b : Ast.binop) : Ll.operand -> Ll.operand -> Ll.insn =
  let ib b op1 op2 = Ll.Binop (b, t, op1, op2) in
  let ic c op1 op2 = Ll.Icmp (c, t, op1, op2) in
  match b with
  | Ast.Add -> ib Ll.Add
  | Ast.Mul -> ib Ll.Mul
  | Ast.Sub -> ib Ll.Sub
  | Ast.And -> ib Ll.And
  | Ast.IAnd -> ib Ll.And
  | Ast.IOr -> ib Ll.Or
  | Ast.Or -> ib Ll.Or
  | Ast.Shl -> ib Ll.Shl
  | Ast.Shr -> ib Ll.Lshr
  | Ast.Sar -> ib Ll.Ashr
  | Ast.Eq -> ic Ll.Eq
  | Ast.Neq -> ic Ll.Ne
  | Ast.Lt -> ic Ll.Slt
  | Ast.Lte -> ic Ll.Sle
  | Ast.Gt -> ic Ll.Sgt
  | Ast.Gte -> ic Ll.Sge
;;

(* Compiles an expression exp in context c, outputting the Ll operand that will
   receive the value of the expression, and the stream of instructions
   implementing the expression.
*)
let rec cmp_exp (tc : TypeCtxt.t) (c : Ctxt.t) (exp : Ast.exp node)
  : Ll.ty * Ll.operand * stream
  =
  match exp.elt with
  | Ast.CInt i -> I64, Const i, []
  | Ast.CNull r -> cmp_ty tc (TNullRef r), Null, []
  | Ast.CBool b -> I1, i1_op_of_bool b, []
  | Ast.CStr s ->
    let gid = gensym "str_arr" in
    let str_typ = str_arr_ty s in
    let uid = gensym "str" in
    ( Ptr I8
    , Id uid
    , []
      >:: G (gid, (str_typ, GString s))
      >:: I (uid, Gep (Ptr str_typ, Gid gid, [ Const 0L; Const 0L ])) )
  | Ast.Bop ((Ast.Eq as bop), e1, e2) | Ast.Bop ((Ast.Neq as bop), e1, e2) ->
    (* Polymorphic equality operations *)
    (* Allow any type for the first operand, and cast 
        the second operand to the type of the first. *)
    let _, _, ret_ty = typ_of_binop bop in
    let ll_t, op1, code1 = cmp_exp tc c e1 in
    let op2, code2 = cmp_exp_as tc c e2 ll_t in
    let ans_id = gensym "bop" in
    ( cmp_ty tc ret_ty
    , Id ans_id
    , code1 >@ code2 >:: I (ans_id, cmp_binop ll_t bop op1 op2) )
  | Ast.Bop (bop, e1, e2) ->
    let t, _, ret_ty = typ_of_binop bop in
    let ll_t = cmp_ty tc t in
    let op1, code1 = cmp_exp_as tc c e1 ll_t in
    let op2, code2 = cmp_exp_as tc c e2 ll_t in
    let ans_id = gensym "bop" in
    ( cmp_ty tc ret_ty
    , Id ans_id
    , code1 >@ code2 >:: I (ans_id, cmp_binop ll_t bop op1 op2) )
  | Ast.Uop (uop, e) ->
    let t, ret_ty = typ_of_unop uop in
    let op, code = cmp_exp_as tc c e (cmp_ty tc t) in
    let ans_id = gensym "unop" in
    let cmp_uop op = function
      | Ast.Neg -> Binop (Sub, I64, i64_op_of_int 0, op)
      | Ast.Lognot -> Icmp (Eq, I1, op, i1_op_of_bool false)
      | Ast.Bitnot -> Binop (Xor, I64, op, i64_op_of_int (-1))
    in
    cmp_ty tc ret_ty, Id ans_id, code >:: I (ans_id, cmp_uop op uop)
  | Ast.Id id ->
    let t, op = Ctxt.lookup id c in
    (match t with
     | Ptr (Fun _) -> t, op, []
     | Ptr t ->
       let ans_id = gensym id in
       t, Id ans_id, [ I (ans_id, Load (Ptr t, op)) ]
     | _ -> failwith "broken invariant: identifier not a pointer")
  | Ast.Length e ->
    let arr_ty, arr_op, arr_code = cmp_exp tc c e in
    let arr_len_id = gensym "arr_len" in
    let ans_id = gensym "length" in
    ( I64
    , Id ans_id
    , arr_code
      >@ lift
           [ ( arr_len_id
             , Gep (arr_ty, arr_op, [ i64_op_of_int 0; i64_op_of_int 0 ]) )
           ; ans_id, Load (Ptr I64, Id arr_len_id)
           ] )
  | Ast.Index (e, i) ->
    let ans_ty, ptr_op, code = cmp_exp_lhs tc c exp in
    let ans_id = gensym "index" in
    ans_ty, Id ans_id, code >:: I (ans_id, Load (Ptr ans_ty, ptr_op))
  | Ast.Call (f, es) -> cmp_call tc c f es
  | Ast.CArr (elt_ty, cs) ->
    let size_op = Ll.Const (Int64.of_int @@ List.length cs) in
    let arr_ty, arr_op, alloc_code = oat_alloc_array tc elt_ty size_op in
    let ll_elt_ty = cmp_ty tc elt_ty in
    let add_elt s (i, elt) =
      let elt_op, elt_code = cmp_exp_as tc c elt ll_elt_ty in
      let ind = gensym "ind" in
      s
      >@ elt_code
      >@ lift
           [ ind, Gep (arr_ty, arr_op, [ Const 0L; Const 1L; i64_op_of_int i ])
           ; gensym "store", Store (ll_elt_ty, elt_op, Id ind)
           ]
    in
    let ind_code = List.(fold_left add_elt [] @@ mapi (fun i e -> i, e) cs) in
    arr_ty, arr_op, alloc_code >@ ind_code
  | Ast.NewArr (elt_ty, e) ->
    let _, size_op, size_code = cmp_exp tc c e in
    let arr_ty, arr_op, alloc_code = oat_alloc_array tc elt_ty size_op in
    arr_ty, arr_op, size_code >@ alloc_code
  | Ast.NewArrInit (elt_ty, e1, id, e2) ->
    let _, size_op, size_code = cmp_exp tc c e1 in
    let arr_ty, arr_op, alloc_code = oat_alloc_array tc elt_ty size_op in
    let ast_const (n : int) = no_loc (Ast.CInt (Int64.of_int n)) in
    let ast_loop_id = no_loc (Ast.Id id) in
    let temp_arr = gensym "new_arr_init" in
    let ast_temp_arr = no_loc (Ast.Id temp_arr) in
    let alloc_temp_arr : stream =
      lift [ temp_arr, Alloca arr_ty; "", Store (arr_ty, arr_op, Id temp_arr) ]
    in
    let size_id = gensym "size" in
    let size_var_code =
      lift [ size_id, Alloca I64; "", Store (I64, size_op, Id size_id) ]
    in
    let ast_size = no_loc (Ast.Id size_id) in
    let c' = Ctxt.add c temp_arr (Ptr arr_ty, Id temp_arr) in
    let c' = Ctxt.add c' size_id (Ptr I64, Id size_id) in
    let loop : Ast.stmt node =
      no_loc
        (Ast.For
           ( [ id, ast_const 0 ]
           , Some (no_loc (Ast.Bop (Ast.Lt, ast_loop_id, ast_size)))
           , Some
               (no_loc
                  (Ast.Assn
                     ( ast_loop_id
                     , no_loc (Ast.Bop (Ast.Add, ast_loop_id, ast_const 1)) )))
           , [ no_loc
                 (Ast.Assn (no_loc (Ast.Index (ast_temp_arr, ast_loop_id)), e2))
             ] ))
    in
    let _, loop_code = cmp_stmt tc c' Void loop in
    ( arr_ty
    , arr_op
    , size_code >@ alloc_code >@ alloc_temp_arr >@ size_var_code >@ loop_code )
  | Ast.CStruct (id, l) ->
    let st_ty, st_op, alloc_code = oat_alloc_struct tc id in
    let add_field (fname : id) (exp : exp node) : stream =
      let ty', idx = TypeCtxt.lookup_field_name id fname tc in
      let ty = cmp_ty tc ty' in
      let _, exp_op, exp_code = cmp_exp tc c exp in
      let field_id = gensym "field" in
      let field_code =
        lift
          [ field_id, Gep (st_ty, st_op, [ Const 0L; Const idx ])
          ; gensym "store", Store (ty, exp_op, Id field_id)
          ]
      in
      exp_code >@ field_code
    in
    let field_code =
      List.fold_left (fun acc (fname, exp) -> acc >@ add_field fname exp) [] l
    in
    st_ty, st_op, alloc_code >@ field_code
  | Ast.Proj (e, id) ->
    let ans_ty, ptr_op, code = cmp_exp_lhs tc c exp in
    let ans_id = gensym "proj" in
    ans_ty, Id ans_id, code >:: I (ans_id, Load (Ptr ans_ty, ptr_op))

and cmp_exp_lhs (tc : TypeCtxt.t) (c : Ctxt.t) (e : exp node)
  : Ll.ty * Ll.operand * stream
  =
  match e.elt with
  | Ast.Id x ->
    let pt, op = Ctxt.lookup x c in
    let t =
      match pt with
      | Ptr t -> t
      | _ -> failwith "Unexpected variable type"
    in
    t, op, []
  | Ast.Proj (e, i) ->
    let st_ty, st_op, st_code = cmp_exp tc c e in
    (match st_ty with
     | Ptr (Namedt id) ->
       let f_ast_ty, ind = TypeCtxt.lookup_field_name id i tc in
       let f_ty = cmp_ty tc f_ast_ty in
       let ans_id = gensym "proj" in
       ( f_ty
       , Id ans_id
       , st_code >:: I (ans_id, Gep (st_ty, st_op, [ Const 0L; Const ind ])) )
     | _ -> failwith "Proj: invalid field access")
  | Ast.Index (e, i) ->
    let arr_ty, arr_op, arr_code = cmp_exp tc c e in
    let _, ind_op, ind_code = cmp_exp tc c i in
    let ans_ty =
      match arr_ty with
      | Ptr (Struct [ _; Array (_, t) ]) -> t
      | _ -> failwith "Index: indexed into non pointer"
    in
    let ptr_id, tmp_id, call_id =
      gensym "index_ptr", gensym "tmp", gensym "call"
    in
    let tmp_ty = Ptr (Struct [ I64; arr_ty ]) in
    (* call oat_assert_array_length *)
    let assert_code =
      lift
        [ tmp_id, Bitcast (arr_ty, arr_op, tmp_ty)
        ; ( call_id
          , Ll.Call
              ( I64
              , Gid "oat_assert_array_length"
              , [ tmp_ty, Id tmp_id; I64, ind_op ] ) )
        ]
    in
    ( ans_ty
    , Id ptr_id
    , arr_code
      >@ ind_code
      >@ assert_code
      >@ lift
           [ ( ptr_id
             , Gep
                 (arr_ty, arr_op, [ i64_op_of_int 0; i64_op_of_int 1; ind_op ])
             )
           ] )
  | _ -> failwith "invalid lhs expression"

and cmp_call
      (tc : TypeCtxt.t)
      (c : Ctxt.t)
      (exp : Ast.exp node)
      (es : Ast.exp node list)
  : Ll.ty * Ll.operand * stream
  =
  let t, op, s = cmp_exp tc c exp in
  let ts, rt =
    match t with
    | Ptr (Fun (l, r)) -> l, r
    | _ -> failwith "nonfunction passed to cmp_call"
  in
  let args, args_code =
    List.fold_right2
      (fun e t (args, code) ->
         let arg_op, arg_code = cmp_exp_as tc c e t in
         (t, arg_op) :: args, arg_code @ code)
      es
      ts
      ([], [])
  in
  let res_id = gensym "result" in
  rt, Id res_id, s >@ args_code >:: I (res_id, Call (rt, op, args))

and cmp_exp_as (tc : TypeCtxt.t) (c : Ctxt.t) (e : Ast.exp node) (t : Ll.ty)
  : Ll.operand * stream
  =
  let from_t, op, code = cmp_exp tc c e in
  if from_t = t
  then op, code
  else (
    let res_id = gensym "cast" in
    Id res_id, code >:: I (res_id, Bitcast (from_t, op, t)))

(* Compile a statement in context c with return typ rt. Return a new context, 
   possibly extended with new local bindings, and the instruction stream
   implementing the statement.

   Left-hand-sides of assignment statements must either be OAT identifiers,
   or an index into some arbitrary expression of array type. Otherwise, the
   program is not well-formed and your compiler may throw an error.
*)
and cmp_stmt (tc : TypeCtxt.t) (c : Ctxt.t) (rt : Ll.ty) (stmt : Ast.stmt node)
  : Ctxt.t * stream
  =
  match stmt.elt with
  | Ast.Decl (id, init) ->
    let ll_ty, init_op, init_code = cmp_exp tc c init in
    let res_id = gensym id in
    let c' = Ctxt.add c id (Ptr ll_ty, Id res_id) in
    ( c'
    , init_code
      >:: E (res_id, Alloca ll_ty)
      >:: I (gensym "store", Store (ll_ty, init_op, Id res_id)) )
  | Ast.Assn (path, e) ->
    let ll_ty, pop, path_code = cmp_exp_lhs tc c path in
    let eop, exp_code = cmp_exp_as tc c e ll_ty in
    c, path_code >@ exp_code >:: I (gensym "store", Store (ll_ty, eop, pop))
  | Ast.If (guard, st1, st2) ->
    let guard_ty, guard_op, guard_code = cmp_exp tc c guard in
    let _, then_code = cmp_block tc c rt st1 in
    let _, else_code = cmp_block tc c rt st2 in
    let lt, le, lm = gensym "then", gensym "else", gensym "merge" in
    ( c
    , guard_code
      >:: T (Cbr (guard_op, lt, le))
      >:: L lt
      >@ then_code
      >:: T (Br lm)
      >:: L le
      >@ else_code
      >:: T (Br lm)
      >:: L lm )
  | Ast.Cast (typ, id, exp, notnull, null) ->
    let ref_ty, ref_op, ref_code = cmp_exp tc c exp in
    let null_cond = gensym "null_cond" in
    let cast_id = gensym "cast" in
    let notnull_id = gensym id in
    let notnull_ref_ty = Ptr (cmp_rty tc typ) in
    let check_null_code =
      lift
        [ null_cond, Icmp (Eq, ref_ty, ref_op, Null)
        ; cast_id, Bitcast (ref_ty, ref_op, notnull_ref_ty)
        ; notnull_id, Alloca notnull_ref_ty
        ; "", Store (notnull_ref_ty, Id cast_id, Id notnull_id)
        ]
    in
    let c' = Ctxt.add c id (Ptr notnull_ref_ty, Id notnull_id) in
    let _, notnull_code = cmp_block tc c' rt notnull in
    let _, null_code = cmp_block tc c' rt null in
    let lnot, lnull, lm = gensym "notnull", gensym "null", gensym "merge" in
    ( c
    , ref_code
      >@ check_null_code
      >:: T (Cbr (Id null_cond, lnull, lnot))
      >:: L lnot
      >@ notnull_code
      >:: T (Br lm)
      >:: L lnull
      >@ null_code
      >:: T (Br lm)
      >:: L lm )
  | Ast.While (guard, body) ->
    let guard_ty, guard_op, guard_code = cmp_exp tc c guard in
    let lcond, lbody, lpost = gensym "cond", gensym "body", gensym "post" in
    let _, body_code = cmp_block tc c rt body in
    ( c
    , []
      >:: T (Br lcond)
      >:: L lcond
      >@ guard_code
      >:: T (Cbr (guard_op, lbody, lpost))
      >:: L lbody
      >@ body_code
      >:: T (Br lcond)
      >:: L lpost )
  | Ast.For (inits, guard, after, body) ->
    let ds = List.map (fun d -> no_loc (Decl d)) inits in
    let ci, init = cmp_block tc c rt ds in
    let guard =
      match guard with
      | Some e -> e
      | None -> no_loc (CBool true)
    in
    let guard_ty, guard_op, guard_code = cmp_exp tc ci guard in
    let after =
      match after with
      | Some s -> [ s ]
      | None -> []
    in
    let lcond, lbody, lpost = gensym "cond", gensym "body", gensym "post" in
    let _, body_code = cmp_block tc ci rt body in
    let _, after_code = cmp_block tc ci rt after in
    ( c
    , init
      >:: T (Br lcond)
      >:: L lcond
      >@ guard_code
      >:: T (Cbr (guard_op, lbody, lpost))
      >:: L lbody
      >@ body_code
      >@ after_code
      >:: T (Br lcond)
      >:: L lpost )
  | Ast.Ret None -> c, [ T (Ret (Void, None)) ]
  | Ast.Ret (Some e) ->
    let op, code = cmp_exp_as tc c e rt in
    c, code >:: T (Ret (rt, Some op))
  | Ast.SCall (f, es) ->
    let _, op, code = cmp_call tc c f es in
    c, code

(* Compile a series of statements *)
and cmp_block (tc : TypeCtxt.t) (c : Ctxt.t) (rt : Ll.ty) (stmts : Ast.block)
  : Ctxt.t * stream
  =
  List.fold_left
    (fun (c, code) s ->
       let c, stmt_code = cmp_stmt tc c rt s in
       c, code >@ stmt_code)
    (c, [])
    stmts
;;

(* Construct the structure context for compilation.  We could reuse
   the H component from the Typechecker rather than recomputing this
   information here, but we do it this way to make the two parts of
   the project less interdependent.  *)
let get_struct_defns (p : Ast.prog) : TypeCtxt.t =
  List.fold_right
    (fun d ts ->
       match d with
       | Ast.Gtdecl { elt = id, fs } -> TypeCtxt.add ts id fs
       | _ -> ts)
    p
    TypeCtxt.empty
;;

(* Adds each function identifier to the context at an
   appropriately translated type.  

   NOTE: The Gid of a function is just its source name
*)
let cmp_function_ctxt (tc : TypeCtxt.t) (c : Ctxt.t) (p : Ast.prog) : Ctxt.t =
  List.fold_left
    (fun c -> function
       | Ast.Gfdecl { elt = { frtyp; fname; args } } ->
         let ft = TRef (RFun (List.map fst args, frtyp)) in
         Ctxt.add c fname (cmp_ty tc ft, Gid fname)
       | _ -> c)
    c
    p
;;

(* Populate a context with bindings for global variables 
   mapping OAT identifiers to LLVMlite gids and their types.

   Only a small subset of OAT expressions can be used as global initializers
   in well-formed programs. (The constructors starting with C and Id's 
   for global function values).
*)
let cmp_global_ctxt (tc : TypeCtxt.t) (c : Ctxt.t) (p : Ast.prog) : Ctxt.t =
  let gexp_ty c = function
    | Id id -> fst (Ctxt.lookup id c)
    | CStruct (t, cs) -> Ptr (Namedt t)
    | CNull r -> cmp_ty tc (TNullRef r)
    | CBool b -> I1
    | CInt i -> I64
    | CStr s -> Ptr I8
    | CArr (u, cs) -> Ptr (Struct [ I64; Array (0, cmp_ty tc u) ])
    | x ->
      failwith ("bad global initializer: " ^ Astlib.string_of_exp (no_loc x))
  in
  List.fold_left
    (fun c -> function
       | Ast.Gvdecl { elt = { name; init } } ->
         Ctxt.add c name (Ptr (gexp_ty c init.elt), Gid name)
       | _ -> c)
    c
    p
;;

(* Compile a function declaration in global context c. Return the LLVMlite cfg
   and a list of global declarations containing the string literals appearing
   in the function.
*)
let cmp_fdecl (tc : TypeCtxt.t) (c : Ctxt.t) (f : Ast.fdecl node)
  : Ll.fdecl * (Ll.gid * Ll.gdecl) list
  =
  let { frtyp; args; body } = f.elt in
  let add_arg (s_typ, s_id) (c, code, args) =
    let ll_id = gensym s_id in
    let ll_ty = cmp_ty tc s_typ in
    let alloca_id = gensym s_id in
    let c = Ctxt.add c s_id (Ptr ll_ty, Ll.Id alloca_id) in
    ( c
    , []
      >:: E (alloca_id, Alloca ll_ty)
      >:: I (gensym "store", Store (ll_ty, Id ll_id, Id alloca_id))
      >@ code
    , (ll_ty, ll_id) :: args )
  in
  let c, args_code, args = List.fold_right add_arg args (c, [], []) in
  let ll_rty = cmp_ret_ty tc frtyp in
  let _, block_code = cmp_block tc c ll_rty body in
  let argtys, f_param = List.split args in
  let f_ty = argtys, ll_rty in
  let return_code =
    let return_val =
      match frtyp with
      | RetVoid -> None
      | RetVal TBool | RetVal TInt -> Some (Const 0L)
      | RetVal (TRef _ | TNullRef _) -> Some Null
    in
    [ T (Ret (ll_rty, return_val)) ]
  in
  let f_cfg, globals =
    cfg_of_stream (args_code >@ block_code >@ return_code)
  in
  { f_ty; f_param; f_cfg }, globals
;;

(* Compile a global initializer, returning the resulting LLVMlite global
   declaration, and a list of additional global declarations.
*)
let rec cmp_gexp c (tc : TypeCtxt.t) (e : Ast.exp node)
  : Ll.gdecl * (Ll.gid * Ll.gdecl) list
  =
  match e.elt with
  | CNull r -> (cmp_ty tc (TNullRef r), GNull), []
  | CBool b -> (I1, if b then GInt 1L else GInt 0L), []
  | CInt i -> (I64, GInt i), []
  | Id id -> (fst @@ Ctxt.lookup id c, GGid id), []
  | CStr s ->
    let gid = gensym "str" in
    let ll_ty = str_arr_ty s in
    let cast = GBitcast (Ptr ll_ty, GGid gid, Ptr I8) in
    (Ptr I8, cast), [ gid, (ll_ty, GString s) ]
  | CArr (u, cs) ->
    let elts, gs =
      List.fold_right
        (fun cst (elts, gs) ->
           let gd, gs' = cmp_gexp c tc cst in
           gd :: elts, gs' @ gs)
        cs
        ([], [])
    in
    let len = List.length cs in
    let ll_u = cmp_ty tc u in
    let gid = gensym "global_arr" in
    let arr_t = Struct [ I64; Array (len, ll_u) ] in
    let arr_i =
      GStruct [ I64, GInt (Int64.of_int len); Array (len, ll_u), GArray elts ]
    in
    let final_t = Struct [ I64; Array (0, ll_u) ] in
    let cast = GBitcast (Ptr arr_t, GGid gid, Ptr final_t) in
    (Ptr final_t, cast), (gid, (arr_t, arr_i)) :: gs
  | CStruct (id, cs) ->
    let gid = gensym "global_st" in
    let fields = TypeCtxt.lookup id tc in
    let elts, gs, tys =
      List.fold_right
        (fun (fname, cst) (elts, gs, tys) ->
           let f_ty, _ = TypeCtxt.lookup_field_name id fname tc in
           let gd, gs' = cmp_gexp c tc cst in
           gd :: elts, gs' @ gs, cmp_ty tc f_ty :: tys)
        cs
        ([], [], [])
    in
    let final_t = Struct tys in
    let cast = GBitcast (Ptr final_t, GGid gid, Ptr (Namedt id)) in
    (Ptr final_t, cast), (gid, (final_t, GStruct elts)) :: gs
  | _ -> failwith "bad global initializer"
;;

(* Oat internals function context ------------------------------------------- *)
let internals =
  [ "oat_malloc", Ll.Fun ([ I64 ], Ptr I64)
  ; "oat_alloc_array", Ll.Fun ([ I64 ], Ptr I64)
  ; "oat_assert_not_null", Ll.Fun ([ Ptr I8 ], Void)
  ; "oat_assert_array_length", Ll.Fun ([ Ptr I64; I64 ], Void)
  ]
;;

(* Oat builtin function context --------------------------------------------- *)
let builtins =
  List.map
    (fun (fname, ftyp) ->
       let args, ret = cmp_fty TypeCtxt.empty ftyp in
       fname, Ll.Fun (args, ret))
    Typechecker.builtins
;;

let tctxt_to_tdecls c =
  List.map (fun (i, l) -> i, Struct (List.map (fun f -> cmp_ty c f.ftyp) l)) c
;;

(* Compile a OAT program to LLVMlite *)
let cmp_prog (p : Ast.prog) : Ll.prog =
  let tc = get_struct_defns p in
  (* add built-in functions to context *)
  let init_ctxt =
    List.fold_left
      (fun c (i, t) -> Ctxt.add c i (Ll.Ptr t, Gid i))
      Ctxt.empty
      builtins
  in
  let fc = cmp_function_ctxt tc init_ctxt p in
  (* build global variable context *)
  let c = cmp_global_ctxt tc fc p in
  (* compile functions and global variables *)
  let fdecls, gdecls =
    List.fold_right
      (fun d (fs, gs) ->
         match d with
         | Ast.Gvdecl { elt = gd } ->
           let ll_gd, gs' = cmp_gexp c tc gd.init in
           fs, ((gd.name, ll_gd) :: gs') @ gs
         | Ast.Gfdecl fd ->
           let fdecl, gs' = cmp_fdecl tc c fd in
           (fd.elt.fname, fdecl) :: fs, gs' @ gs
         | Ast.Gtdecl _ -> fs, gs)
      p
      ([], [])
  in
  (* gather external declarations *)
  let edecls = internals @ builtins in
  { tdecls = tctxt_to_tdecls tc; gdecls; fdecls; edecls }
;;
