open Ll
open Llutil
open Ast

(* This file is where much of the work of the project will be carried out.
   Follow the instructions on the project web site, but first skim through
   this file to see what it contains.
*)

(* instruction streams ------------------------------------------------------ *)

(* As in the last project, we'll be working with a flattened representation
   of LLVMlite programs to make emitting code easier. This version
   additionally makes it possible to emit elements that will be gathered up and
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

(* The type of streams of LLVMLite instructions. Note that to improve performance,
 * we will emit the instructions in reverse order. That is, the LLVMLite code:
 *     %1 = mul i64 2, 2
 *     %2 = add i64 1, %1
 *     br label %l1
 * would be constructed as a stream as follows:
 *     I ("1", Binop (Mul, I64, Const 2L, Const 2L))
 *     >:: I ("2", Binop (Add, I64, Const 1L, Id "1"))
 *     >:: T (Br "l1")
 *)
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

  (* Lookup a function, fail otherwise *)
  let lookup_function (id : Ast.id) (c : t) : Ll.ty * Ll.operand =
    match List.assoc id c with
    | Ptr (Fun (args, ret)), g -> Ptr (Fun (args, ret)), g
    | _ -> failwith @@ id ^ " not bound to a function"
  ;;

  let lookup_function_option (id : Ast.id) (c : t) : (Ll.ty * Ll.operand) option
    =
    try Some (lookup_function id c) with
    | _ -> None
  ;;
end

(* compiling OAT types ------------------------------------------------------ *)

(* The mapping of source types onto LLVMlite is straightforward. Booleans and ints
   are represented as the corresponding integer types. OAT strings are
   pointers to bytes (I8). Arrays are the most interesting type: they are
   represented as pointers to structs where the first component is the number
   of elements in the following array.

   The trickiest part of this project will be satisfying LLVM's rudimentary type
   system. Recall that global arrays in LLVMlite need to be declared with their
   length in the type to statically allocate the right amount of memory. The
   global strings and arrays you emit will therefore have a more specific type
   annotation than the output of cmp_rty. You will have to carefully bitcast
   gids to satisfy the LLVM type checker.
*)

let rec cmp_ty : Ast.ty -> Ll.ty = function
  | Ast.TBool -> I1
  | Ast.TInt -> I64
  | Ast.TRef r -> Ptr (cmp_rty r)

and cmp_rty : Ast.rty -> Ll.ty = function
  | Ast.RString -> I8
  | Ast.RArray u -> Struct [ I64; Array (0, cmp_ty u) ]
  | Ast.RFun (ts, t) ->
    let args, ret = cmp_fty (ts, t) in
    Fun (args, ret)

and cmp_ret_ty : Ast.ret_ty -> Ll.ty = function
  | Ast.RetVoid -> Void
  | Ast.RetVal t -> cmp_ty t

and cmp_fty (ts, r) : Ll.fty = List.map cmp_ty ts, cmp_ret_ty r

let cmp_ety : Ll.ty -> Ll.ty = function
  | Ptr (Struct [ I64; Array (0, t) ]) -> t
  | _ -> failwith "cmp_ety: not an array"
;;

let cmp_deref : Ll.ty -> Ll.ty = function
  | Ptr t -> t
  | _ -> failwith "cmp_deref: not a pointer"
;;

let rec print_type : Ll.ty -> unit = function
  | Void -> print_string "void"
  | I1 -> print_string "i1"
  | I8 -> print_string "i8"
  | I64 -> print_string "i64"
  | Ptr t ->
    print_string "ptr ";
    print_type t
  | Struct ts ->
    print_string "{";
    List.iter
      (fun t ->
        print_type t;
        print_string ", ")
      ts;
    print_string "}"
  | Array (n, t) ->
    Printf.printf "[%d x " n;
    print_type t;
    print_string "]"
  | Fun (ts, t) ->
    print_string "fun (";
    List.iter
      (fun t ->
        print_type t;
        print_string ", ")
      ts;
    print_string ") -> ";
    print_type t
  | Namedt s -> Printf.printf "%%%s" s
;;

(* | _ -> failwith "cmp_ety: not an array" *)

let typ_of_binop : Ast.binop -> Ast.ty * Ast.ty * Ast.ty = function
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> TInt, TInt, TInt
  | Eq | Neq | Lt | Lte | Gt | Gte -> TInt, TInt, TBool
  | And | Or -> TBool, TBool, TBool
;;

let typ_of_unop : Ast.unop -> Ast.ty * Ast.ty = function
  | Neg | Bitnot -> TInt, TInt
  | Lognot -> TBool, TBool
;;

(* Get the LLVMlite binary operator corresponding to an arithmetic binary operator *)
let opr_of_arith_bop : Ast.binop -> Ll.bop = function
  | Add -> Add
  | Mul -> Mul
  | Sub -> Sub
  | IAnd -> And
  | IOr -> Or
  | Shl -> Shl
  | Shr -> Lshr
  | Sar -> Ashr
  | _ -> failwith "opr_of_arth_bop: invalid arithmetic operator"
;;

(* Get the LLVMlite binary operator corresponding to a logical binary operator *)
let opr_of_logical_bop : Ast.binop -> Ll.bop = function
  | And -> And
  | Or -> Or
  | _ -> failwith "opr_of_logical_bop: invalid logical operator"
;;

(* Get the LLVMlite comparison operator corresponding to a comparison binary operator *)
let opr_of_cmp_bop : Ast.binop -> Ll.cnd = function
  | Eq -> Eq
  | Neq -> Ne
  | Lt -> Slt
  | Lte -> Sle
  | Gt -> Sgt
  | Gte -> Sge
  | _ -> failwith "opr_of_cmp_bop: invalid comparison operator"
;;

(* Compiler Invariants

   The LLVM IR type of a variable (whether global or local) that stores an Oat
   array value (or any other reference type, like "string") will always be a
   double pointer.  In general, any Oat variable of Oat-type t will be
   represented by an LLVM IR value of type Ptr (cmp_ty t).  So the Oat variable
   x : int will be represented by an LLVM IR value of type i64*, y : string will
   be represented by a value of type i8**, and arr : int[] will be represented
   by a value of type {i64, [0 x i64]}**.  Whether the LLVM IR type is a
   "single" or "double" pointer depends on whether t is a reference type.

   We can think of the compiler as paying careful attention to whether a piece
   of Oat syntax denotes the "value" of an expression or a pointer to the
   "storage space associated with it".  This is the distinction between an
   "expression" and the "left-hand-side" of an assignment statement.  Compiling
   an Oat variable identifier as an expression ("value") does the load, so
   cmp_exp called on an Oat variable of type t returns (code that) generates a
   LLVM IR value of type cmp_ty t.  Compiling an identifier as a left-hand-side
   does not do the load, so cmp_lhs called on an Oat variable of type t returns
   and operand of type (cmp_ty t)*.  Extending these invariants to account for
   array accesses: the assignment e1[e2] = e3; treats e1[e2] as a
   left-hand-side, so we compile it as follows: compile e1 as an expression to
   obtain an array value (which is of pointer of type {i64, [0 x s]}* ).
   compile e2 as an expression to obtain an operand of type i64, generate code
   that uses getelementptr to compute the offset from the array value, which is
   a pointer to the "storage space associated with e1[e2]".

   On the other hand, compiling e1[e2] as an expression (to obtain the value of
   the array), we can simply compile e1[e2] as a left-hand-side and then do the
   load.  So cmp_exp and cmp_lhs are mutually recursive.  [[Actually, as I am
   writing this, I think it could make sense to factor the Oat grammar in this
   way, which would make things clearerhw, I may do that for next time around.]]

 
   Consider globals7.oat (in hw4programs)

   /--------------- globals7.oat ------------------ 
   global arr = int[] null;

   int foo() { 
     var x = new int[3]; 
     arr = x; 
     x[2] = 3; 
     return arr[2]; 
   }
   /------------------------------------------------

   The translation (given by cmp_ty) of the type int[] is {i64, [0 x i64}* so
   the corresponding LLVM IR declaration will look like:

   @arr = global { i64, [0 x i64] }* null

   This means that the type of the LLVM IR identifier @arr is {i64, [0 x i64]}**
   which is consistent with the type of a locally-declared array variable.

   The local variable x would be allocated and initialized by (something like)
   the following code snippet.  Here %_x7 is the LLVM IR uid containing the
   pointer to the "storage space" for the Oat variable x.

   %_x7 = alloca { i64, [0 x i64] }*                              ;; (1)
   %_raw_array5 = call i64*  @oat_alloc_array(i64 3)              ;; (2)
   %_array6 = bitcast i64* %_raw_array5 to { i64, [0 x i64] }*    ;; (3)
   store { i64, [0 x i64]}* %_array6, { i64, [0 x i64] }** %_x7   ;; (4)

   (1) note that alloca uses cmp_ty (int[]) to find the type, so %_x7 has 
       the same type as @arr 

   (2) @oat_alloc_array allocates len+1 i64's 

   (3) we have to bitcast the result of @oat_alloc_array so we can store it
        in %_x7 

   (4) stores the resulting array value (itself a pointer) into %_x7 

  The assignment arr = x; gets compiled to (something like):

  %_x8 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** %_x7     ;; (5)
  store {i64, [0 x i64] }* %_x8, { i64, [0 x i64] }** @arr       ;; (6)

  (5) load the array value (a pointer) that is stored in the address pointed 
      to by %_x7 

  (6) store the array value (a pointer) into @arr 

  The assignment x[2] = 3; gets compiled to (something like):

  %_x9 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** %_x7      ;; (7)
  %_index_ptr11 = getelementptr { i64, [0 x  i64] }, 
                  { i64, [0 x i64] }* %_x9, i32 0, i32 1, i32 2   ;; (8)
  store i64 3, i64* %_index_ptr11                                 ;; (9)

  (7) as above, load the array value that is stored %_x7 

  (8) calculate the offset from the array using GEP

  (9) store 3 into the array

  Finally, return arr[2]; gets compiled to (something like) the following.
  Note that the way arr is treated is identical to x.  (Once we set up the
  translation, there is no difference between Oat globals and locals, except
  how their storage space is initially allocated.)

  %_arr12 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** @arr    ;; (10)
  %_index_ptr14 = getelementptr { i64, [0 x i64] },                
                 { i64, [0 x i64] }* %_arr12, i32 0, i32 1, i32 2  ;; (11)
  %_index15 = load i64, i64* %_index_ptr14                         ;; (12)
  ret i64 %_index15

  (10) just like for %_x9, load the array value that is stored in @arr 

  (11)  calculate the array index offset

  (12) load the array value at the index
*)

(* Global initialized arrays:

  There is another wrinkle: to compile global initialized arrays like in the
  globals4.oat, it is helpful to do a bitcast once at the global scope to
  convert the "precise type" required by the LLVM initializer to the actual
  translation type (which sets the array length to 0).  So for globals4.oat,
  the arr global would compile to (something like):

  @arr = global { i64, [0 x i64] }* bitcast 
           ({ i64, [4 x i64] }* @_global_arr5 to { i64, [0 x i64] }* ) 
  @_global_arr5 = global { i64, [4 x i64] } 
                  { i64 4, [4 x i64] [ i64 1, i64 2, i64 3, i64 4 ] }
*)

(* Some useful helper functions *)

(* Generate a fresh temporary identifier. Since OAT identifiers cannot begin
   with an underscore, these should not clash with any source variables *)
let gensym : string -> string =
  let c = ref 0 in
  fun (s : string) ->
    incr c;
    Printf.sprintf "_%s%d" s !c
;;

(* Generate a label *)
let genlbl : string -> string =
  let c = ref 0 in
  fun (s : string) ->
    incr c;
    Printf.sprintf "%s%d" s !c
;;

(* Amount of space an Oat type takes when stored in the satck, in bytes.
   Note that since structured values are manipulated by reference, all
   Oat values take 8 bytes on the stack.
*)
let size_oat_ty (t : Ast.ty) = 8L

(* Generate code to allocate a zero-initialized array of source type TRef (RArray t) of the
   given size. Note "size" is an operand whose value can be computed at
   runtime *)
let oat_alloc_array (t : Ast.ty) (size : Ll.operand) : Ll.ty * operand * stream =
  let ans_id, arr_id = gensym "array", gensym "raw_array" in
  let ans_ty = cmp_ty @@ TRef (RArray t) in
  let arr_ty = Ptr I64 in
  ( ans_ty
  , Id ans_id
  , lift
      [ arr_id, Call (arr_ty, Gid "oat_alloc_array", [ I64, size ])
      ; ans_id, Bitcast (arr_ty, Id arr_id, ans_ty)
      ] )
;;

(* Compiles 3 types of binary operations: arithmetic, logical, and comparison.
   The operands are assumed to have the same type. *)

let cmp_binop
  (b : Ast.binop)
  (ty : Ll.ty)
  (op1 : Ll.operand)
  (op2 : Ll.operand)
  (res : Ll.uid)
  : stream
  =
  match b with
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr ->
    [ I (res, Binop (opr_of_arith_bop b, ty, op1, op2)) ]
  | Eq | Neq | Lt | Lte | Gt | Gte ->
    [ I (res, Icmp (opr_of_cmp_bop b, ty, op1, op2)) ]
  | And | Or -> [ I (res, Binop (opr_of_logical_bop b, ty, op1, op2)) ]
;;

(* Compiles a left-hand-side expression in context c, outputting the Ll operand
   that will recieve the address of the expression, and the stream of instructions
   implementing the expression.
*)
let rec cmp_lhs (c : Ctxt.t) (exp : Ast.exp node) : Ll.ty * Ll.operand * stream =
  match exp.elt with
  | Id id ->
    let ty, op = Ctxt.lookup id c in
    ty, op, []
  (* | Index ({ elt = Id arr }, exp) ->
    let ty, op = Ctxt.lookup arr c in
    let ty' = cmp_deref ty in
    let arr = gensym "load" in
    let ety = cmp_ety ty' in
    let _, op', s = cmp_exp c exp in
    let result = gensym "index" in
    ( Ptr ety
    , Id result
    , s
      >:: I (arr, Load (ty, op))
      >:: I (result, Gep (ty', Id arr, [ Const 0L; Const 1L; op' ])) ) *)
  | Index (base, idx) ->
    let ty, bop, bs = cmp_exp c base in
    (* print_type ty; *)
    (* print_endline ""; *)
    let ety = cmp_ety ty in
    (* print_type ety; *)
    let _, iop, is = cmp_exp c idx in
    let result = gensym "index" in
    ( Ptr ety
    , Id result
    , bs >@ is >:: I (result, Gep (ty, bop, [ Const 0L; Const 1L; iop ])) )
    (* let _, op, s = cmp_lhs c base in
       cmp_lhs c (no_loc (Index (no_loc (Id op), idx))) *)
  | _ -> failwith "cmp_lhs: invalid left-hand-side"
(* | _ -> print_string "cmp_lhs: invalid left-hand-side"; Ptr Void, Null, [] *)

(* Compiles an expression exp in context c, outputting the Ll operand that will
   recieve the value of the expression, and the stream of instructions
   implementing the expression.

   Tips:
   - use the provided cmp_ty function!

   - string literals (CStr s) should be hoisted. You'll need to make sure
     either that the resulting gid has type (Ptr I8), or, if the gid has type
     [n x i8] (where n is the length of the string), convert the gid to a
     (Ptr I8), e.g., by using getelementptr.

   - use the provided "oat_alloc_array" function to implement literal arrays
     (CArr) and the (NewArr) expressions
*)
and cmp_exp (c : Ctxt.t) (exp : Ast.exp node) : Ll.ty * Ll.operand * stream =
  match exp.elt with
  | CNull rty -> Ptr (cmp_rty rty), Null, []
  | CBool x -> if x then I1, Const 1L, [] else I1, Const 0L, []
  | CInt x -> I64, Const x, []
  | CStr s ->
    let lit_gid = gensym "str_lit" in
    ( Ptr I8
    , Gid lit_gid
    , [ G (lit_gid, (Array (String.length s + 1, I8), GString s)) ] )
  | CArr (t, es) ->
    let ty, op, s =
      oat_alloc_array t (Const (Int64.of_int @@ List.length es))
    in
    let tmp = gensym "tmp" in
    let c' = Ctxt.add c tmp (Ptr ty, Id tmp) in
    let cmp_elt_assn (idx : int64) (exp : exp node) : stream =
      let _, eop, s1 = cmp_exp c exp in
      let _, dst, s2 =
        cmp_lhs c' (no_loc (Index (no_loc (Id tmp), no_loc (CInt idx))))
      in
      s1 >@ s2 >:: I ("", Store (cmp_ty t, eop, dst))
    in
    let _, assns =
      List.fold_left
        (fun (acc, ss) e -> Int64.succ acc, ss >@ cmp_elt_assn acc e)
        (0L, [])
        es
    in
    ty, op, s >:: I (tmp, Alloca ty) >:: I ("", Store (ty, op, Id tmp)) >@ assns
  | NewArr (t, e) ->
    let _, sz, sizes = cmp_exp c e in
    let ty, op, s = oat_alloc_array t sz in
    let tmp = gensym "tmp" in
    let c' = Ctxt.add c tmp (Ptr ty, Id tmp) in
    let oatsz = gensym "oatsz" in
    let c'' = Ctxt.add c' oatsz (Ptr I64, Id oatsz) in
    let i = gensym "i" in
    let _, fors =
      cmp_stmt
        c''
        Void
        (no_loc
           (For
              ( [ i, no_loc (CInt 0L) ]
              , Some (no_loc (Bop (Lt, no_loc (Id i), no_loc (Id oatsz))))
              , Some
                  (no_loc
                     (Assn
                        ( no_loc (Id i)
                        , no_loc (Bop (Add, no_loc (Id i), no_loc (CInt 1L))) )))
              , [ no_loc
                    (Assn
                       ( no_loc (Index (no_loc (Id tmp), no_loc (Id i)))
                       , no_loc (CInt 0L) ))
                ] )))
    in
    ( ty
    , op
    , sizes
      >@ s
      >:: I (tmp, Alloca ty)
      >:: I (oatsz, Alloca I64)
      >:: I ("", Store (ty, op, Id tmp))
      >:: I ("", Store (I64, sz, Id oatsz))
      >@ fors )
  (*
     (* let _, sz, s1 = cmp_exp c e in
     let ty, op, s2 = cmp_exp c (no_loc (CArr ())) in
     ty, op, s1 >@ s2 *)
     (* TODO: create a foor loop for default initialization of each elements *)
     For (
     (* no_loc (Decl (tmp, e)),
     no_loc (Bop (Lt, Id tmp, e)),
     no_loc (Uop (Neg, Id tmp)),
     no_loc (Assn (Index (no_loc (Id tmp), e), CInt 0L) *)
     )
     ) *)
  (*
     let ty, op, s =
      oat_alloc_array t (Const (Int64.of_int @@ List.length es))
    in
    let tmp = gensym "tmp" in
    let c' = Ctxt.add c tmp (Ptr ty, Id tmp) in
    let cmp_elt_assn (idx : int64) : stream =
      let _, dst, s2 =
        cmp_lhs c' (no_loc (Index (no_loc (Id tmp), no_loc (CInt idx))))
      in
      s1 >@ s2 >:: I ("", Store (cmp_ty t, (Const 0L), dst))
    in
    let _, assns =
      List.fold_left
        (fun (acc, ss) e -> Int64.succ acc, ss >@ cmp_elt_assn acc e)
        (0L, [])
        es
    in
    ty, op, s >:: I (tmp, Alloca ty) >:: I ("", Store (ty, op, Id tmp)) >@ assns *)
  | Id x ->
    let x' = gensym "exp" in
    let ty, op = Ctxt.lookup x c in
    cmp_deref ty, Id x', [ I (x', Load (ty, op)) ]
  | Index _ ->
    (* TODO *)
    let ty, dst, s = cmp_lhs c exp in
    let result = gensym "index_load" in
    cmp_deref ty, Id result, s >:: I (result, Load (ty, dst))
  | Call (e, es) -> failwith "cmp_exp Call not implemented"
  | Bop (b, e1, e2) ->
    let res = gensym "bop" in
    let _, _, res_ty = typ_of_binop b in
    let op_ty, op1, op1_code = cmp_exp c e1 in
    let _, op2, op2_code = cmp_exp c e2 in
    ( cmp_ty res_ty
    , Ll.Id res
    , op1_code >@ op2_code >@ cmp_binop b op_ty op1 op2 res )
  | Uop (u, e) ->
    let res = gensym "uop" in
    let _, op, op_code = cmp_exp c e in
    (match u with
     | Neg -> I64, Ll.Id res, op_code >:: I (res, Binop (Sub, I64, Const 0L, op))
     | Lognot ->
       I1, Ll.Id res, op_code >:: I (res, Binop (Xor, I1, Const 1L, op))
     | Bitnot ->
       I64, Ll.Id res, op_code >:: I (res, Binop (Xor, I64, Const (-1L), op)))

(* Compile a statement in context c with return typ rt. Return a new context,
   possibly extended with new local bindings, and the instruction stream
   implementing the statement.

   Left-hand-sides of assignment statements must either be OAT identifiers,
   or an index into some arbitrary expression of array type. Otherwise, the
   program is not well-formed and your compiler may throw an error.

   Tips:
   - for local variable declarations, you will need to emit Allocas in the
     entry block of the current function using the E() constructor.

   - don't forget to add a bindings to the context for local variable
     declarations

   - you can avoid some work by translating For loops to the corresponding
     While loop, building the AST and recursively calling cmp_stmt

   - you might find it helpful to reuse the code you wrote for the Call
     expression to implement the SCall statement

   - compiling the left-hand-side of an assignment is almost exactly like
     compiling the Id or Index expression. Instead of loading the resulting
     pointer, you just need to store to it!
*)
and cmp_stmt (c : Ctxt.t) (rt : Ll.ty) (stmt : Ast.stmt node) : Ctxt.t * stream =
  match stmt.elt with
  | Assn (lhs, rhs) ->
    let _, lop, ls = cmp_lhs c lhs in
    let rty, rop, rs = cmp_exp c rhs in
    c, rs >@ ls >:: I (gensym "store", Store (rty, rop, lop))
  | Decl (id, elt) ->
    let ty, op, s = cmp_exp c elt in
    ( Ctxt.add c id (Ptr ty, Id id)
    , s >:: E (id, Alloca ty) >:: I ("", Store (ty, op, Id id)) )
  | Ret None -> c, [ T (Ret (rt, None)) ]
  | Ret (Some elt) ->
    let _, op, stream = cmp_exp c elt in
    c, stream >@ [ T (Ret (rt, Some op)) ]
  | If (cond, tbr, fbr) ->
    let if_cond = gensym "cond" in
    let tbr' = genlbl "tbr" in
    let fbr' = genlbl "fbr" in
    let if_end = genlbl "if_end" in
    let ty, cond', conds = cmp_exp c cond in
    let _, tbr = cmp_block c rt tbr in
    let _, fbr = cmp_block c rt fbr in
    ( c
    , conds
      >:: I (if_cond, Icmp (Eq, ty, Const 1L, cond'))
      >:: T (Cbr (Id if_cond, tbr', fbr'))
      >:: L tbr'
      >@ tbr
      >:: T (Br if_end)
      >:: L fbr'
      >@ fbr
      >:: T (Br if_end)
      >:: L if_end )
  | For (vdecls, cond, last, blk) ->
    let cond' = Option.value cond ~default:(no_loc (CBool true)) in
    let last' = Option.value (Option.map (fun x -> [ x ]) last) ~default:[] in
    let body = blk @ last' in
    ( c
    , snd
      @@ cmp_block
           c
           rt
           (List.map no_loc
            @@ List.map (fun vdecl -> Decl vdecl) vdecls
            @ [ While (cond', body) ]) )
  | While (exp, blk) ->
    let loop_cond = genlbl "loop_cond" in
    let cond_chk = gensym "cond" in
    let loop_body = genlbl "loop_body" in
    let loop_end = genlbl "loop_end" in
    let ty, cond, conds = cmp_exp c exp in
    let _, blks = cmp_block c rt blk in
    ( c
    , [ T (Br loop_cond) ]
      >:: L loop_cond
      >@ conds
      >:: I (cond_chk, Icmp (Eq, ty, Const 0L, cond))
      >:: T (Cbr (Id cond_chk, loop_end, loop_body))
      >:: L loop_body
      >@ blks
      >:: T (Br loop_cond)
      >:: L loop_end )
  | _ -> failwith "cmp_stmt not implemented"

(* Compile a series of statements *)
and cmp_block (c : Ctxt.t) (rt : Ll.ty) (stmts : Ast.block) : Ctxt.t * stream =
  List.fold_left
    (fun (c, code) s ->
      let c, stmt_code = cmp_stmt c rt s in
      c, code >@ stmt_code)
    (c, [])
    stmts
;;

(* Adds each function identifer to the context at an
   appropriately translated type.

   NOTE: The Gid of a function is just its source name
*)
let cmp_function_ctxt (c : Ctxt.t) (p : Ast.prog) : Ctxt.t =
  List.fold_left
    (fun c -> function
      | Ast.Gfdecl { elt = { frtyp; fname; args } } ->
        let ft = TRef (RFun (List.map fst args, frtyp)) in
        Ctxt.add c fname (cmp_ty ft, Gid fname)
      | _ -> c)
    c
    p
;;

(* Populate a context with bindings for global variables
   mapping OAT identifiers to LLVMlite gids and their types.

   Only a small subset of OAT expressions can be used as global initializers
   in well-formed programs. (The constructors starting with C).
*)
let cmp_global_ctxt (c : Ctxt.t) (p : Ast.prog) : Ctxt.t =
  let open Ast in
  let type_of_exp (exp : exp node) : ty =
    match exp.elt with
    | CNull rty -> TRef rty
    | CBool _ -> TBool
    | CInt _ -> TInt
    | CStr _ -> TRef RString
    | CArr (t, _) -> TRef (RArray t)
    | NewArr (t, _) -> TRef (RArray t)
    | _ -> failwith "cmp_global_ctxt: invalid initializer"
  in
  List.fold_left
    (fun c -> function
      | Ast.Gvdecl { elt = { name; init } } ->
        Ctxt.add c name (Ptr (cmp_ty (type_of_exp init)), Gid name)
      | _ -> c)
    c
    p
;;

(* Compile a function declaration in global context c. Return the LLVMlite cfg
   and a list of global declarations containing the string literals appearing
   in the function.

   You will need to
   1. Allocate stack space for the function parameters using Alloca
   2. Store the function arguments in their corresponding alloca'd stack slot
   3. Extend the context with bindings for function variables
   4. Compile the body of the function using cmp_block
   5. Use cfg_of_stream to produce a LLVMlite cfg from
*)
let cmp_fdecl (c : Ctxt.t) (f : Ast.fdecl node)
  : Ll.fdecl * (Ll.gid * Ll.gdecl) list
  =
  let { elt = { frtyp; args; body } } = f in
  let f_ty = List.map (fun (arg, _) -> cmp_ty arg) args, cmp_ret_ty frtyp in
  let f_param = List.map snd args in
  (* TODO:
     1. allocate stack space for function parameters and store them
     2. extend the context with bindings for function variables
     3. Not sure whether the following is correct
  *)
  let f_cfg, gdecls =
    cfg_of_stream (snd @@ cmp_block c (cmp_ret_ty frtyp) body)
  in
  let fdecl = { f_ty; f_param; f_cfg } in
  fdecl, gdecls
;;

(* Compile a global initializer, returning the resulting LLVMlite global
   declaration, and a list of additional global declarations.

   Tips:
   - Only CNull, CBool, CInt, CStr, and CArr can appear as global initializers
     in well-formed OAT programs. Your compiler may throw an error for the other
     cases

   - OAT arrays are always handled via pointers. A global array of arrays will
     be an array of pointers to arrays emitted as additional global declarations.
*)
let rec cmp_gexp c (e : Ast.exp node) : Ll.gdecl * (Ll.gid * Ll.gdecl) list =
  match e.elt with
  | CNull rty -> (Ptr (cmp_rty rty), GNull), []
  | CBool x -> (I1, GInt (if x then 1L else 0L)), []
  | CInt x -> (I64, GInt x), []
  | CStr s -> (Array (String.length s + 1, I8), GString s), []
  | CArr (t, es) ->
    let len = List.length es in
    let elem_ty = cmp_ty t in
    let data_arr_ty = Array (len, elem_ty) in
    let arr_ty = Struct [ I64; data_arr_ty ] in
    let real_array = gensym "real_array" in
    (* TODO:
       1. cmp_gexp for each element
       2. if element is an array, give it a name
       3. put the decls of subarrays in the list of global declarations
       4. put ptrs to subarrays in the list of main array decls
    *)
    ( (Ptr arr_ty, GGid real_array)
    , [ (* optional subarray decls with name *)
        ( real_array
        , ( arr_ty
          , GStruct
              [ I64, GInt (Int64.of_int len)
              ; ( data_arr_ty
                , GArray
                    (* ptrs to subarrays or just the elements *)
                    (List.map (fun ee -> fst @@ cmp_gexp c ee) es) )
              ] ) )
      ] )
  | _ -> failwith "cmp_gexp: invalid global initializer"
;;

(* Oat internals function context ------------------------------------------- *)
let internals = [ "oat_alloc_array", Ll.Fun ([ I64 ], Ptr I64) ]

(* Oat builtin function context --------------------------------------------- *)
let builtins =
  [ ( "array_of_string"
    , cmp_rty @@ RFun ([ TRef RString ], RetVal (TRef (RArray TInt))) )
  ; ( "string_of_array"
    , cmp_rty @@ RFun ([ TRef (RArray TInt) ], RetVal (TRef RString)) )
  ; "length_of_string", cmp_rty @@ RFun ([ TRef RString ], RetVal TInt)
  ; "string_of_int", cmp_rty @@ RFun ([ TInt ], RetVal (TRef RString))
  ; ( "string_cat"
    , cmp_rty @@ RFun ([ TRef RString; TRef RString ], RetVal (TRef RString)) )
  ; "print_string", cmp_rty @@ RFun ([ TRef RString ], RetVoid)
  ; "print_int", cmp_rty @@ RFun ([ TInt ], RetVoid)
  ; "print_bool", cmp_rty @@ RFun ([ TBool ], RetVoid)
  ]
;;

(* Compile a OAT program to LLVMlite *)
let cmp_prog (p : Ast.prog) : Ll.prog =
  (* add built-in functions to context *)
  let init_ctxt =
    List.fold_left
      (fun c (i, t) -> Ctxt.add c i (Ll.Ptr t, Gid i))
      Ctxt.empty
      builtins
  in
  let fc = cmp_function_ctxt init_ctxt p in
  (* build global variable context *)
  let c = cmp_global_ctxt fc p in
  (* compile functions and global variables *)
  let fdecls, gdecls =
    List.fold_right
      (fun d (fs, gs) ->
        match d with
        | Ast.Gvdecl { elt = gd } ->
          let ll_gd, gs' = cmp_gexp c gd.init in
          fs, ((gd.name, ll_gd) :: gs') @ gs
        | Ast.Gfdecl fd ->
          let fdecl, gs' = cmp_fdecl c fd in
          (fd.elt.fname, fdecl) :: fs, gs' @ gs)
      p
      ([], [])
  in
  (* gather external declarations *)
  let edecls = internals @ builtins in
  { tdecls = []; gdecls; fdecls; edecls }
;;
