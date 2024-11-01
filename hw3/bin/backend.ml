(* ll ir compilation -------------------------------------------------------- *)

open Ll
open X86
module Platform = Util.Platform

(* Overview ----------------------------------------------------------------- *)

(* We suggest that you spend some time understanding this entire file and
   how it fits with the compiler pipeline before making changes.  The suggested
   plan for implementing the compiler is provided on the project web page.
*)

(* helpers ------------------------------------------------------------------ *)

(* Map LL comparison operations to X86 condition codes *)
let compile_cnd = function
  | Ll.Eq -> X86.Eq
  | Ll.Ne -> X86.Neq
  | Ll.Slt -> X86.Lt
  | Ll.Sle -> X86.Le
  | Ll.Sgt -> X86.Gt
  | Ll.Sge -> X86.Ge
;;

(* locals and layout -------------------------------------------------------- *)

(* One key problem in compiling the LLVM IR is how to map its local
   identifiers to X86 abstractions.  For the best performance, one
   would want to use an X86 register for each LLVM %uid.  However,
   since there are an unlimited number of %uids and only 16 registers,
   doing so effectively is quite difficult.  We will see later in the
   course how _register allocation_ algorithms can do a good job at
   this.

   A simpler, but less performant, implementation is to map each %uid
   in the LLVM source to a _stack slot_ (i.e. a region of memory in
   the stack).  Since LLVMlite, unlike real LLVM, permits %uid locals
   to store only 64-bit data, each stack slot is an 8-byte value.

   [ NOTE: For compiling LLVMlite, even i1 data values should be
   represented as a 8-byte quad. This greatly simplifies code
   generation. ]

   We call the datastructure that maps each %uid to its stack slot a
   'stack layout'.  A stack layout maps a uid to an X86 operand for
   accessing its contents.  For this compilation strategy, the operand
   is always an offset from %rbp (in bytes) that represents a storage slot in
   the stack.
*)

type layout = (uid * X86.operand) list

(* A context contains the global type declarations (needed for getelementptr
   calculations) and a stack layout. *)
type ctxt =
  { tdecls : (tid * ty) list
  ; layout : layout
  }

(* useful for looking up items in tdecls or layouts *)
let lookup m x = List.assoc x m

(* compiling operands  ------------------------------------------------------ *)

(* LLVM IR instructions support several kinds of operands.

   LL local %uids live in stack slots, whereas global ids live at
   global addresses that must be computed from a label.  Constants are
   immediately available, and the operand Null is the 64-bit 0 value.

   NOTE: two important facts about global identifiers:

   (1) You should use (Platform.mangle gid) to obtain a string
   suitable for naming a global label on your platform (OS X expects
   "_main" while linux expects "main").

   (2) 64-bit assembly labels are not allowed as immediate operands.
   That is, the X86 code: movq _gid %rax which looks like it should
   put the address denoted by _gid into %rax is not allowed.
   Instead, you need to compute an %rip-relative address using the
   leaq instruction:   leaq _gid(%rip) %rax.

   One strategy for compiling instruction operands is to use a
   designated register (or registers) for holding the values being
   manipulated by the LLVM IR instruction. You might find it useful to
   implement the following helper function, whose job is to generate
   the X86 instruction that moves an LLVM operand into a designated
   destination (usually a register).
*)
let compile_operand (ctxt : ctxt) (dest : X86.operand) : Ll.operand -> ins
  = function
  | Null -> Movq, [ Imm (Lit 0L); dest ]
  | Const i -> Movq, [ Imm (Lit i); dest ]
  | Gid gid -> Leaq, [ Ind3 (Lbl (Platform.mangle gid), Rip); dest ]
  | Id uid -> Movq, [ lookup ctxt.layout uid; dest ]
;;

(* compiling call  ---------------------------------------------------------- *)

(* You will probably find it helpful to implement a helper function that
   generates code for the LLVM IR call instruction.

   The code you generate should follow the x64 System V AMD64 ABI
   calling conventions, which places the first six 64-bit (or smaller)
   values in registers and pushes the rest onto the stack.  Note that,
   since all LLVM IR operands are 64-bit values, the first six
   operands will always be placed in registers.  (See the notes about
   compiling fdecl below.)

   [ NOTE: Don't forget to preserve caller-save registers (only if needed). ]

   [ NOTE: Remember, call can use labels as immediates! You shouldn't need to 
     perform any RIP-relative addressing for this one. ]

   [ NOTE: It is the caller's responsibility to clean up arguments pushed onto
     the stack, so you must free the stack space after the call returns. (But 
     see below about alignment.) ]

   [ NOTE: One important detail about the ABI besides the conventions is that, 
  at the time the [callq] instruction is invoked, %rsp *must* be 16-byte aligned.  
  However, because LLVM IR provides the Alloca instruction, which can dynamically
  allocate space on the stack, it is hard to know statically whether %rsp meets
  this alignment requirement.  Moroever: since, according to the calling 
  conventions, stack arguments numbered > 6 are pushed to the stack, we must take
  that into account when enforcing the alignment property.  

  We suggest that, for a first pass, you *ignore* %rsp alignment -- only a few of 
  the test cases rely on this behavior.  Once you have everything else working,
  you can enforce proper stack alignment at the call instructions by doing 
  these steps: 
    1. *before* pushing any arguments of the call to the stack, ensure that the
    %rsp is 16-byte aligned.  You can achieve that with the x86 instruction:
    `andq $-16, %rsp`  (which zeros out the lower 4 bits of %rsp, possibly 
    "allocating" unused padding space on the stack)

    2. if there are an *odd* number of arguments that will be pushed to the stack
    (which would break the 16-byte alignment because stack slots are 8 bytes),
    allocate an extra 8 bytes of padding on the stack. 
    
    3. follow the usual calling conventions - any stack arguments will still leave
    %rsp 16-byte aligned

    4. after the call returns, in addition to freeing up the stack slots used by
    arguments, if there were an odd number of slots, also free the extra padding. 
    
  ]
*)

(* compiling getelementptr (gep)  ------------------------------------------- *)

(* The getelementptr instruction computes an address by indexing into
   a datastructure, following a path of offsets.  It computes the
   address based on the size of the data, which is dictated by the
   data's type.

   To compile getelementptr, you must generate x86 code that performs
   the appropriate arithmetic calculations.
*)

(* [size_ty] maps an LLVMlite type to a size in bytes.
   (needed for getelementptr)

   - the size of a struct is the sum of the sizes of each component
   - the size of an array of t's with n elements is n * the size of t
   - all pointers, I1, and I64 are 8 bytes
   - the size of a named type is the size of its definition

   - Void, i8, and functions have undefined sizes according to LLVMlite.
     Your function should simply return 0 in those cases
*)
let rec size_ty (tdecls : (tid * ty) list) (t : Ll.ty) : int =
  match t with
  | Void | I8 | Fun _ -> 0
  | I1 | I64 | Ptr _ -> 8
  | Struct ts -> List.fold_left (fun acc t -> acc + size_ty tdecls t) 0 ts
  | Array (n, t) -> n * size_ty tdecls t
  | Namedt tid -> size_ty tdecls (lookup tdecls tid)
;;

(* Generates code that computes a pointer value.

   1. op must be of pointer type: t*

   2. the value of op is the base address of the calculation

   3. the first index in the path is treated as the index into an array
   of elements of type t located at the base address

   4. subsequent indices are interpreted according to the type t:

   - if t is a struct, the index must be a constant n and it
     picks out the n'th element of the struct. [ NOTE: the offset
       within the struct of the n'th element is determined by the
       sizes of the types of the previous elements ]

   - if t is an array, the index can be any operand, and its
     value determines the offset within the array.

   - if t is any other type, the path is invalid

   5. if the index is valid, the remainder of the path is computed as
   in (4), but relative to the type f the sub-element picked out
   by the path so far
*)
let compile_gep (ctxt : ctxt) (op : Ll.ty * Ll.operand) (path : Ll.operand list)
  : ins list
  =
  failwith "compile_gep not implemented"
;;

(* compiling instructions  -------------------------------------------------- *)

let rec loadable (ctxt : ctxt) : ty -> bool = function
  | Ptr _ -> true
  | Namedt t -> loadable ctxt @@ lookup ctxt.tdecls t
  | _ -> false
;;

let callable : Ll.operand -> bool = function
  | Gid _ -> true
  | Id _ -> true
  | _ -> false
;;

let prepare_arg (ctxt : ctxt) (n : int) (arg : Ll.operand) : ins list =
  let open Asm in
  let arg_regs = [ Rdi; Rsi; Rdx; Rcx; R08; R09 ] in
  match n with
  | n when n < 6 -> [ compile_operand ctxt (Reg (List.nth arg_regs n)) arg ]
  | _ -> [ compile_operand ctxt ~%Rax arg; Pushq, [ ~%Rax ] ]
;;

let rec prepare_args (ctxt : ctxt) (n : int)
  : (ty * Ll.operand) list -> ins list
  = function
  | [] -> []
  | (_, arg) :: args -> prepare_args ctxt (succ n) args @ prepare_arg ctxt n arg
;;

(* The result of compiling a single LLVM instruction might be many x86
   instructions.  We have not determined the structure of this code
   for you. Some of the instructions require only a couple of assembly
   instructions, while others require more.  We have suggested that
   you need at least compile_operand, compile_call, and compile_gep
   helpers; you may introduce more as you see fit.

   Here are a few notes:

   - Icmp:  the Setb instruction may be of use.  Depending on how you
     compile Cbr, you may want to ensure that the value produced by
     Icmp is exactly 0 or 1.

   - Load & Store: these need to dereference the pointers. Const and
     Null operands aren't valid pointers.  Don't forget to
     Platform.mangle the global identifier.

   - Alloca: needs to return a pointer into the stack

   - Bitcast: does nothing interesting at the assembly level
*)
let rec compile_insn (ctxt : ctxt) ((uid : uid), (i : Ll.insn)) : X86.ins list =
  let open Asm in
  match i with
  | Binop (bop, _, lhs, rhs) ->
    [ compile_operand ctxt ~%Rax lhs
    ; compile_operand ctxt ~%Rcx rhs
    ; ( (match bop with
         | Add -> Addq
         | Sub -> Subq
         | Mul -> Imulq
         | Shl -> Shlq
         | Lshr -> Shrq
         | Ashr -> Sarq
         | And -> Andq
         | Or -> Orq
         | Xor -> Xorq)
      , [ ~%Rcx; ~%Rax ] )
    ; Movq, [ ~%Rax; lookup ctxt.layout uid ]
    ]
  | Alloca _ ->
    [ Subq, [ ~$8; ~%Rsp ]; Movq, [ ~%Rsp; lookup ctxt.layout uid ] ]
  | Load (t, Gid gid) when loadable ctxt t ->
    [ Movq, [ Ind3 (Lbl (Platform.mangle gid), Rip); ~%Rax ]
    ; Movq, [ ~%Rax; lookup ctxt.layout uid ]
    ]
  | Load (t, Id id) when loadable ctxt t ->
    [ Movq, [ lookup ctxt.layout id; ~%Rax ]
    ; Movq, [ Ind2 Rax; ~%Rax ]
    ; Movq, [ ~%Rax; lookup ctxt.layout uid ]
    ]
  | Store (_, op, Gid gid) ->
    [ compile_operand ctxt ~%Rax op
    ; Movq, [ ~%Rax; Ind3 (Lbl (Platform.mangle gid), Rip) ]
    ]
  | Store (_, op, Id id) ->
    [ compile_operand ctxt ~%Rax op; Movq, [ ~%Rax; lookup ctxt.layout id ] ]
  | Icmp (cnd, _, lhs, rhs) ->
    [ compile_operand ctxt ~%Rax lhs
    ; compile_operand ctxt ~%Rcx rhs
    ; Xorq, [ ~%Rdx; ~%Rdx ]
    ; Cmpq, [ ~%Rcx; ~%Rax ]
    ; Set (compile_cnd cnd), [ ~%Rdx ]
    ; Movq, [ ~%Rdx; lookup ctxt.layout uid ]
    ]
  | Call (Void, op, args) when callable op ->
    prepare_args ctxt 0 args
    @ [ compile_operand ctxt ~%Rax op; Callq, [ ~%Rax ] ]
  | Call (_, op, args) ->
    compile_insn ctxt (uid, Call (Void, op, args))
    @ [ Movq, [ ~%Rax; lookup ctxt.layout uid ] ]
  | Bitcast (_, op, _) ->
    [ compile_operand ctxt ~%Rax op; Movq, [ ~%Rax; lookup ctxt.layout uid ] ]
  | Gep (t, op, path) -> compile_gep ctxt (t, op) path
  | _ -> failwith "compile_insn not implemented"
;;

(* compiling terminators  --------------------------------------------------- *)

(* prefix the function name [fn] to a label to ensure that the X86 labels are
   globally unique . *)
let mk_lbl (fn : string) (l : string) = fn ^ "." ^ l

(* Compile block terminators is not too difficult:

   - Ret should properly exit the function: freeing stack space,
     restoring the value of %rbp, and putting the return value (if
     any) in %rax.

   - Br should jump

   - Cbr branch should treat its operand as a boolean conditional

   [fn] - the name of the function containing this terminator
*)
let compile_terminator (fn : string) (ctxt : ctxt) (t : Ll.terminator)
  : ins list
  =
  let open Asm in
  match t with
  | Ret (_, Some op) ->
    [ compile_operand ctxt ~%Rax op
    ; Movq, [ ~%Rbp; ~%Rsp ]
    ; Popq, [ ~%Rbp ]
    ; Retq, []
    ]
  | Ret (_, None) -> [ Movq, [ ~%Rbp; ~%Rsp ]; Popq, [ ~%Rbp ]; Retq, [] ]
  | Br lbl -> [ Jmp, [ ~$$(mk_lbl fn lbl) ] ]
  | Cbr (op, l1, l2) ->
    [ compile_operand ctxt ~%Rax op
    ; Cmpq, [ ~$1; ~%Rax ]
    ; J Eq, [ ~$$(mk_lbl fn l1) ]
    ; Jmp, [ ~$$(mk_lbl fn l2) ]
    ]
;;

(* compiling blocks --------------------------------------------------------- *)

(* We have left this helper function here for you to complete.
   [fn] - the name of the function containing this block
   [ctxt] - the current context
   [blk]  - LLVM IR code for the block
*)
let compile_block (fn : string) (ctxt : ctxt) (blk : Ll.block) : ins list =
  List.concat_map (compile_insn ctxt) blk.insns
  @ compile_terminator fn ctxt (snd blk.term)
;;

let compile_lbl_block fn lbl ctxt blk : elem =
  Asm.text (mk_lbl fn lbl) (compile_block fn ctxt blk)
;;

(* compile_fdecl ------------------------------------------------------------ *)

(* Complete this helper function, which computes the location of the nth incoming
   function argument: either in a register or relative to %rbp,
   according to the calling conventions. We will test this function as part of
   the hidden test cases.

   You might find it useful for compile_fdecl.

   [ NOTE: the first six arguments are numbered 0 .. 5 ]
*)
let arg_loc (n : int) : operand =
  let arg_regs = [ Rdi; Rsi; Rdx; Rcx; R08; R09 ] in
  match n with
  | n when n < 6 -> Reg (List.nth arg_regs n)
  | _ -> Ind3 (Lit (Int64.of_int (8 * (n - 4))), Rbp)
;;

(* We suggest that you create a helper function that computes the
   stack layout for a given function declaration.

   - each function argument should be copied into a stack slot
   - in this (inefficient) compilation strategy, each local id
     is also stored as a stack slot.
   - see the discussion about locals
*)
let stack_layout (args : uid list) ((block, lbled_blocks) : cfg) : layout =
  let blocks =
    List.fold_left (fun result (_, blk) -> blk :: result) [ block ] lbled_blocks
  in
  let uids =
    List.sort_uniq String.compare
    @@ args
    @ List.fold_left
        (fun result blk -> List.map fst blk.insns @ [ fst blk.term ] @ result)
        []
        blocks
  in
  snd
  @@ List.fold_left_map
       (fun acc arg ->
         match arg with
         | _ -> succ acc, (arg, Ind3 (Lit (Int64.of_int (-8 * acc)), Rbp)))
       1
       uids
;;

(* The code for the entry-point of a function must do several things:

   - since our simple compiler maps local %uids to stack slots,
     compiling the control-flow-graph body of an fdecl requires us to
     compute the layout (see the discussion of locals and layout)

   - the function code should also comply with the calling
     conventions, typically by moving arguments out of the parameter
     registers (or stack slots) into local storage space.  For our
     simple compilation strategy, that local storage space should be
     in the stack. (So the function parameters can also be accounted
     for in the layout.)

   - the function entry code should allocate the stack storage needed
     to hold all of the local stack slots.
*)
let compile_fdecl
  (tdecls : (tid * ty) list)
  (name : string)
  ({ f_param; f_cfg; _ } : fdecl)
  : prog
  =
  let open Asm in
  let stack = stack_layout f_param f_cfg in
  let stack_size = 8 * List.length stack in
  let ctxt = { tdecls; layout = stack } in
  let fn = Platform.mangle name in
  gtext
    fn
    ([ Pushq, [ ~%Rbp ]; Movq, [ ~%Rsp; ~%Rbp ]; Subq, [ ~$stack_size; ~%Rsp ] ]
     @ snd
         (List.fold_left
            (fun (n, insn) param ->
              ( succ n
              , insn
                @ [ Movq, [ arg_loc n; ~%Rax ]
                  ; Movq, [ ~%Rax; lookup stack param ]
                  ] ))
            (0, [])
            f_param)
     @ compile_block fn ctxt (fst f_cfg))
  :: List.map (fun (lbl, blk) -> compile_lbl_block fn lbl ctxt blk) (snd f_cfg)
;;

(* compile_gdecl ------------------------------------------------------------ *)
(* Compile a global value into an X86 global data declaration and map
   a global uid to its associated X86 label.
*)
let rec compile_ginit : ginit -> X86.data list = function
  | GNull -> [ Quad (Lit 0L) ]
  | GGid gid -> [ Quad (Lbl (Platform.mangle gid)) ]
  | GInt c -> [ Quad (Lit c) ]
  | GString s -> [ Asciz s ]
  | GArray gs | GStruct gs -> List.map compile_gdecl gs |> List.flatten
  | GBitcast (_t1, g, _t2) -> compile_ginit g

and compile_gdecl (_, g) = compile_ginit g

(* compile_prog ------------------------------------------------------------- *)
let compile_prog { tdecls; gdecls; fdecls; _ } : X86.prog =
  let g (lbl, gdecl) = Asm.data (Platform.mangle lbl) (compile_gdecl gdecl) in
  let f (name, fdecl) = compile_fdecl tdecls name fdecl in
  List.map g gdecls @ (List.map f fdecls |> List.flatten)
;;
