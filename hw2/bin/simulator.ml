(* X86lite Simulator *)

(* See the documentation in the X86lite specification, available on the
   course web pages, for a detailed explanation of the instruction
   semantics.
*)

open X86

(* simulator machine state -------------------------------------------------- *)

let mem_bot = 0x400000L (* lowest valid address *)
let mem_top = 0x410000L (* one past the last byte in memory *)
let mem_size = Int64.to_int (Int64.sub mem_top mem_bot)
let nregs = 17 (* including Rip *)
let ins_size = 8L (* assume we have a 8-byte encoding *)
let exit_addr = 0xfdeadL (* halt when m.regs(%rip) = exit_addr *)

(* The simulator memory maps addresses to symbolic bytes.  Symbolic
   bytes are either actual data indicated by the Byte constructor or
   'symbolic instructions' that take up eight bytes for the purposes of
   layout.

   The symbolic bytes abstract away from the details of how
   instructions are represented in memory.  Each instruction takes
   exactly eight consecutive bytes, where the first byte InsB0 stores
   the actual instruction, and the next sevent bytes are InsFrag
   elements, which aren't valid data.

   For example, the two-instruction sequence:
   at&t syntax             ocaml syntax
   movq %rdi, (%rsp)       Movq,  [~%Rdi; Ind2 Rsp]
   decq %rdi               Decq,  [~%Rdi]

   is represented by the following elements of the mem array (starting
   at address 0x400000):

   0x400000 :  InsB0 (Movq,  [~%Rdi; Ind2 Rsp])
   0x400001 :  InsFrag
   0x400002 :  InsFrag
   0x400003 :  InsFrag
   0x400004 :  InsFrag
   0x400005 :  InsFrag
   0x400006 :  InsFrag
   0x400007 :  InsFrag
   0x400008 :  InsB0 (Decq,  [~%Rdi])
   0x40000A :  InsFrag
   0x40000B :  InsFrag
   0x40000C :  InsFrag
   0x40000D :  InsFrag
   0x40000E :  InsFrag
   0x40000F :  InsFrag
   0x400010 :  InsFrag
*)
type sbyte =
  | InsB0 of ins (* 1st byte of an instruction *)
  | InsFrag (* 2nd - 8th bytes of an instruction *)
  | Byte of char (* non-instruction byte *)

(* memory maps addresses to symbolic bytes *)
type mem = sbyte array

(* Flags for condition codes *)
type flags =
  { mutable fo : bool
  ; mutable fs : bool
  ; mutable fz : bool
  }

(* Register files *)
type regs = int64 array

(* Complete machine state *)
type mach =
  { flags : flags
  ; regs : regs
  ; mem : mem
  }

(* simulator helper functions ----------------------------------------------- *)

(* The index of a register in the regs array *)
let rind : reg -> int = function
  | Rip -> 16
  | Rax -> 0
  | Rbx -> 1
  | Rcx -> 2
  | Rdx -> 3
  | Rsi -> 4
  | Rdi -> 5
  | Rbp -> 6
  | Rsp -> 7
  | R08 -> 8
  | R09 -> 9
  | R10 -> 10
  | R11 -> 11
  | R12 -> 12
  | R13 -> 13
  | R14 -> 14
  | R15 -> 15
;;

(* Helper functions for reading/writing sbytes *)

(* Convert an int64 to its sbyte representation *)
let sbytes_of_int64 (i : int64) : sbyte list =
  let open Char in
  let open Int64 in
  List.map
    (fun n -> Byte (shift_right i n |> logand 0xffL |> to_int |> chr))
    [ 0; 8; 16; 24; 32; 40; 48; 56 ]
;;

(* Convert an sbyte representation to an int64 *)
let int64_of_sbytes (bs : sbyte list) : int64 =
  let open Char in
  let open Int64 in
  let f b i =
    match b with
    | Byte c -> logor (shift_left i 8) (c |> code |> of_int)
    | _ -> 0L
  in
  List.fold_right f bs 0L
;;

(* Convert a string to its sbyte representation *)
let sbytes_of_string (s : string) : sbyte list =
  let rec loop acc = function
    | i when i < 0 -> acc
    | i -> loop (Byte s.[i] :: acc) (pred i)
  in
  loop [ Byte '\x00' ] @@ (String.length s - 1)
;;

(* Serialize an instruction to sbytes *)
let sbytes_of_ins ((op, args) : ins) : sbyte list =
  let check = function
    | Imm (Lbl _) | Ind1 (Lbl _) | Ind3 (Lbl _, _) ->
      invalid_arg "sbytes_of_ins: tried to serialize a label!"
    | _ -> ()
  in
  List.iter check args;
  [ InsB0 (op, args)
  ; InsFrag
  ; InsFrag
  ; InsFrag
  ; InsFrag
  ; InsFrag
  ; InsFrag
  ; InsFrag
  ]
;;

(* Serialize a data element to sbytes *)
let sbytes_of_data : data -> sbyte list = function
  | Quad (Lit i) -> sbytes_of_int64 i
  | Asciz s -> sbytes_of_string s
  | Quad (Lbl _) -> invalid_arg "sbytes_of_data: tried to serialize a label!"
;;

(* It might be useful to toggle printing of intermediate states of your
   simulator. Our implementation uses this mutable flag to turn on/off
   printing.  For instance, you might write something like:

   [if !debug_simulator then print_endline @@ string_of_ins u; ...]
*)
let debug_simulator = ref false

(* override some useful operators *)
let ( +. ) = Int64.add
let ( -. ) = Int64.sub
let ( *. ) = Int64.mul
let ( <. ) a b = Int64.compare a b < 0
let ( >. ) a b = Int64.compare a b > 0
let ( <=. ) a b = Int64.compare a b <= 0
let ( >=. ) a b = Int64.compare a b >= 0

(* Interpret a condition code with respect to the given flags. *)
(* !!! Check the Specification for Help *)
let interp_cnd { fo; fs; fz } : cnd -> bool =
  fun cond_inst ->
  match cond_inst with
  | Eq -> fz
  | Neq -> not fz
  | Lt -> fs <> fo
  | Le -> fs <> fo || fz
  | Gt -> fs = fo && not fz
  | Ge -> fs = fo
;;

(* Maps an X86lite address into Some OCaml array index,
   or None if the address is not within the legal address space. *)
let map_addr (addr : quad) : int option =
  let open Int64 in
  let i = to_int (sub addr mem_bot) in
  if i < 0 || i >= mem_size then None else Some i
;;

(* Your simulator should raise this exception if it tries to read from or
   store to an address not within the valid address space. *)
exception X86lite_segfault

(* Raise X86lite_segfault when addr is invalid. *)
let map_addr_segfault (addr : quad) : int =
  match map_addr addr with
  | Some i -> if i mod 8 <> 0 then raise X86lite_segfault else i
  | None -> raise X86lite_segfault
;;

(* Simulates one step of the machine:
   - fetch the instruction at %rip
   - compute the source and/or destination information from the operands
   - simulate the instruction semantics
   - update the registers and/or memory appropriately
   - set the condition flags

   We provide the basic structure of step function and helper functions.
   Implement the subroutine below to complete the step function.
   See step function to understand each subroutine and how they
   are glued together.
*)

let readquad (m : mach) (addr : quad) : quad =
  let i = map_addr_segfault addr in
  let sbytes = List.init 8 (fun n -> m.mem.(i + n)) in
  int64_of_sbytes sbytes
;;

let writequad (m : mach) (addr : quad) (w : quad) : unit =
  let i = map_addr_segfault addr in
  let sbytes = sbytes_of_int64 w in
  List.iteri (fun n b -> m.mem.(i + n) <- b) sbytes
;;

let fetchins (m : mach) (addr : quad) : ins =
  let i = map_addr_segfault addr in
  match m.mem.(i) with
  | InsB0 ins -> ins
  | _ -> raise X86lite_segfault
;;

(* Compute the instruction result.
 * NOTE: See int64_overflow.ml for the definition of the return type
*  Int64_overflow.t. *)
let interp_opcode (m : mach) (o : opcode) (args : int64 list) : Int64_overflow.t
  =
  let open Int64 in
  let open Int64_overflow in
  match o, args with
  | Addq, [ src; dest ] -> add dest src
  | Andq, [ src; dest ] -> ok @@ logand dest src
  | Imulq, [ src; dest ] -> mul dest src
  | Leaq, [ addr ] -> ok addr
  | Movq, [ src; _ ] -> ok src
  | Negq, [ dest ] -> neg dest
  | Notq, [ dest ] -> ok @@ lognot dest
  | Orq, [ src; dest ] -> ok @@ logor dest src
  | Cmpq, [ src; dest ] | Subq, [ src; dest ] -> sub dest src
  | Xorq, [ src; dest ] -> ok @@ logxor dest src
  | Sarq, [ amt; dest ] -> ok @@ shift_right dest @@ to_int amt
  | Shlq, [ amt; dest ] -> ok @@ shift_left dest @@ to_int amt
  | Shrq, [ amt; dest ] -> ok @@ shift_right_logical dest @@ to_int amt
  | J cnd, [ src ] ->
    ok (if interp_cnd m.flags cnd then src else m.regs.(rind Rip))
  | Set cnd, [ dest ] ->
    ok
      (logor
         (logand dest (lognot 0xffL))
         (if interp_cnd m.flags cnd then 1L else 0L))
  | _ -> failwith "interp_opcode not implemented"
;;

let write_ind (m : mach) : operand -> int64 -> unit = function
  | Reg reg -> fun x -> m.regs.(rind reg) <- x
  | Ind1 (Lit imm) -> fun x -> writequad m imm x
  | Ind2 reg -> fun x -> writequad m m.regs.(rind reg) x
  | Ind3 (Lit disp, base) -> fun x -> writequad m (m.regs.(rind base) +. disp) x
  | _ -> raise X86lite_segfault
;;

(** Update machine state with instruction results. *)
let ins_writeback (m : mach) : ins -> int64 -> unit = function
  | Cmpq, _ -> fun _ -> ()
  | J _, _ -> write_ind m (Reg Rip)
  | Addq, [ _; dest ]
  | Andq, [ _; dest ]
  | Imulq, [ _; dest ]
  | Leaq, [ _; dest ]
  | Movq, [ _; dest ]
  | Orq, [ _; dest ]
  | Subq, [ _; dest ]
  | Xorq, [ _; dest ]
  | Sarq, [ _; dest ]
  | Shlq, [ _; dest ]
  | Shrq, [ _; dest ]
  | Negq, [ dest ]
  | Notq, [ dest ]
  | Set _, [ dest ] -> write_ind m dest
  | _ -> failwith "ins_writeback not implemented"
;;

let read_ind (m : mach) : operand -> int64 = function
  | Ind1 (Lit imm) -> imm
  | Ind2 reg -> m.regs.(rind reg)
  | Ind3 (Lit disp, base) -> m.regs.(rind base) +. disp
  | _ -> raise X86lite_segfault
;;

let read_operand (m : mach) (opnd : operand) : int64 =
  match opnd with
  | Imm (Lit imm) -> imm
  | Reg reg -> m.regs.(rind reg)
  | Ind1 _ | Ind2 _ | Ind3 _ -> readquad m @@ read_ind m opnd
  | _ -> raise X86lite_segfault
;;

(* mem addr ---> mem array index *)
let interp_operands (m : mach) : ins -> int64 list = function
  | Leaq, [ addr; _ ] -> [ read_ind m addr ]
  | Movq, operands
  | Addq, operands
  | Cmpq, operands
  | Subq, operands
  | Imulq, operands
  | Negq, operands
  | Andq, operands
  | Orq, operands
  | Notq, operands
  | Sarq, operands
  | Shlq, operands
  | Shrq, operands
  | J _, operands
  | Set _, operands
  | Xorq, operands -> List.map (read_operand m) operands
  | _ -> raise X86lite_segfault
;;

(* NOTE: Your simulator is not required to detect invalid operands. *)
let validate_operands : ins -> unit = function
  | _ -> ()
;;

let rec crack (is : ins) : ins list =
  let open Asm in
  match is with
  | Pushq, [ src ] -> [ Subq, [ ~$8; ~%Rsp ]; Movq, [ src; Ind2 Rsp ] ]
  | Popq, [ dest ] -> [ Movq, [ Ind2 Rsp; dest ]; Addq, [ ~$8; ~%Rsp ] ]
  | Incq, [ dest ] -> [ Addq, [ ~$1; dest ] ]
  | Decq, [ dest ] -> [ Subq, [ ~$1; dest ] ]
  | Jmp, [ src ] -> [ Movq, [ src; ~%Rip ] ]
  | Callq, [ src ] -> crack (Pushq, [ ~%Rip ]) @ [ Movq, [ src; ~%Rip ] ]
  | Retq, [] -> crack (Popq, [ ~%Rip ])
  | _ -> [ is ]
;;

(* TODO: double check against spec *)
let set_flags (m : mach) (op : opcode) (ws : quad list) (w : Int64_overflow.t)
  : unit
  =
  match op with
  | Callq | Retq | Pushq | Popq | Jmp | J _ | Leaq | Movq | Notq | Set _ -> ()
  | Sarq ->
    (match ws with
     | [ amt; dest ] ->
       if amt <> 0L
       then (
         m.flags.fs <- w.value <. 0L;
         m.flags.fz <- w.value = 0L;
         if amt = 1L then m.flags.fo <- false)
     | _ -> raise X86lite_segfault)
  | Shlq ->
    (match ws with
     | [ amt; dest ] ->
       if amt <> 0L
       then (
         m.flags.fs <- w.value <. 0L;
         m.flags.fz <- w.value = 0L;
         if amt = 1L
         then
           m.flags.fo
           <- Int64.shift_right_logical dest 63
              <> (Int64.shift_right_logical dest 62 |> Int64.logand 1L))
     | _ -> raise X86lite_segfault)
  | Shrq ->
    (match ws with
     | [ amt; dest ] ->
       if amt <> 0L then m.flags.fs <- Int64.shift_right_logical w.value 63 = 1L;
       m.flags.fz <- w.value = 0L;
       if amt = 1L then m.flags.fo <- Int64.shift_right_logical dest 63 = 1L
     | _ -> raise X86lite_segfault)
  | Incq
  | Decq
  | Addq
  | Andq
  | Negq
  | Orq
  | Cmpq
  | Subq
  | Xorq
  (* fs and fz are undefined *)
  | Imulq ->
    m.flags.fo <- w.overflow;
    m.flags.fs <- w.value <. 0L;
    m.flags.fz <- w.value = 0L
;;

let step (m : mach) : unit =
  (* execute an instruction *)
  let ((op, args) as ins) = fetchins m m.regs.(rind Rip) in
  validate_operands ins;
  (* Some instructions involve running two or more basic instructions. 
   * For other instructions, just return a list of one instruction.
   * See the X86lite specification for details. *)
  let uops : ins list = crack (op, args) in
  m.regs.(rind Rip) <- m.regs.(rind Rip) +. ins_size;
  List.iter
    (fun ((uop, _) as u) ->
      if !debug_simulator then print_endline @@ string_of_ins u;
      let ws = interp_operands m u in
      let res = interp_opcode m uop ws in
      ins_writeback m u @@ res.Int64_overflow.value;
      set_flags m op ws res)
    uops
;;

(* Runs the machine until the rip register reaches a designated
   memory address. Returns the contents of %rax when the
   machine halts. *)
let run (m : mach) : int64 =
  while m.regs.(rind Rip) <> exit_addr do
    step m
  done;
  m.regs.(rind Rax)
;;

(* assembling and linking --------------------------------------------------- *)

(* A representation of the executable *)
type exec =
  { entry : quad (* address of the entry point *)
  ; text_pos : quad (* starting address of the code *)
  ; data_pos : quad (* starting address of the data *)
  ; text_seg : sbyte list (* contents of the text segment *)
  ; data_seg : sbyte list (* contents of the data segment *)
  }

(* Assemble should raise this when a label is used but not defined *)
exception Undefined_sym of lbl

(* Assemble should raise this when a label is defined more than once *)
exception Redefined_sym of lbl

(* Convert an X86 program into an object file:
   - separate the text and data segments
   - compute the size of each segment
     Note: the size of an Asciz string section is (1 + the string length)
     due to the null terminator

   - resolve the labels to concrete addresses and 'patch' the instructions to
     replace Lbl values with the corresponding Imm values.
     HINT: consider building a mapping from symboli Lbl to memory address

   - the text segment starts at the lowest address
   - the data segment starts after the text segment

   HINT: List.fold_left and List.fold_right are your friends.
*)
let is_size (is : ins list) : quad =
  List.fold_left (fun acc i -> acc +. ins_size) 0L is
;;

let ds_size (ds : data list) : quad =
  List.fold_left
    (fun acc d ->
      acc
      +.
      match d with
      | Asciz s -> Int64.of_int (String.length s + 1)
      | Quad _ -> 8L)
    0L
    ds
;;

let sep_segments (p : prog) : prog * prog =
  let data_seg : prog =
    List.filter
      (fun { asm; _ } ->
        match asm with
        | Data _ -> true
        | _ -> false)
      p
  in
  let text_seg : prog =
    List.filter
      (fun { asm; _ } ->
        match asm with
        | Text _ -> true
        | _ -> false)
      p
  in
  text_seg, data_seg
;;

let resolve_lbls ((text_seg, data_seg) : prog * prog) : (lbl, quad) Hashtbl.t =
  let seg = text_seg @ data_seg in
  let resolve_lbls' (seg : prog) : (lbl * quad) list * quad =
    List.fold_left
      (fun (acc, addr) { lbl; asm; _ } ->
        match asm with
        | Text is ->
          let acc' = (lbl, addr) :: acc in
          acc', addr +. is_size is
        | Data ds ->
          let acc' = (lbl, addr) :: acc in
          acc', addr +. ds_size ds)
      ([], mem_bot)
      seg
  in
  let lbls, _ = resolve_lbls' seg in
  let tbl = Hashtbl.create (List.length lbls) in
  List.iter
    (fun (lbl, addr) ->
      if Hashtbl.mem tbl lbl
      then raise (Redefined_sym lbl)
      else Hashtbl.add tbl lbl addr)
    lbls;
  tbl
;;

let assemble (p : prog) : exec =
  let text_seg, data_seg = sep_segments p in
  let lbls = resolve_lbls (text_seg, data_seg) in
  let map_lbl (lbl : lbl) : quad =
    match Hashtbl.find_opt lbls lbl with
    | Some addr -> addr
    | None -> raise (Undefined_sym lbl)
  in
  let map_lbl_to_lit (lbl : lbl) : imm = Lit (map_lbl lbl) in
  let resolve_opr_lbl : operand -> operand = function
    | Imm (Lbl lbl) -> Imm (map_lbl_to_lit lbl)
    | Ind1 (Lbl lbl) -> Ind1 (map_lbl_to_lit lbl)
    | Ind3 (Lbl lbl, r) -> Ind3 (map_lbl_to_lit lbl, r)
    | opr -> opr
  in
  let resolve_ins_lbl (op, oprs) : ins = op, List.map resolve_opr_lbl oprs in
  let resolve_seg_lbl (seg : prog) : sbyte list =
    List.fold_left
      (fun acc { asm; _ } ->
        match asm with
        | Text is ->
          acc
          @ List.concat_map (fun ins -> sbytes_of_ins (resolve_ins_lbl ins)) is
        | Data ds -> acc @ List.concat_map sbytes_of_data ds)
      []
      seg
  in
  let text_size =
    List.fold_right
      (fun { asm; _ } acc ->
        match asm with
        | Text is -> acc +. is_size is
        | _ -> acc)
      text_seg
      0L
  in
  { entry = map_lbl "main"
  ; text_pos = mem_bot
  ; data_pos = mem_bot +. text_size
  ; text_seg = resolve_seg_lbl text_seg
  ; data_seg = resolve_seg_lbl data_seg
  }
;;

(* Convert an object file into an executable machine state.
   - allocate the mem array
   - set up the memory state by writing the symbolic bytes to the
     appropriate locations
   - create the inital register state
   - initialize rip to the entry point address
   - initializes rsp to the last word in memory
   - the other registers are initialized to 0
   - the condition code flags start as 'false'

   Hint: The Array.make, Array.blit, and Array.of_list library functions
   may be of use.
*)
let load { entry; text_pos; data_pos; text_seg; data_seg } : mach =
  let flags = { fo = false; fs = false; fz = false } in
  let regs = Array.make nregs 0L in
  regs.(rind Rip) <- entry;
  regs.(rind Rsp) <- mem_top -. 8L;
  let mem = Array.make mem_size (Byte '\x00') in
  let segs = text_seg @ data_seg in
  let exit_addr_mem = Array.of_list @@ sbytes_of_int64 exit_addr in
  Array.blit exit_addr_mem 0 mem (mem_size - 8) 8;
  Array.blit (Array.of_list segs) 0 mem 0 (List.length segs);
  { flags; regs; mem }
;;
