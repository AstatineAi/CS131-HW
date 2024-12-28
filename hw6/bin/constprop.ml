open Ll
open Datastructures

(* The lattice of symbolic constants ---------------------------------------- *)
module SymConst = struct
  type t =
    | NonConst (* Uid may take on multiple values at runtime *)
    | Const of int64 (* Uid will always evaluate to const i64 or i1 *)
    | UndefConst (* Uid is not defined at the point *)

  let compare (a : t) (b : t) =
    match a, b with
    | Const i, Const j -> Int64.compare i j
    | NonConst, NonConst | UndefConst, UndefConst -> 0
    | NonConst, _ | _, UndefConst -> 1
    | UndefConst, _ | _, NonConst -> -1
  ;;

  let to_string : t -> string = function
    | NonConst -> "NonConst"
    | Const i -> Printf.sprintf "Const (%LdL)" i
    | UndefConst -> "UndefConst"
  ;;
end

(* The analysis computes, at each program point, which UIDs in scope will evaluate 
   to integer constants *)
type fact = SymConst.t UidM.t

(* flow function across Ll instructions ------------------------------------- *)
(* - Uid of a binop or icmp with const arguments is constant-out with
     result that is computed statically (see the Int64 module)
   - Uid of a binop or icmp with an UndefConst argument is UndefConst-out
   - Uid of a binop or icmp with an NonConst argument is NonConst-out
   - Uid of stores and void calls are UndefConst-out
   - Uid of all other instructions are NonConst-out
 *)
let insn_flow ((u, i) : uid * insn) (d : fact) : fact =
  let find_op (op : operand) : SymConst.t =
    match op with
    | Const i -> SymConst.Const i
    | Id u ->
      (match UidM.find_opt u d with
       | Some v -> v
       | None -> SymConst.UndefConst)
    | _ -> SymConst.UndefConst
  in
  match i with
  | Binop (bop, _, op1, op2) ->
    let v1 = find_op op1 in
    let v2 = find_op op2 in
    let apply_binop (i1 : int64) (i2 : int64) : SymConst.t =
      let open Int64 in
      match bop with
      | Add -> SymConst.Const (add i1 i2)
      | Sub -> SymConst.Const (sub i1 i2)
      | Mul -> SymConst.Const (mul i1 i2)
      | Shl -> SymConst.Const (shift_left i1 (to_int i2))
      | Lshr -> SymConst.Const (shift_right_logical i1 (to_int i2))
      | Ashr -> SymConst.Const (shift_right i1 (to_int i2))
      | And -> SymConst.Const (logand i1 i2)
      | Or -> SymConst.Const (logor i1 i2)
      | Xor -> SymConst.Const (logxor i1 i2)
    in
    let res =
      match v1, v2 with
      | SymConst.Const i1, SymConst.Const i2 -> apply_binop i1 i2
      | SymConst.UndefConst, _ | _, SymConst.UndefConst -> SymConst.UndefConst
      | _ -> SymConst.NonConst
    in
    UidM.add u res d
  | Icmp (cnd, _, op1, op2) ->
    let v1 = find_op op1 in
    let v2 = find_op op2 in
    let apply_icmp (i1 : int64) (i2 : int64) : SymConst.t =
      let open Int64 in
      match cnd with
      | Eq -> SymConst.Const (if i1 = i2 then 1L else 0L)
      | Ne -> SymConst.Const (if i1 <> i2 then 1L else 0L)
      | Slt -> SymConst.Const (if i1 < i2 then 1L else 0L)
      | Sle -> SymConst.Const (if i1 <= i2 then 1L else 0L)
      | Sgt -> SymConst.Const (if i1 > i2 then 1L else 0L)
      | Sge -> SymConst.Const (if i1 >= i2 then 1L else 0L)
    in
    let res =
      match v1, v2 with
      | SymConst.Const i1, SymConst.Const i2 -> apply_icmp i1 i2
      | SymConst.UndefConst, _ | _, SymConst.UndefConst -> SymConst.UndefConst
      | _ -> SymConst.NonConst
    in
    UidM.add u res d
  | Store (_, _, _) | Call (Void, _, _) -> UidM.add u SymConst.UndefConst d
  | _ -> UidM.add u SymConst.NonConst d
;;

(* The flow function across terminators is trivial: they never change const info *)
let terminator_flow (t : terminator) (d : fact) : fact = d

(* module for instantiating the generic framework --------------------------- *)
module Fact = struct
  type t = fact

  let forwards = true
  let insn_flow = insn_flow
  let terminator_flow = terminator_flow
  let normalize : fact -> fact = UidM.filter (fun _ v -> v != SymConst.UndefConst)

  let compare (d : fact) (e : fact) : int =
    UidM.compare SymConst.compare (normalize d) (normalize e)
  ;;

  let to_string : fact -> string = UidM.to_string (fun _ v -> SymConst.to_string v)

  (* The constprop analysis should take the meet over predecessors to compute the
       flow into a node. You may find the UidM.merge function useful *)
  let combine (ds : fact list) : fact =
    let merge_const (u : uid) (c1 : SymConst.t option) (c2 : SymConst.t option)
      : SymConst.t option
      =
      match c1, c2 with
      | Some (SymConst.Const i1), Some (SymConst.Const i2) ->
        if Int64.equal i1 i2 then c1 else Some SymConst.NonConst
      | Some SymConst.UndefConst, c | c, Some SymConst.UndefConst -> c
      | Some SymConst.NonConst, _ | _, Some SymConst.NonConst -> Some SymConst.NonConst
      | Some c, None | None, Some c -> Some c
      | None, None -> None
    in
    List.fold_left (UidM.merge merge_const) UidM.empty ds
  ;;
end

(* instantiate the general framework ---------------------------------------- *)
module Graph = Cfg.AsGraph (Fact)
module Solver = Solver.Make (Fact) (Graph)

(* expose a top-level analysis operation ------------------------------------ *)
let analyze (g : Cfg.t) : Graph.t =
  (* the analysis starts with every node set to bottom (the map of every uid 
     in the function to UndefConst *)
  let init l = UidM.empty in
  (* the flow into the entry node should indicate that any parameter to the
     function is not a constant *)
  let cp_in =
    List.fold_right (fun (u, _) -> UidM.add u SymConst.NonConst) g.Cfg.args UidM.empty
  in
  let fg = Graph.of_cfg init cp_in g in
  Solver.solve fg
;;

(* run constant propagation on a cfg given analysis results ----------------- *)
(* HINT: your cp_block implementation will probably rely on several helper 
   functions.                                                                 *)
let run (cg : Graph.t) (cfg : Cfg.t) : Cfg.t =
  let open SymConst in
  let cp_block (l : Ll.lbl) (cfg : Cfg.t) : Cfg.t =
    let b = Cfg.block cfg l in
    let cb = Graph.uid_out cg l in
    let replace_op (u : uid) (op : operand) : operand =
      match op with
      | Id v ->
        (match UidM.find_opt v (cb u) with
         | Some (Const i) -> Const i
         | _ -> op)
      | _ -> op
    in
    let replace_insn (u : uid) (i : insn) : insn =
      match i with
      | Binop (b, t, o1, o2) -> Binop (b, t, replace_op u o1, replace_op u o2)
      | Icmp (c, t, o1, o2) -> Icmp (c, t, replace_op u o1, replace_op u o2)
      | Store (t, o1, o2) -> Store (t, replace_op u o1, o2)
      | Call (t, o, args) ->
        let new_args = List.map (fun (t, o) -> t, replace_op u o) args in
        Call (t, replace_op u o, new_args)
      | Gep (t, o, os) -> Gep (t, replace_op u o, List.map (replace_op u) os)
      | _ -> i
    in
    let replace_term ((u, t) : uid * terminator) : uid * terminator =
      let new_t =
        match t with
        | Ret (t, o) -> Ret (t, Option.map (replace_op u) o)
        | Br l -> Br l
        | Cbr (o, l1, l2) -> Cbr (replace_op u o, l1, l2)
      in
      u, new_t
    in
    let new_insns = List.map (fun (u, i) -> u, replace_insn u i) b.insns in
    let new_term = replace_term b.term in
    let new_block = { insns = new_insns; term = new_term } in
    Cfg.add_block l new_block cfg
  in
  LblS.fold cp_block (Cfg.nodes cfg) cfg
;;
