open Format
open Ast
open Tast
open X86_64

let debug = ref false

let iter f = List.fold_left (fun code x -> code ++ f x) nop
let iter2 f = List.fold_left2 (fun code x y -> code ++ f x y) nop

let new_label =
  let r = ref 0 in fun () -> incr r; "L_" ^ string_of_int !r

let strings = Hashtbl.create 17

let current_fn_name = ref ""

let rec sizeof = function
  | Tint | Tbool -> 8
  | Tstring -> 8
  | Tptr _ -> 8
  | Tstruct s -> s.s_size
  | Tnil -> 8
  | Tmany _ -> 0

let alloc_string s =
  if Hashtbl.mem strings s then
    Hashtbl.find strings s
  else begin
    let lbl = new_label () in
    Hashtbl.add strings s lbl;
    lbl
  end

let allocate_struct_fields s =
  let offset = ref 0 in
  List.iter (fun f ->
    f.f_ofs <- !offset;
    offset := !offset + sizeof f.f_typ
  ) s.s_list;
  s.s_size <- !offset

let rec allocate_locals_expr ofs e =
  match e.expr_desc with
  | TEskip | TEconstant _ | TEnil -> ofs
  | TEbinop (_, e1, e2) ->
      let ofs = allocate_locals_expr ofs e1 in
      allocate_locals_expr ofs e2
  | TEunop (_, e1) ->
      allocate_locals_expr ofs e1
  | TEnew _ -> ofs
  | TEcall (_, args) ->
      List.fold_left allocate_locals_expr ofs args
  | TEident _ -> ofs
  | TEdot (e1, _) ->
      allocate_locals_expr ofs e1
  | TEassign (lhs, rhs) ->
      let ofs = List.fold_left allocate_locals_expr ofs lhs in
      List.fold_left allocate_locals_expr ofs rhs
  | TEvars vars ->
      List.fold_left (fun ofs v ->
        let size = sizeof v.v_typ in
        let new_ofs = ofs - size in
        v.v_ofs <- new_ofs;
        new_ofs
      ) ofs vars
  | TEif (cond, then_e, else_e) ->
      let ofs = allocate_locals_expr ofs cond in
      let ofs = allocate_locals_expr ofs then_e in
      allocate_locals_expr ofs else_e
  | TEreturn exprs ->
      List.fold_left allocate_locals_expr ofs exprs
  | TEblock exprs ->
      List.fold_left allocate_locals_expr ofs exprs
  | TEfor (cond, body) ->
      let ofs = allocate_locals_expr ofs cond in
      allocate_locals_expr ofs body
  | TEprint exprs ->
      List.fold_left allocate_locals_expr ofs exprs
  | TEincdec (e1, _) ->
      allocate_locals_expr ofs e1

let allocate_params fn =
  let num_params = List.length fn.fn_params in
  List.iteri (fun i v ->
    let size = sizeof v.v_typ in
    if v.v_addr then begin
      v.v_ofs <- -8 * (i + 1)
    end else begin
      if i < 6 then
        v.v_ofs <- -8 * (i + 1)
      else
        v.v_ofs <- 16 + 8 * (i - 6)
    end;
    ignore size
  ) fn.fn_params;
  -8 * (min num_params 6)

let param_regs = [| rdi; rsi; rdx; rcx; r8; r9 |]

let rec get_types_list el =
  List.concat_map (fun e ->
    match e.expr_typ with
    | Tmany tl -> tl
    | t -> [t]
  ) el

let rec compile_expr e = match e.expr_desc with
  | TEskip ->
      nop
  | TEconstant (Cint n) ->
      movq (imm64 n) (reg rax)
  | TEconstant (Cbool b) ->
      movq (imm (if b then 1 else 0)) (reg rax)
  | TEconstant (Cstring s) ->
      let lbl = alloc_string s in
      movq (ilab lbl) (reg rax)
  | TEbinop (op, e1, e2) ->
      compile_binop op e1 e2
  | TEunop (op, e) ->
      compile_unop op e
  | TEnil ->
      xorq (reg rax) (reg rax)
  | TEnew typ ->
      let size = sizeof typ in
      movq (imm size) (reg rdi) ++
      movq (imm 1) (reg rsi) ++
      call "calloc_"
  | TEprint el ->
      compile_print_list el
  | TEblock el ->
      iter compile_expr el
  | TEreturn [] ->
      jmp ("F_" ^ !current_fn_name ^ "_ret")
  | TEreturn exprs ->
      let code = List.fold_left (fun (code, idx) e ->
        match e.expr_typ with
        | Tmany tl ->
            let n = List.length tl in
            let load_code = List.fold_left (fun (c, i) _ ->
              let c = c ++ movq (ind ~ofs:(8 * i) rax) (reg r10) ++
                      movq (reg r10) (ind ~ofs:(16 + 8 * (idx + i)) rbp) in
              (c, i + 1)
            ) (nop, 0) tl in
            (code ++ compile_expr e ++ fst load_code, idx + n)
        | _ ->
            (code ++ compile_expr e ++
             movq (reg rax) (ind ~ofs:(16 + 8 * idx) rbp),
             idx + 1)
      ) (nop, 0) exprs in
      fst code ++
      jmp ("F_" ^ !current_fn_name ^ "_ret")
  | TEident v ->
      compile_load_var v
  | TEdot (e1, f) ->
      (match e1.expr_typ with
       | Tptr _ ->
           compile_expr e1 ++
           testq (reg rax) (reg rax) ++
           jz "graceful_stop" ++
           compile_load_field f.f_ofs f.f_typ
       | Tstruct _ ->
           compile_addr e1 ++
           compile_load_field f.f_ofs f.f_typ
       | _ -> failwith "TEdot on non-struct")
  | TEassign (lhs, rhs) ->
      compile_assign lhs rhs
  | TEvars vars ->
      iter (fun v ->
        let size = sizeof v.v_typ in
        compile_zero_init v.v_ofs size
      ) vars
  | TEif (cond, then_e, else_e) ->
      let lbl_else = new_label () in
      let lbl_end = new_label () in
      compile_expr cond ++
      testq (reg rax) (reg rax) ++
      jz lbl_else ++
      compile_expr then_e ++
      jmp lbl_end ++
      label lbl_else ++
      compile_expr else_e ++
      label lbl_end
  | TEfor (cond, body) ->
      let lbl_start = new_label () in
      let lbl_end = new_label () in
      label lbl_start ++
      (match cond.expr_desc with
       | TEskip -> nop
       | _ ->
           compile_expr cond ++
           testq (reg rax) (reg rax) ++
           jz lbl_end) ++
      compile_expr body ++
      jmp lbl_start ++
      label lbl_end
  | TEcall (fn, args) ->
      compile_call fn args
  | TEincdec (e1, incdec) ->
      compile_addr e1 ++
      (match incdec with
       | Inc -> incq (ind rax)
       | Dec -> decq (ind rax))

and compile_zero_init ofs size =
  let rec zero_words ofs remaining =
    if remaining <= 0 then nop
    else
      movq (imm 0) (ind ~ofs rbp) ++
      zero_words (ofs + 8) (remaining - 8)
  in
  zero_words ofs size

and compile_load_var v =
  let size = sizeof v.v_typ in
  if size <= 8 then
    movq (ind ~ofs:v.v_ofs rbp) (reg rax)
  else
    leaq (ind ~ofs:v.v_ofs rbp) rax

and compile_load_field ofs typ =
  let size = sizeof typ in
  if size <= 8 then
    movq (ind ~ofs rax) (reg rax)
  else
    if ofs <> 0 then addq (imm ofs) (reg rax) else nop

and compile_store_to_addr typ =
  let size = sizeof typ in
  if size <= 8 then
    movq (reg rax) (ind rbx)
  else begin
    let rec copy ofs remaining =
      if remaining <= 0 then nop
      else
        movq (ind ~ofs rax) (reg r10) ++
        movq (reg r10) (ind ~ofs rbx) ++
        copy (ofs + 8) (remaining - 8)
    in
    copy 0 size
  end

and compile_addr e =
  match e.expr_desc with
  | TEident v ->
      leaq (ind ~ofs:v.v_ofs rbp) rax
  | TEdot (e1, f) ->
      (match e1.expr_typ with
       | Tptr _ ->
           compile_expr e1 ++
           testq (reg rax) (reg rax) ++
           jz "graceful_stop" ++
           (if f.f_ofs <> 0 then addq (imm f.f_ofs) (reg rax) else nop)
       | Tstruct _ ->
           compile_addr e1 ++
           (if f.f_ofs <> 0 then addq (imm f.f_ofs) (reg rax) else nop)
       | _ -> failwith "compile_addr: TEdot on non-struct type")
  | TEunop (Ustar, e1) ->
      compile_expr e1 ++
      testq (reg rax) (reg rax) ++
      jz "graceful_stop"
  | _ ->
      failwith "compile_addr: not an lvalue"

and compile_unop op e =
  match op with
  | Uneg ->
      compile_expr e ++
      negq (reg rax)
  | Unot ->
      compile_expr e ++
      testq (reg rax) (reg rax) ++
      movq (imm 0) (reg rax) ++
      sete (reg al)
  | Ustar ->
      compile_expr e ++
      testq (reg rax) (reg rax) ++
      jz "graceful_stop" ++
      (match e.expr_typ with
       | Tptr inner ->
           let inner_size = sizeof inner in
           if inner_size <= 8 then
             movq (ind rax) (reg rax)
           else
             nop
       | _ -> movq (ind rax) (reg rax))
  | Uamp ->
      compile_addr e

and compile_binop op e1 e2 =
  match op with
  | Badd | Bsub | Bmul ->
      compile_expr e1 ++
      pushq (reg rax) ++
      compile_expr e2 ++
      popq rbx ++
      (match op with
       | Badd -> addq (reg rbx) (reg rax)
       | Bsub -> subq (reg rax) (reg rbx) ++ movq (reg rbx) (reg rax)
       | Bmul -> imulq (reg rbx) (reg rax)
       | _ -> assert false)
  | Bdiv | Bmod ->
      compile_expr e2 ++
      pushq (reg rax) ++
      compile_expr e1 ++
      popq rbx ++
      testq (reg rbx) (reg rbx) ++
      jz "graceful_stop" ++
      cqto ++
      idivq (reg rbx) ++
      (if op = Bmod then movq (reg rdx) (reg rax) else nop)
  | Beq | Bne | Blt | Ble | Bgt | Bge ->
      compile_expr e1 ++
      pushq (reg rax) ++
      compile_expr e2 ++
      popq rbx ++
      cmpq (reg rax) (reg rbx) ++
      movq (imm 0) (reg rax) ++
      (match op with
       | Beq -> sete (reg al)
       | Bne -> setne (reg al)
       | Blt -> setl (reg al)
       | Ble -> setle (reg al)
       | Bgt -> setg (reg al)
       | Bge -> setge (reg al)
       | _ -> assert false)
  | Band ->
      let lbl_false = new_label () in
      let lbl_end = new_label () in
      compile_expr e1 ++
      testq (reg rax) (reg rax) ++
      jz lbl_false ++
      compile_expr e2 ++
      testq (reg rax) (reg rax) ++
      jz lbl_false ++
      movq (imm 1) (reg rax) ++
      jmp lbl_end ++
      label lbl_false ++
      movq (imm 0) (reg rax) ++
      label lbl_end
  | Bor ->
      let lbl_true = new_label () in
      let lbl_end = new_label () in
      compile_expr e1 ++
      testq (reg rax) (reg rax) ++
      jnz lbl_true ++
      compile_expr e2 ++
      testq (reg rax) (reg rax) ++
      jnz lbl_true ++
      movq (imm 0) (reg rax) ++
      jmp lbl_end ++
      label lbl_true ++
      movq (imm 1) (reg rax) ++
      label lbl_end

and is_string_type = function
  | Tstring -> true
  | _ -> false

and compile_print_list el =
  let space_lbl = alloc_string " " in
  let rec loop prev_was_non_string = function
    | [] -> nop
    | e :: rest ->
        let curr_is_non_string = not (is_string_type e.expr_typ) in
        let space_code =
          if prev_was_non_string && curr_is_non_string then
            movq (ilab space_lbl) (reg rdi) ++
            call "printf_"
          else
            nop
        in
        space_code ++
        compile_print e ++
        loop curr_is_non_string rest
  in
  loop false el

and compile_print e =
  match e.expr_typ with
  | Tstring ->
      compile_expr e ++
      movq (reg rax) (reg rdi) ++
      call "printf_"
  | Tint ->
      let fmt_lbl = alloc_string "%ld" in
      compile_expr e ++
      movq (reg rax) (reg rsi) ++
      movq (ilab fmt_lbl) (reg rdi) ++
      xorq (reg rax) (reg rax) ++
      call "printf_"
  | Tbool ->
      let true_lbl = alloc_string "true" in
      let false_lbl = alloc_string "false" in
      let lbl_end = new_label () in
      compile_expr e ++
      testq (reg rax) (reg rax) ++
      jz ("print_false_" ^ lbl_end) ++
      movq (ilab true_lbl) (reg rdi) ++
      jmp ("print_end_" ^ lbl_end) ++
      label ("print_false_" ^ lbl_end) ++
      movq (ilab false_lbl) (reg rdi) ++
      label ("print_end_" ^ lbl_end) ++
      call "printf_"
  | Tptr _ | Tnil ->
      let nil_lbl = alloc_string "<nil>" in
      let fmt_lbl = alloc_string "%ld" in
      let lbl_end = new_label () in
      compile_expr e ++
      testq (reg rax) (reg rax) ++
      jnz ("print_ptr_" ^ lbl_end) ++
      movq (ilab nil_lbl) (reg rdi) ++
      call "printf_" ++
      jmp ("print_end_" ^ lbl_end) ++
      label ("print_ptr_" ^ lbl_end) ++
      movq (reg rax) (reg rsi) ++
      movq (ilab fmt_lbl) (reg rdi) ++
      xorq (reg rax) (reg rax) ++
      call "printf_" ++
      label ("print_end_" ^ lbl_end)
  | _ ->
      nop

and compile_assign lhs rhs =
  let rhs_types = get_types_list rhs in
  let num_rhs = List.length rhs_types in
  let num_lhs = List.length lhs in
  if num_lhs = num_rhs && num_rhs > 0 then begin
    if List.length rhs = 1 && num_rhs > 1 then begin
      let rhs_e = List.hd rhs in
      compile_expr rhs_e ++
      movq (reg rax) (reg r12) ++
      (let result, _ = List.fold_left (fun (code, idx) lhs_e ->
        let store_code =
          match lhs_e.expr_desc with
          | TEident v when v.v_name = "_" -> nop
          | _ ->
              compile_addr lhs_e ++
              movq (reg rax) (reg rbx) ++
              movq (ind ~ofs:(8 * idx) r12) (reg rax) ++
              compile_store_to_addr lhs_e.expr_typ
        in
        (code ++ store_code, idx + 1)
      ) (nop, 0) lhs in result)
    end else begin
      let temp_code = List.fold_left (fun code rhs_e ->
        let size = sizeof rhs_e.expr_typ in
        code ++
        compile_expr rhs_e ++
        (if size <= 8 then pushq (reg rax)
         else
           let rec push_struct ofs remaining =
             if remaining <= 0 then nop
             else
               pushq (ind ~ofs:(remaining - 8) rax) ++
               push_struct ofs (remaining - 8)
           in
           push_struct 0 size)
      ) nop rhs in
      let total_size = List.fold_left (fun acc e ->
        acc + (max 8 (sizeof e.expr_typ))
      ) 0 rhs in
      let store_code, _ = List.fold_right (fun lhs_e (code, ofs) ->
        let size = max 8 (sizeof lhs_e.expr_typ) in
        let new_ofs = ofs - size in
        let store =
          match lhs_e.expr_desc with
          | TEident v when v.v_name = "_" -> nop
          | _ ->
              compile_addr lhs_e ++
              movq (reg rax) (reg rbx) ++
              (if size <= 8 then
                 movq (ind ~ofs:new_ofs rsp) (reg rax) ++
                 compile_store_to_addr lhs_e.expr_typ
               else
                 let rec copy i =
                   if i >= size then nop
                   else
                     movq (ind ~ofs:(new_ofs + i) rsp) (reg r10) ++
                     movq (reg r10) (ind ~ofs:i rbx) ++
                     copy (i + 8)
                 in
                 copy 0)
        in
        (code ++ store, new_ofs)
      ) lhs (nop, total_size) in
      temp_code ++
      store_code ++
      addq (imm total_size) (reg rsp)
    end
  end else
    nop

and compile_call fn args =
  let arg_types = get_types_list args in
  let num_args = List.length arg_types in
  let num_rets = List.length fn.fn_typ in
  let ret_space = num_rets * 8 in
  let stack_args = if num_args > 6 then num_args - 6 else 0 in
  let stack_arg_space = stack_args * 8 in
  let total_stack = ret_space + stack_arg_space in
  let padding = if total_stack mod 16 <> 0 then 8 else 0 in
  (if padding > 0 then subq (imm padding) (reg rsp) else nop) ++
  (if ret_space > 0 then subq (imm ret_space) (reg rsp) else nop) ++
  (if List.length args = 1 && List.length arg_types > 1 then begin
    let e = List.hd args in
    compile_expr e ++
    movq (reg rax) (reg r12) ++
    (let result, _ = List.fold_left (fun (code, idx) _ ->
      let code =
        if idx < 6 then
          code ++ movq (ind ~ofs:(8 * idx) r12) (reg param_regs.(idx))
        else
          code ++ movq (ind ~ofs:(8 * idx) r12) (reg r10) ++
          pushq (reg r10)
      in
      (code, idx + 1)
    ) (nop, 0) arg_types in result)
  end else begin
    let push_stack_args =
      if num_args > 6 then
        let stack_arg_exprs = List.filteri (fun i _ -> i >= 6) args in
        let stack_arg_exprs_rev = List.rev stack_arg_exprs in
        List.fold_left (fun code e ->
          code ++
          compile_expr e ++
          pushq (reg rax)
        ) nop stack_arg_exprs_rev
      else
        nop
    in
    let load_reg_args =
      let reg_arg_exprs = List.filteri (fun i _ -> i < 6) args in
      let n = List.length reg_arg_exprs in
      if n = 0 then nop
      else begin
        let push_all = List.fold_left (fun code e ->
          code ++ compile_expr e ++ pushq (reg rax)
        ) nop reg_arg_exprs in
        let pop_to_regs =
          let rec pop_loop i =
            if i < 0 then nop
            else popq param_regs.(i) ++ pop_loop (i - 1)
          in
          pop_loop (n - 1)
        in
        push_all ++ pop_to_regs
      end
    in
    push_stack_args ++ load_reg_args
  end) ++
  call ("F_" ^ fn.fn_name) ++
  (if stack_arg_space > 0 then addq (imm stack_arg_space) (reg rsp) else nop) ++
  (if num_rets = 0 then
     (if ret_space > 0 then addq (imm ret_space) (reg rsp) else nop) ++
     (if padding > 0 then addq (imm padding) (reg rsp) else nop)
   else if num_rets = 1 then
     popq rax ++
     (if padding > 0 then addq (imm padding) (reg rsp) else nop)
   else
     movq (reg rsp) (reg rax) ++
     (if padding > 0 then addq (imm padding) (reg rsp) else nop))

let compile_decl = function
  | TDfunction (fn, body) ->
      current_fn_name := fn.fn_name;
      let num_params = List.length fn.fn_params in
      let num_rets = List.length fn.fn_typ in
      List.iteri (fun i v ->
        if i < 6 then
          v.v_ofs <- -8 * (i + 1)
        else
          v.v_ofs <- 16 + 8 * (num_rets + (i - 6))
      ) fn.fn_params;
      let param_space = 8 * (min num_params 6) in
      let local_ofs = allocate_locals_expr (-param_space) body in
      let frame_size = -local_ofs in
      let aligned_frame = if frame_size mod 16 = 0 then frame_size else frame_size + 8 in
      label ("F_" ^ fn.fn_name) ++
      pushq (reg rbp) ++
      movq (reg rsp) (reg rbp) ++
      (if aligned_frame > 0 then subq (imm aligned_frame) (reg rsp) else nop) ++
      iter2 (fun i v ->
        if i < 6 then
          movq (reg param_regs.(i)) (ind ~ofs:v.v_ofs rbp)
        else
          nop
      ) (List.mapi (fun i v -> i) fn.fn_params) fn.fn_params ++
      compile_expr body ++
      label ("F_" ^ fn.fn_name ^ "_ret") ++
      movq (reg rbp) (reg rsp) ++
      popq rbp ++
      ret
  | TDstruct s ->
      allocate_struct_fields s;
      nop

let file ?debug:(b=false) (dl: Tast.tfile): X86_64.program =
  debug := b;
  List.iter (function TDstruct s -> allocate_struct_fields s | _ -> ()) dl;
  let func_code = iter compile_decl dl in
  let string_data =
    Hashtbl.fold (fun s lbl acc ->
      acc ++ label lbl ++ string s
    ) strings nop
  in
  { text =
        globl "main" ++ label "main" ++
        call "F_main" ++
        xorq (reg rax) (reg rax) ++
        ret ++
        func_code ++
        label "graceful_stop" ++
        movq (imm 1) (reg rdi) ++
        call "exit_"
    ++ inline "
"
    ++ aligned_call_wrapper ~f:"malloc" ~newf:"malloc_"
    ++ aligned_call_wrapper ~f:"calloc" ~newf:"calloc_"
    ++ aligned_call_wrapper ~f:"printf" ~newf:"printf_"
    ++ aligned_call_wrapper ~f:"exit" ~newf:"exit_"
  ;
  data =
    string_data
  ;
  }
