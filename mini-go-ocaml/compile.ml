open Format
open Ast
open Tast
open X86_64

let debug = ref false

let iter f = List.fold_left (fun code x -> code ++ f x) nop
let iter2 f = List.fold_left2 (fun code x y -> code ++ f x y) nop

let new_label =
  let r = ref 0 in fun () -> incr r; "L_" ^ string_of_int !r

(* String constants labels *)
let strings = Hashtbl.create 17

let alloc_string s =
  if Hashtbl.mem strings s then
    Hashtbl.find strings s
  else begin
    let lbl = new_label () in
    Hashtbl.add strings s lbl;
    lbl
  end

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
  | TEprint el ->
      iter compile_print el
  | TEblock el ->
      iter compile_expr el
  | TEreturn [] ->
      nop
  | _ ->
      failwith "compile_expr: not yet implemented"

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
    movq (ind rax) (reg rax)
  | Uamp ->
    compile_addr e

and compile_addr e =
  match e.expr_desc with
  | TEident v ->
    leaq (ind ~ofs:v.v_ofs rbp) rax
  | TEdot (e1, f) ->
    (match e1.expr_typ with
      | Tptr _ ->
      compile_expr e1 ++
      (if f.f_ofs <> 0 then addq (imm f.f_ofs) (reg rax) else nop)
      | Tstruct _ ->
        compile_addr e1 ++
        (if f.f_ofs <> 0 then addq (imm f.f_ofs) (reg rax) else nop)
      | _ -> failwith "compile_addr: TEdot on non-struct type")
  | TEunop (Ustar, e1) ->
      (* Address of ptr is just ptr *)
      compile_expr e1
  | _ ->
      failwith "compile_addr: not an lvalue"

and compile_binop op e1 e2 =
  match op with
  | Badd | Bsub | Bmul | Bdiv | Bmod | Beq | Bne | Blt | Ble | Bgt | Bge ->
      compile_expr e1 ++
      pushq (reg rax) ++
      compile_expr e2 ++
      popq rbx ++
      (match op with
       | Badd -> addq (reg rbx) (reg rax)
       | Bsub ->
           movq (reg rax) (reg rcx) ++
           movq (reg rbx) (reg rax) ++
           subq (reg rcx) (reg rax)
       | Bmul -> imulq (reg rbx) (reg rax)
       | Bdiv | Bmod ->
           movq (reg rbx) (reg rax) ++
           cqto ++  (* sign extend rax into rdx:rax *)
           popq rbx ++  (* get divisor back *)
           idivq (reg rbx) ++
           (if op = Bmod then movq (reg rdx) (reg rax) else nop)
       | Beq | Bne | Blt | Ble | Bgt | Bge ->
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


and compile_print e = match e.expr_typ with
  | Tstring ->
      compile_expr e ++
      movq (reg rax) (reg rdi) ++
      call "printf_"
  | Tint ->
      let fmt_lbl = alloc_string "%ld" in
      compile_expr e ++
      movq (reg rax) (reg rsi) ++
      movq (ilab fmt_lbl) (reg rdi) ++
      xorq (reg rax) (reg rax) ++  (* rax = 0 for printf varargs *)
      call "printf_"
  | Tbool ->
      let fmt_lbl = alloc_string "%d" in
      compile_expr e ++
      movq (reg rax) (reg rsi) ++
      movq (ilab fmt_lbl) (reg rdi) ++
      xorq (reg rax) (reg rax) ++
      call "printf_"
  | _ ->
      failwith "compile_print: unsupported typ"

let compile_decl = function
  | TDfunction (f, body) ->
      label ("F_" ^ f.fn_name) ++
      pushq (reg rbp) ++
      movq (reg rsp) (reg rbp) ++
      compile_expr body ++
      movq (reg rbp) (reg rsp) ++
      popq rbp ++
      ret
  | TDstruct _ ->
      nop

let file ?debug:(b=false) (dl: Tast.tfile): X86_64.program =
  debug := b;
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
      inline "
# TODO some auxiliary assembly functions, if needed
"
  ++ aligned_call_wrapper ~f:"malloc" ~newf:"malloc_"
  ++ aligned_call_wrapper ~f:"calloc" ~newf:"calloc_"
  ++ aligned_call_wrapper ~f:"printf" ~newf:"printf_"
;
    data =
      string_data
    ;
  }
