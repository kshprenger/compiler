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
  | TEprint el ->
      iter compile_print el
  | TEblock el ->
      iter compile_expr el
  | TEreturn [] ->
      nop
  | _ ->
      failwith "compile_expr: not yet implemented"

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
          call "F_main" ++  (* Call Go's main function *)
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
