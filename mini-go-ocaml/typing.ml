
(** Static type checking of Mini Go programs (TODO) *)

open Format
open Lib
open Ast
open Tast

let debug = ref false

let dummy_loc = Lexing.dummy_pos, Lexing.dummy_pos

exception Error of Ast.location * string

(** use this function to report errors; it is a printf-like function, eg.

    errorm ~loc "bad arity %d for function %s" n f

*)
let errorm ?(loc=dummy_loc) f =
  Format.kasprintf (fun s -> raise (Error (loc, s))) ("@[" ^^ f ^^ "@]")

(** use this function to create variable, so that they all have a
    unique id if field `v_id` *)
let new_var : string -> Ast.location -> typ -> var =
  let id = ref 0 in
  fun x loc ty ->
    incr id;
    { v_name = x; v_id = !id; v_loc = loc; v_typ = ty;
      v_used = false; v_addr = false; v_ofs= -1 }


let rec typ_of_ptyp (ctx: (string, int) Hashtbl.t) (pt: Ast.ptyp) : Tast.typ =
  match pt with
  | Ast.PTident id ->
      (match id.id with
       | "int" -> Tast.Tint
       | "bool" -> Tast.Tbool
       | "string" -> Tast.Tstring
       | struct_name ->
           errorm ~loc:id.loc "unknown type %s" struct_name)
  | Ast.PTptr inner ->
      Tast.Tptr (typ_of_ptyp ctx inner)

let rec type_expr (ctx: (string, int) Hashtbl.t) (pe: Ast.pexpr) : Tast.expr =
  match pe.pexpr_desc with
  | Ast.PEskip ->
      { expr_desc = Tast.TEskip; expr_typ = Tast.Tmany [] }
  | Ast.PEconstant c ->
      let typ = match c with
        | Ast.Cbool _ -> Tast.Tbool
        | Ast.Cint _ -> Tast.Tint
        | Ast.Cstring _ -> Tast.Tstring
      in
      { expr_desc = Tast.TEconstant c; expr_typ = typ }
  | Ast.PEblock exprs ->
      let typed_exprs = List.map (type_expr ctx) exprs in
      { expr_desc = Tast.TEblock typed_exprs; expr_typ = Tast.Tmany [] }
  | Ast.PEcall (func_id, args) ->
      (* Special case for fmt.Print - it becomes TEprint *)
      if func_id.id = "fmt.Print" then
        let typed_args = List.map (type_expr ctx) args in
        { expr_desc = Tast.TEprint typed_args; expr_typ = Tast.Tmany [] }
      else
      (* todo *)
        failwith ("type_expr: unknown function " ^ func_id.id)
  | Ast.PEnil ->
      { expr_desc = Tast.TEnil; expr_typ = Tast.Tnil }
  | Ast.PEreturn exprs ->
      let typed_exprs = List.map (type_expr ctx) exprs in
      { expr_desc = Tast.TEreturn typed_exprs; expr_typ = Tast.Tmany [] }
  | _ -> failwith "type_expr: not yet implemented"




let construct_single_typed_declaration (ctx: (string, int) Hashtbl.t) (decl: Ast.pdecl): Tast.tdecl =
  match decl with
  | Ast.PDfunction pfunc ->
      let params = List.map (fun ((param_id : Ast.ident), ptyp) ->
        let param_typ = typ_of_ptyp ctx ptyp in
        new_var param_id.id param_id.loc param_typ
      ) pfunc.pf_params in

      let return_types = List.map (typ_of_ptyp ctx) pfunc.pf_typ in

      let func = {
        Tast.fn_name = pfunc.pf_name.id;
        fn_params = params;
        fn_typ = return_types;
      } in

      let typed_body = type_expr ctx pfunc.pf_body in

      Tast.TDfunction (func, typed_body)

    | Ast.PDstruct pstruct -> failwith "todo"
;;

let file ~debug:b (imp, dl : Ast.pfile) : Tast.tfile =
  debug := b;
  let result = ref [] in
  let ctx : (string, int) Hashtbl.t = Hashtbl.create 100 in
  List.iter (fun declaration ->
    let typed_declaration = construct_single_typed_declaration  ctx declaration in
      result := typed_declaration :: !result
  ) dl;

  !result
