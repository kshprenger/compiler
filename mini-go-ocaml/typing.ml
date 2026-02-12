(** Static type checking of Mini Go programs *)

open Format
open Lib
open Ast
open Tast

let debug = ref false

let dummy_loc = Lexing.dummy_pos, Lexing.dummy_pos

exception Error of Ast.location * string

let errorm ?(loc=dummy_loc) f =
  Format.kasprintf (fun s -> raise (Error (loc, s))) ("@[" ^^ f ^^ "@]")

let new_var : string -> Ast.location -> typ -> var =
  let id = ref 0 in
  fun x loc ty ->
    incr id;
    { v_name = x; v_id = !id; v_loc = loc; v_typ = ty;
      v_used = false; v_addr = false; v_ofs= -1 }

(** Check if two types are equal *)
let rec types_equal (t1: Tast.typ) (t2: Tast.typ) : bool =
  match t1, t2 with
  | Tint, Tint -> true
  | Tbool, Tbool -> true
  | Tstring, Tstring -> true
  | Tptr t1', Tptr t2' -> types_equal t1' t2'
  | Tstruct s1, Tstruct s2 -> s1.s_name = s2.s_name
  | Tnil, Tptr _ | Tptr _, Tnil -> true  (* nil is compatible with any pointer *)
  | Tnil, Tnil -> true
  | Tmany l1, Tmany l2 ->
      List.length l1 = List.length l2 && List.for_all2 types_equal l1 l2
  | _, _ -> false

(** Check if a type is assignable to another (for nil compatibility) *)
let type_assignable ~(to_typ: Tast.typ) ~(from_typ: Tast.typ) : bool =
  match from_typ, to_typ with
  | Tnil, Tptr _ -> true
  | _, _ -> types_equal to_typ from_typ

let rec typ_of_ptyp (env_structs: (string, structure) Hashtbl.t) (pt: Ast.ptyp) : Tast.typ =
  match pt with
  | Ast.PTident id ->
      (match id.id with
       | "int" -> Tast.Tint
       | "bool" -> Tast.Tbool
       | "string" -> Tast.Tstring
       | struct_name ->
           (match Hashtbl.find_opt env_structs struct_name with
            | Some s -> Tast.Tstruct s
            | None -> errorm ~loc:id.loc "unknown type %s" struct_name))
  | Ast.PTptr inner ->
      Tast.Tptr (typ_of_ptyp env_structs inner)

(** Check if an expression always reaches a return statement *)
let rec returns (e: Tast.expr) : bool =
  match e.expr_desc with
  | TEreturn _ -> true
  | TEblock el ->
      (* A block returns if any statement in it returns unconditionally *)
      List.exists returns el
  | TEif (_, e_then, e_else) ->
      (* if-then-else returns if both branches return *)
      returns e_then && returns e_else
  | TEfor (_, _) ->
      (* A for loop may never execute, so it doesn't guarantee return *)
      false
  | _ -> false

(** Type an expression in environments:
    - env_structs: structure definitions
    - env_funcs: function definitions
    - env_vars: local variables in scope
    - return_types: expected return types for the current function
*)
let rec type_expr
    (env_structs: (string, structure) Hashtbl.t)
    (env_funcs: (string, function_) Hashtbl.t)
    (env_vars: (string, var) Hashtbl.t)
    (return_types: typ list)
    (pe: Ast.pexpr) : Tast.expr =
  let loc = pe.pexpr_loc in
  match pe.pexpr_desc with
  | Ast.PEnil ->
      { expr_desc = Tast.TEnil; expr_typ = Tast.Tnil }
  | Ast.PEskip ->
      { expr_desc = Tast.TEskip; expr_typ = Tast.Tmany [] }
  | Ast.PEconstant c ->
      let typ = match c with
        | Ast.Cbool _ -> Tast.Tbool
        | Ast.Cint _ -> Tast.Tint
        | Ast.Cstring _ -> Tast.Tstring
      in
      { expr_desc = Tast.TEconstant c; expr_typ = typ }

  | Ast.PEident id ->
      if id.id = "_" then
        errorm ~loc "cannot use _ as value"
      else
        (match Hashtbl.find_opt env_vars id.id with
         | Some v ->
             v.v_used <- true;
             { expr_desc = Tast.TEident v; expr_typ = v.v_typ }
         | None -> errorm ~loc "undefined variable %s" id.id)

  | Ast.PEblock exprs ->
      let typed_exprs = List.map (type_expr env_structs env_funcs env_vars return_types) exprs in
      { expr_desc = Tast.TEblock typed_exprs; expr_typ = Tast.Tmany [] }

  | Ast.PEcall (func_id, args) ->
      if func_id.id = "fmt.Print" then
        let typed_args = List.map (type_expr env_structs env_funcs env_vars return_types) args in
        { expr_desc = Tast.TEprint typed_args; expr_typ = Tast.Tmany [] }
      else
        (match Hashtbl.find_opt env_funcs func_id.id with
         | Some fn ->
             let typed_args = List.map (type_expr env_structs env_funcs env_vars return_types) args in
             (* Check arguments number *)
             if List.length typed_args <> List.length fn.fn_params then
               errorm ~loc "function %s expects %d arguments, got %d"
                 func_id.id (List.length fn.fn_params) (List.length typed_args);
             (* Check arguments types *)
             List.iter2 (fun arg param ->
               if not (type_assignable ~to_typ:param.v_typ ~from_typ:arg.expr_typ) then
                 errorm ~loc "type mismatch in argument to %s" func_id.id
             ) typed_args fn.fn_params;
             let result_typ = match fn.fn_typ with
               | [] -> Tmany []
               | [t] -> t
               | ts -> Tmany ts
             in
             { expr_desc = Tast.TEcall (fn, typed_args); expr_typ = result_typ }
         | None -> errorm ~loc "undefined function %s" func_id.id)

  | Ast.PEreturn exprs ->
      let typed_exprs = List.map (type_expr env_structs env_funcs env_vars return_types) exprs in
      (* Return should have correct number of values *)
      if List.length typed_exprs <> List.length return_types then
        errorm ~loc "return expects %d value(s), got %d"
          (List.length return_types) (List.length typed_exprs);
      (* Each returned value should have the correct type *)
      List.iter2 (fun expr expected_typ ->
        if not (type_assignable ~to_typ:expected_typ ~from_typ:expr.expr_typ) then
          errorm ~loc "return type mismatch: expected %a, got different type"
            (fun _ _ -> ()) ()
      ) typed_exprs return_types;
      { expr_desc = Tast.TEreturn typed_exprs; expr_typ = Tast.Tmany [] }

  | Ast.PEif (cond, then_branch, else_branch) ->
      let typed_cond = type_expr env_structs env_funcs env_vars return_types cond in
      if not (types_equal typed_cond.expr_typ Tbool) then
        errorm ~loc:cond.pexpr_loc "condition must be boolean";
      let typed_then = type_expr env_structs env_funcs env_vars return_types then_branch in
      let typed_else = type_expr env_structs env_funcs env_vars return_types else_branch in
      { expr_desc = Tast.TEif (typed_cond, typed_then, typed_else); expr_typ = Tast.Tmany [] }

  | Ast.PEfor (cond, body) ->
      let typed_cond = type_expr env_structs env_funcs env_vars return_types cond in
      (* Empty condition means infinite loop (for {}) - treated as true *)
      (match cond.pexpr_desc with
       | PEskip -> ()
       | _ -> if not (types_equal typed_cond.expr_typ Tbool) then
                errorm ~loc:cond.pexpr_loc "for condition must be boolean");
      let typed_body = type_expr env_structs env_funcs env_vars return_types body in
      { expr_desc = Tast.TEfor (typed_cond, typed_body); expr_typ = Tast.Tmany [] }

  | Ast.PEvars (ids, ptyp_opt, init_exprs) ->
      (* Handle variable declarations: var x, y T = e1, e2 or x, y := e1, e2 *)
      let typed_inits = List.map (type_expr env_structs env_funcs env_vars return_types) init_exprs in
      let vars = List.mapi (fun i id ->
        let typ = match ptyp_opt with
          | Some pt -> typ_of_ptyp env_structs pt
          | None ->
              if i < List.length typed_inits then
                (List.nth typed_inits i).expr_typ
              else
                errorm ~loc:id.loc "cannot infer type for %s" id.id
        in
        if id.id <> "_" then begin
          if Hashtbl.mem env_vars id.id then
            errorm ~loc:id.loc "variable %s already declared" id.id;
          let v = new_var id.id id.loc typ in
          Hashtbl.add env_vars id.id v;
          v
        end else
          new_var "_" id.loc typ
      ) ids in
      { expr_desc = Tast.TEvars vars; expr_typ = Tast.Tmany [] }

  | _ -> failwith "type_expr: not yet implemented"

(** Check that all local variables (except _) are used *)
let check_unused_variables (env_vars: (string, var) Hashtbl.t) : unit =
  Hashtbl.iter (fun name v ->
    if name <> "_" && not v.v_used then
      errorm ~loc:v.v_loc "variable %s declared but not used" name
  ) env_vars

let construct_single_typed_declaration
    (env_structs: (string, structure) Hashtbl.t)
    (env_funcs: (string, function_) Hashtbl.t)
    (decl: Ast.pdecl) : Tast.tdecl =
  match decl with
  | Ast.PDfunction pfunc ->
      let func_name = pfunc.pf_name.id in
      let func_loc = pfunc.pf_name.loc in

      if Hashtbl.mem env_funcs func_name then
        errorm ~loc:func_loc "second definition of function %s" func_name;

      (* Local vars environment for function *)
      let env_vars : (string, var) Hashtbl.t = Hashtbl.create 16 in

      (* Params *)
      let params = List.map (fun ((param_id : Ast.ident), ptyp) ->
        let param_typ = typ_of_ptyp env_structs ptyp in
        let v = new_var param_id.id param_id.loc param_typ in
        if param_id.id <> "_" then begin  (*Golang's underscore *)
          if Hashtbl.mem env_vars param_id.id then
            errorm ~loc:param_id.loc "duplicate parameter %s" param_id.id;
          Hashtbl.add env_vars param_id.id v;
          (* Params considered used (they come from caller) *)
          v.v_used <- true
        end;
        v
      ) pfunc.pf_params in

      let return_types = List.map (typ_of_ptyp env_structs) pfunc.pf_typ in

      let func = {
        Tast.fn_name = func_name;
        fn_params = params;
        fn_typ = return_types;
      } in

      (* Adding function to environment before typing body (for recursion) *)
      Hashtbl.add env_funcs func_name func;

      let typed_body = type_expr env_structs env_funcs env_vars return_types pfunc.pf_body in

      (* If function has return values, all paths must reach return *)
      if List.length return_types > 0 && not (returns typed_body) then
        errorm ~loc:func_loc "function %s: not all control paths return a value" func_name;

      (* All local variables (except underscore) must be used *)
      (* Note: we only check variables added in the body, not params *)
      Hashtbl.iter (fun name v ->
        if name <> "_" && not v.v_used then
          errorm ~loc:v.v_loc "variable %s declared but not used" name
      ) env_vars;

      Tast.TDfunction (func, typed_body)

  | Ast.PDstruct pstruct ->
      (* TODO *)
      failwith "struct typing not yet implemented"

let file ~debug:b (imp, dl : Ast.pfile) : Tast.tfile =
  debug := b;
  let env_structs : (string, structure) Hashtbl.t = Hashtbl.create 16 in
  let env_funcs : (string, function_) Hashtbl.t = Hashtbl.create 16 in

  let result = List.map (fun decl ->
    construct_single_typed_declaration env_structs env_funcs decl
  ) dl in

  result
