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

let rec types_equal (t1: Tast.typ) (t2: Tast.typ) : bool =
  match t1, t2 with
  | Tint, Tint -> true
  | Tbool, Tbool -> true
  | Tstring, Tstring -> true
  | Tptr t1', Tptr t2' -> types_equal t1' t2'
  | Tstruct s1, Tstruct s2 -> s1.s_name = s2.s_name
  | Tnil, Tptr _ | Tptr _, Tnil -> true  (* nil == NULL - compatible *)
  | Tnil, Tnil -> true
  | Tmany l1, Tmany l2 ->
      List.length l1 = List.length l2 && List.for_all2 types_equal l1 l2
  | _, _ -> false

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
            | None -> errorm ~loc:id.loc "Unknown type %s" struct_name))
  | Ast.PTptr inner ->
      Tast.Tptr (typ_of_ptyp env_structs inner)

let rec is_returns (e: Tast.expr) : bool =
  match e.expr_desc with
  | TEreturn _ -> true
  | TEblock el ->
      List.exists is_returns el
  | TEif (_, e_then, e_else) ->
      is_returns e_then && is_returns e_else
  | TEfor (_, _) ->
      false (*TODO?????*)
  | _ -> false

let rec is_lvalue (pe: Ast.pexpr) : bool =
  match pe.pexpr_desc with
  | PEident id -> id.id <> "_"  (* skip this one *)
  | PEdot (e, _) -> true
  | PEunop (Ustar, _) -> true
  | _ -> false

let get_types (e: Tast.expr) : typ list =
  match e.expr_typ with
  | Tmany tys -> tys
  | t -> [t]

let fmt_used = ref false

let rec type_expr
    (env_structs: (string, structure) Hashtbl.t)
    (env_funcs: (string, function_) Hashtbl.t)
    (env_vars: (string, var) Hashtbl.t list)
    (return_types: typ list)
    (has_fmt: bool)
    (pe: Ast.pexpr) : Tast.expr =
  let loc = pe.pexpr_loc in
  let find_var name =
    let rec search = function
      | [] -> None
      | env :: rest ->
          match Hashtbl.find_opt env name with
          | Some v -> Some v
          | None -> search rest
    in
    search env_vars
  in
  let add_var name v =
    match env_vars with
    | [] -> failwith "No scope"
    | env :: _ -> Hashtbl.add env name v
  in
  let mem_current_scope name =
    match env_vars with
    | [] -> false
    | env :: _ -> Hashtbl.mem env name
  in
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
        errorm ~loc "Cannot use _ as value"
      else
        (match find_var id.id with
         | Some v ->
             v.v_used <- true;
             { expr_desc = Tast.TEident v; expr_typ = v.v_typ }
         | None -> errorm ~loc "Undefined var %s" id.id)

  | Ast.PEblock exprs ->
      let new_scope = Hashtbl.create 16 in
      let new_env_vars = new_scope :: env_vars in
      let typed_exprs = List.map (type_expr env_structs env_funcs new_env_vars return_types has_fmt) exprs in
      Hashtbl.iter (fun name v ->
        if name <> "_" && not v.v_used then
          errorm ~loc:v.v_loc "Variable %s declared but not used" name
      ) new_scope;
      { expr_desc = Tast.TEblock typed_exprs; expr_typ = Tast.Tmany [] }

  | Ast.PEcall (func_id, args) ->
      if func_id.id = "fmt.Print" then begin
        if not has_fmt then
          errorm ~loc "fmt.Print requires import \"fmt\"";
        fmt_used := true;
        let typed_args = List.map (type_expr env_structs env_funcs env_vars return_types has_fmt) args in
        { expr_desc = Tast.TEprint typed_args; expr_typ = Tast.Tmany [] }
      end
      else if func_id.id = "new" then begin
        match args with
        | [{ pexpr_desc = PEident type_id; _ }] ->
            let inner_typ = typ_of_ptyp env_structs (PTident type_id) in
            { expr_desc = Tast.TEnew inner_typ; expr_typ = Tast.Tptr inner_typ }
        | _ -> errorm ~loc "new - expects a type argument"
      end
      else
        (match Hashtbl.find_opt env_funcs func_id.id with
         | Some fn ->
             let typed_args = List.map (type_expr env_structs env_funcs env_vars return_types has_fmt) args in
             List.iter (fun arg ->
               match arg.expr_typ with
               | Tmany [] -> errorm ~loc "Cannot use no value as argument"
               | _ -> ()
             ) typed_args;
             let flattened_arg_types = List.concat_map get_types typed_args in
             if List.length flattened_arg_types <> List.length fn.fn_params then
               errorm ~loc "Function %s expects %d arguments, got %d"
                 func_id.id (List.length fn.fn_params) (List.length flattened_arg_types);
             List.iter2 (fun arg_typ param ->
               if not (type_assignable ~to_typ:param.v_typ ~from_typ:arg_typ) then
                 errorm ~loc "Type mismatch in argument to %s" func_id.id
             ) flattened_arg_types fn.fn_params;
             let result_typ = match fn.fn_typ with
               | [] -> Tmany []
               | [t] -> t
               | ts -> Tmany ts
             in
             { expr_desc = Tast.TEcall (fn, typed_args); expr_typ = result_typ }
         | None -> errorm ~loc "Undefined function %s" func_id.id)

  | Ast.PEreturn exprs ->
      let typed_exprs = List.map (type_expr env_structs env_funcs env_vars return_types has_fmt) exprs in
      let flattened_types = List.concat_map get_types typed_exprs in
      if List.length flattened_types <> List.length return_types then
        errorm ~loc "Return expects %d value(s), got %d"
          (List.length return_types) (List.length flattened_types);
      List.iter2 (fun ret_typ expected_typ ->
        if not (type_assignable ~to_typ:expected_typ ~from_typ:ret_typ) then
          errorm ~loc "Return type mismatch"
      ) flattened_types return_types;
      { expr_desc = Tast.TEreturn typed_exprs; expr_typ = Tast.Tmany [] }

  | Ast.PEif (cond, then_branch, else_branch) ->
      let typed_cond = type_expr env_structs env_funcs env_vars return_types has_fmt cond in
      if not (types_equal typed_cond.expr_typ Tbool) then
        errorm ~loc:cond.pexpr_loc "condition must be boolean";
      let typed_then = type_expr env_structs env_funcs env_vars return_types has_fmt then_branch in
      let typed_else = type_expr env_structs env_funcs env_vars return_types has_fmt else_branch in
      { expr_desc = Tast.TEif (typed_cond, typed_then, typed_else); expr_typ = Tast.Tmany [] }

  | Ast.PEfor (cond, body) ->
      let typed_cond = type_expr env_structs env_funcs env_vars return_types has_fmt cond in
      (* for {} <-> while true {} *)
      (match cond.pexpr_desc with
       | PEskip -> ()
       | _ -> if not (types_equal typed_cond.expr_typ Tbool) then
                errorm ~loc:cond.pexpr_loc "for condition must be boolean");
      let typed_body = type_expr env_structs env_funcs env_vars return_types has_fmt body in
      { expr_desc = Tast.TEfor (typed_cond, typed_body); expr_typ = Tast.Tmany [] }

  | Ast.PEvars (ids, ptyp_opt, init_exprs) ->
      let typed_inits = List.map (type_expr env_structs env_funcs env_vars return_types has_fmt) init_exprs in
      let flattened_init_types = List.concat_map get_types typed_inits in
      let num_ids = List.length ids in
      let num_inits = List.length flattened_init_types in
      if ptyp_opt <> None && num_inits > 0 && num_ids <> num_inits then
        errorm ~loc "Assignment count mismatch: %d = %d" num_ids num_inits;
      let vars = List.mapi (fun i id ->
        let typ = match ptyp_opt with
          | Some pt -> typ_of_ptyp env_structs pt
          | None ->
              if i < num_inits then begin
                let init_typ = List.nth flattened_init_types i in
                if init_typ = Tnil then
                  errorm ~loc:id.loc "Cannot deduce type from nil for %s" id.id;
                init_typ
              end
              else
                errorm ~loc:id.loc "Cannot deduce type for %s" id.id
        in
        if num_inits > 0 && i < num_inits then begin
          let init_typ = List.nth flattened_init_types i in
          if not (type_assignable ~to_typ:typ ~from_typ:init_typ) then
            errorm ~loc:id.loc "Type mismatch in initialization of %s" id.id
        end;
        if id.id <> "_" then begin
          if mem_current_scope id.id then
            errorm ~loc:id.loc "Variable %s already declared" id.id;
          let v = new_var id.id id.loc typ in
          add_var id.id v;
          v
        end else
          new_var "_" id.loc typ
      ) ids in
      { expr_desc = Tast.TEvars vars; expr_typ = Tast.Tmany [] }

  | Ast.PEbinop (op, e1, e2) ->
      let te1 = type_expr env_structs env_funcs env_vars return_types has_fmt e1 in
      let te2 = type_expr env_structs env_funcs env_vars return_types has_fmt e2 in
      let result_typ = match op with
        | Badd | Bsub | Bmul | Bdiv | Bmod ->
            if not (types_equal te1.expr_typ Tint && types_equal te2.expr_typ Tint) then
              errorm ~loc "Arithmetic operators require int operands";
            Tint
        | Beq | Bne ->
            if te1.expr_typ = Tnil && te2.expr_typ = Tnil then
              errorm ~loc "Cannot compare nil with nil";
            let compatible =
              types_equal te1.expr_typ te2.expr_typ ||
              (type_assignable ~to_typ:te1.expr_typ ~from_typ:te2.expr_typ) ||
              (type_assignable ~to_typ:te2.expr_typ ~from_typ:te1.expr_typ)
            in
            if not compatible then
              errorm ~loc "Cannot compare types";
            Tbool
        | Blt | Ble | Bgt | Bge ->
            if not (types_equal te1.expr_typ Tint && types_equal te2.expr_typ Tint) then
              errorm ~loc "Comparison operators require int operands";
            Tbool
        | Band | Bor ->
            if not (types_equal te1.expr_typ Tbool && types_equal te2.expr_typ Tbool) then
              errorm ~loc "Logical operators require bool operands";
            Tbool
      in
      { expr_desc = Tast.TEbinop (op, te1, te2); expr_typ = result_typ }

  | Ast.PEunop (op, e) ->
      let te = type_expr env_structs env_funcs env_vars return_types has_fmt e in
      let result_typ = match op with
        | Uneg ->
            if not (types_equal te.expr_typ Tint) then
              errorm ~loc "Unary minus requires int operand";
            Tint
        | Unot ->
            if not (types_equal te.expr_typ Tbool) then
              errorm ~loc "not requires bool operand";
            Tbool
        | Uamp ->
            (* Address-of operator: &x requires x to be an l-value *)
            (match e.pexpr_desc with
             | PEident id when id.id = "_" ->
                 errorm ~loc "Cannot take address of _"
             | PEident _ | PEdot _ | PEunop (Ustar, _) ->
                 (match te.expr_desc with
                  | TEident v -> v.v_addr <- true
                  | TEdot ({ expr_desc = TEident v; _ }, _) -> v.v_addr <- true
                  | _ -> ());
                 Tptr te.expr_typ
             | _ -> errorm ~loc "Cannot take address of this expression")
        | Ustar ->
            (match te.expr_typ with
             | Tptr inner_typ -> inner_typ
             | Tnil -> errorm ~loc "Cannot dereference nil"
             | _ -> errorm ~loc "Cannot dereference non-pointer type")
      in
      { expr_desc = Tast.TEunop (op, te); expr_typ = result_typ }

  | Ast.PEdot (e, field_id) ->
      let te = type_expr env_structs env_funcs env_vars return_types has_fmt e in
      let struct_typ = match te.expr_typ with
        | Tstruct s -> Tstruct s
        | Tptr (Tstruct s) -> Tstruct s
        | _ -> errorm ~loc "Field access on non-struct type"
      in
      (match struct_typ with
       | Tstruct s ->
           (match Hashtbl.find_opt s.s_fields field_id.id with
            | Some f ->
                { expr_desc = Tast.TEdot (te, f); expr_typ = f.f_typ }
            | None ->
                errorm ~loc "Struct %s has no field %s" s.s_name field_id.id)
       | _ -> failwith "unreachable")

  | Ast.PEassign (lhs_list, rhs_list) ->
      let typed_rhs = List.map (type_expr env_structs env_funcs env_vars return_types has_fmt) rhs_list in
      let flattened_rhs_types = List.concat_map get_types typed_rhs in
      if List.length lhs_list <> List.length flattened_rhs_types then
        errorm ~loc "Assignment count mismatch: %d = %d"
          (List.length lhs_list) (List.length flattened_rhs_types);
      let typed_lhs = List.mapi (fun i lhs ->
        match lhs.pexpr_desc with
        | PEident id when id.id = "_" ->
            let rhs_typ = List.nth flattened_rhs_types i in
            let v = new_var "_" id.loc rhs_typ in
            v.v_used <- true;
            { expr_desc = Tast.TEident v; expr_typ = rhs_typ }
        | _ ->
            let te = type_expr env_structs env_funcs env_vars return_types has_fmt lhs in
            if not (is_lvalue lhs) then
              errorm ~loc:lhs.pexpr_loc "cannot assign to this expression";
            te
      ) lhs_list in
      List.iter2 (fun te rhs_typ ->
        if not (type_assignable ~to_typ:te.expr_typ ~from_typ:rhs_typ) then
          errorm ~loc "type mismatch in assignment"
      ) typed_lhs flattened_rhs_types;
      { expr_desc = Tast.TEassign (typed_lhs, typed_rhs); expr_typ = Tast.Tmany [] }

  | Ast.PEincdec (e, incdec) ->
      let te = type_expr env_structs env_funcs env_vars return_types has_fmt e in
      if not (types_equal te.expr_typ Tint) then
        errorm ~loc "increment/decrement requires int operand";
      if not (is_lvalue e) then
        errorm ~loc "cannot increment/decrement this expression";
      { expr_desc = Tast.TEincdec (te, incdec); expr_typ = Tast.Tmany [] }

let check_unused_variables (env_vars: (string, var) Hashtbl.t) : unit =
  Hashtbl.iter (fun name v ->
    if name <> "_" && not v.v_used then
      errorm ~loc:v.v_loc "Variable %s declared but not used" name
  ) env_vars

let construct_single_typed_declaration
    (env_structs: (string, structure) Hashtbl.t)
    (env_funcs: (string, function_) Hashtbl.t)
    (has_fmt: bool)
    (decl: Ast.pdecl) : Tast.tdecl =
  match decl with
  | Ast.PDfunction pfunc ->
      let func_name = pfunc.pf_name.id in
      let func_loc = pfunc.pf_name.loc in

      if Hashtbl.mem env_funcs func_name then
        errorm ~loc:func_loc "Second definition of function %s" func_name;

      let env_vars : (string, var) Hashtbl.t = Hashtbl.create 16 in

      let params = List.map (fun ((param_id : Ast.ident), ptyp) ->
        let param_typ = typ_of_ptyp env_structs ptyp in
        let v = new_var param_id.id param_id.loc param_typ in
        if param_id.id <> "_" then begin  (*Golang's underscore *)
          if Hashtbl.mem env_vars param_id.id then
            errorm ~loc:param_id.loc "Duplicate parameter %s" param_id.id;
          Hashtbl.add env_vars param_id.id v;
          (* Params considered used *)
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

      let typed_body = type_expr env_structs env_funcs [env_vars] return_types has_fmt pfunc.pf_body in

      if List.length return_types > 0 && not (is_returns typed_body) then
        errorm ~loc:func_loc "Function %s: not all control paths return a value" func_name;

      Hashtbl.iter (fun name v ->
        if name <> "_" && not v.v_used then
          errorm ~loc:v.v_loc "Variable %s declared but not used" name
      ) env_vars;

      Tast.TDfunction (func, typed_body)

  | Ast.PDstruct pstruct ->
      let s = Hashtbl.find env_structs pstruct.ps_name.id in
      Tast.TDstruct s

let check_recursive_structs (env_structs: (string, structure) Hashtbl.t) : unit =
  (* Partial DFS traversing to recursive structs *)
  let rec check_from_type (origin: structure) (visited: string list) (typ: typ) (loc: Ast.location) : unit =
    match typ with
    | Tstruct s ->
        if s.s_name = origin.s_name then
          errorm ~loc "Recursive struct %s" origin.s_name;
        if not (List.mem s.s_name visited) then
          List.iter (fun f ->
            check_from_type origin (s.s_name :: visited) f.f_typ loc
          ) s.s_list
    | Tptr _ -> ()
    | _ -> ()
  in
  Hashtbl.iter (fun _ s ->
    List.iter (fun f ->
      check_from_type s [s.s_name] f.f_typ dummy_loc
    ) s.s_list
  ) env_structs

let file ~debug:b ((imp, dl) : Ast.pfile) : Tast.tfile =
  debug := b;
  fmt_used := false;
  let env_structs : (string, structure) Hashtbl.t = Hashtbl.create 16 in
  let env_funcs : (string, function_) Hashtbl.t = Hashtbl.create 16 in

  (* Phase 1: Add all structure names (without fields) to check uniqueness *)
  List.iter (fun decl ->
    match decl with
    | Ast.PDstruct pstruct ->
        let name = pstruct.ps_name.id in
        let loc = pstruct.ps_name.loc in
        if Hashtbl.mem env_structs name then
          errorm ~loc "Second definition of struct %s" name;
        let s = {
          s_name = name;
          s_fields = Hashtbl.create 16;
          s_list = [];
          s_size = 0;
        } in
        Hashtbl.add env_structs name s
    | _ -> ()
  ) dl;

  (* Phase 2: Add all structs fields *)
  List.iter (fun decl ->
    match decl with
    | Ast.PDstruct pstruct ->
        let s = Hashtbl.find env_structs pstruct.ps_name.id in
        let fields = List.map (fun ((field_id : Ast.ident), field_ptyp) ->
          let field_name = field_id.id in
          let field_loc = field_id.loc in
          if Hashtbl.mem s.s_fields field_name then
            errorm ~loc:field_loc "Duplicate field %s in struct %s" field_name s.s_name;
          let field_typ = typ_of_ptyp env_structs field_ptyp in
          let f = { f_name = field_name; f_typ = field_typ; f_ofs = 0 } in
          Hashtbl.add s.s_fields field_name f;
          f
        ) pstruct.ps_fields in
        s.s_list <- fields
    | _ -> ()
  ) dl;

  (*Phase 3: Check for recursive structs *)
  check_recursive_structs env_structs;

  (*Phase 4: Actual typing here *)
  let result = List.map (fun decl ->
    construct_single_typed_declaration env_structs env_funcs imp decl
  ) dl in

  (match Hashtbl.find_opt env_funcs "main" with
   | None -> errorm "missing main function"
   | Some main_fn ->
       if List.length main_fn.fn_params <> 0 then
         errorm "main function should have no parameters";
       if List.length main_fn.fn_typ <> 0 then
         errorm "main function should have no return values");

  if imp && not !fmt_used then
    errorm "fmt imported but not used";

  result
