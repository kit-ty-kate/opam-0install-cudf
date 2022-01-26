module Context = struct
  type rejection = UserConstraint of Cudf_types.vpkg

  type t = {
    universe : Cudf.universe;
    constraints : (Cudf_types.pkgname * (Cudf_types.relop * Cudf_types.version)) list;
    version_rev_compare : Cudf.package -> Cudf.package -> int;
    fresh_id : unit -> int;
  }

  let user_restrictions t name =
    List.fold_left (fun acc (name', c) ->
      if String.equal name name' then
        c :: acc
      else
        acc
    ) [] t.constraints

  let candidates t name =
    let user_constraints = user_restrictions t name in
    match Cudf.lookup_packages t.universe name with
    | [] ->
        [] (* Package not found *)
    | versions ->
        List.map (fun pkg ->
          let rec check_constr = function
            | [] -> (pkg.Cudf.version, Ok pkg)
            | (op, v)::c ->
                if Model.fop op pkg.Cudf.version v then
                  check_constr c
                else
                  (pkg.Cudf.version, Error (UserConstraint (name, Some (op, v))))  (* Reject *)
          in
          check_constr user_constraints
        ) (List.fast_sort t.version_rev_compare versions) (* Higher versions are preferred. *)

  let print_constr = function
    | None -> ""
    | Some (`Eq, v) -> "="^string_of_int v
    | Some (`Neq, v) -> "!="^string_of_int v
    | Some (`Geq, v) -> ">="^string_of_int v
    | Some (`Gt, v) -> ">"^string_of_int v
    | Some (`Leq, v) -> "<="^string_of_int v
    | Some (`Lt, v) -> "<"^string_of_int v

  let pp_rejection f = function
    | UserConstraint (name, c) -> Format.fprintf f "Rejected by user-specified constraint %s%s" name (print_constr c)

  let fresh_id {fresh_id; _} = fresh_id ()
end

module Input = Model.Make(Context)

let requirements ~context pkgs =
  let role =
    let impl = Input.virtual_impl ~context ~depends:pkgs () in
    Input.virtual_role ~context [impl]
  in
  { Input.role; command = None }

module Solver = Zeroinstall_solver.Make(Input)
module Diagnostics = Zeroinstall_solver.Diagnostics(Solver.Output)

type t = Context.t
type selections = Solver.Output.t
type diagnostics = Input.requirements   (* So we can run another solve *)

let version_rev_compare ~prefer_oldest =
  if prefer_oldest then
    fun pkg1 pkg2 ->
      Int.compare pkg1.Cudf.version pkg2.Cudf.version
  else
    fun pkg1 pkg2 ->
      Int.compare pkg2.Cudf.version pkg1.Cudf.version

let create_fun_id_fun () =
  let r = ref 0 in
  fun () ->
    Stdlib.incr r;
    !r

let create ?(prefer_oldest=false) ~constraints universe =
  {
    Context.universe;
    constraints;
    version_rev_compare = version_rev_compare ~prefer_oldest;
    fresh_id = create_fun_id_fun ();
  }

let solve context pkgs =
  let req = requirements ~context pkgs in
  match Solver.do_solve ~closest_match:false req with
  | Some sels -> Ok sels
  | None -> Error req

let diagnostics ?verbose req =
  Diagnostics.get_failure_reason ?verbose
    (Option.get (Solver.do_solve req ~closest_match:true))

let packages_of_result sels =
  Solver.Output.RoleMap.fold (fun _role sel acc ->
    match Input.version (Solver.Output.unwrap sel) with
    | None -> acc
    | Some v -> v :: acc
  ) (Solver.Output.to_map sels) []
