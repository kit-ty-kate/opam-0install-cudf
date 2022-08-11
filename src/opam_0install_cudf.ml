let tagged_with_avoid_version pkg =
  List.exists (function
    | "avoid-version", (`Int 1 | `Bool true) -> true
    | _ -> false
  ) pkg.Cudf.pkg_extra

let version_rev_compare ~prefer_oldest ~handle_avoid_version ~prefer_installed =
  (* cmp ordered from least important to most important setting *)
  let cmp =
    if prefer_oldest then
      fun pkg1 pkg2 -> Int.compare pkg1.Cudf.version pkg2.Cudf.version
    else
      fun pkg1 pkg2 -> Int.compare pkg2.Cudf.version pkg1.Cudf.version
  in
  let cmp =
    if handle_avoid_version then
      fun pkg1 pkg2 ->
        match tagged_with_avoid_version pkg1, tagged_with_avoid_version pkg2 with
        | true, true | false, false -> cmp pkg1 pkg2
        | true, false when pkg1.Cudf.installed -> cmp pkg1 pkg2
        | false, true when pkg2.Cudf.installed -> cmp pkg1 pkg2
        | true, false -> 1
        | false, true -> -1
    else
      cmp
  in
  let cmp =
    if prefer_installed then
      fun pkg1 pkg2 ->
        match pkg1.Cudf.installed, pkg2.Cudf.installed with
        | true, true | false, false -> cmp pkg1 pkg2
        | true, false -> -1
        | false, true -> 1
    else
      cmp
  in
  cmp

module Context = struct
  type rejection = UserConstraint of Cudf_types.vpkg

  type t = {
    universe : Cudf.universe;
    constraints : (Cudf_types.pkgname * (Cudf_types.relop * Cudf_types.version)) list;
    fresh_id : int ref;
    version_rev_compare : Cudf.package -> Cudf.package -> int;
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
        List.fast_sort t.version_rev_compare versions (* Higher versions are preferred. *)
        |> List.map (fun pkg ->
          let rec check_constr = function
            | [] -> (pkg.Cudf.version, Ok pkg)
            | ((op, v)::c) ->
                if Model.fop op pkg.Cudf.version v then
                  check_constr c
                else
                  (pkg.Cudf.version, Error (UserConstraint (name, Some (op, v))))  (* Reject *)
          in
          check_constr user_constraints
        )

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

  let fresh_id {fresh_id; _} =
    incr fresh_id;
    !fresh_id
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

let create ?(prefer_oldest=false) ?(handle_avoid_version=true) ?(prefer_installed=false) ~constraints universe =
  {
    Context.universe;
    constraints;
    fresh_id = ref 0;
    version_rev_compare = version_rev_compare ~prefer_oldest ~handle_avoid_version ~prefer_installed;
  }

let solve context pkgs =
  let req = requirements ~context pkgs in
  match Solver.do_solve ~closest_match:false req with
  | Some sels -> Ok sels
  | None -> Error req

let packages_of_result sels =
  sels
  |> Solver.Output.to_map |> Solver.Output.RoleMap.to_seq |> List.of_seq
  |> List.filter_map (fun (_role, sel) -> Input.version (Solver.Output.unwrap sel))

module Raw_diagnostics = struct
  type restriction = Input.restriction = {
    kind : [`Ensure | `Prevent];
    expr : (Cudf_types.relop * Cudf_types.version) list;
  }

  type role =
    | Real of Cudf_types.pkgname
    | Virtual of impl list
  and real_impl = {
    pkg : Cudf.package;
    requires : dependency list;
  }
  and dependency = {
    drole : role;
    importance : [`Essential | `Recommended | `Restricts];
    restrictions : restriction list;
  }
  and impl =
    | RealImpl of real_impl
    | VirtualImpl of dependency list
    | Reject of (Cudf_types.pkgname * Cudf_types.version)
    | Dummy

  type rejection_reason =
    | ModelRejection of Cudf_types.vpkg
    | FailsRestriction of restriction
    | DepFailsRestriction of dependency * restriction
    | ConflictsRole of role
    | DiagnosticsFailure of string

  type reject = impl * rejection_reason
  type candidates = reject list * [`All_unusable | `No_candidates | `Conflicts]

  type outcome =
    | SelectedImpl of impl
    | RejectedCandidates of candidates

  type note =
    | UserRequested of restriction
    | ReplacesConflict of role
    | ReplacedByConflict of role
    | Restricts of role * impl * restriction list
    | Feed_problem of string

  type t = {
    role : role;
    outcome : outcome;
    notes : note list;
  }

  let rec map_role = function
    | Input.Real {context = _; name} -> Real name
    | Input.Virtual (_, impls) -> Virtual (List.map map_impl impls)
  and map_impl = function
    | Input.RealImpl {pkg; requires} -> RealImpl {pkg; requires = List.map map_dependency requires}
    | Input.VirtualImpl (_, dependencies) -> VirtualImpl (List.map map_dependency dependencies)
    | Input.Reject pkg -> Reject pkg
    | Input.Dummy -> Dummy
  and map_dependency {drole; importance; restrictions} =
    { drole = map_role drole; importance; restrictions}

  let map_note = function
    | Diagnostics.Note.UserRequested restriction -> UserRequested restriction
    | Diagnostics.Note.ReplacesConflict role -> ReplacesConflict (map_role role)
    | Diagnostics.Note.ReplacedByConflict role -> ReplacedByConflict (map_role role)
    | Diagnostics.Note.Restricts (role, impl, restrictions) -> Restricts (map_role role, map_impl impl, restrictions)
    | Diagnostics.Note.RequiresCommand _ -> assert false (* NOTE: the current implementation does not have any commands *)
    | Diagnostics.Note.Feed_problem msg -> Feed_problem msg

  let map_reason = function
    | `Model_rejection (Context.UserConstraint rejection) -> ModelRejection rejection
    | `FailsRestriction restriction -> FailsRestriction restriction
    | `DepFailsRestriction (dependency, restriction) -> DepFailsRestriction (map_dependency dependency, restriction)
    | `MachineGroupConflict _ -> assert false (* NOTE: the current implementation does not have any machine groups *)
    | `ClassConflict _ -> assert false (* NOTE: the current implementation does not have any class-conflicts *)
    | `ConflictsRole role -> ConflictsRole (map_role role)
    | `MissingCommand _ -> assert false (* NOTE: the current implementation does not have any commands *)
    | `DiagnosticsFailure msg -> DiagnosticsFailure msg

  let map_reject (impl, reason) =
    (map_impl impl, map_reason reason)

  let map_candidates (rejects, kind) =
    (List.map map_reject rejects, kind)

  let get_aux req =
    Solver.do_solve req ~closest_match:true
    |> Option.get

  let get req =
    get_aux req |>
    Diagnostics.of_result |>
    Solver.Output.RoleMap.bindings |>
    List.map (fun (_role, component) ->
      let selected_impl = Option.map map_impl (Diagnostics.Component.selected_impl component) in
      {
        role = map_role (Diagnostics.Component.role component);
        outcome = begin match selected_impl with
          | Some selected_impl -> SelectedImpl selected_impl
          | None -> RejectedCandidates (map_candidates (Diagnostics.Component.rejects component))
        end;
        notes = List.map map_note (Diagnostics.Component.notes component);
      }
    )
end

let diagnostics ?verbose req =
  Raw_diagnostics.get_aux req |> Diagnostics.get_failure_reason ?verbose
