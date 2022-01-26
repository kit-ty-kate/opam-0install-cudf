(* Note: changes to this file may require similar changes to lib/model.ml *)

let fop : Cudf_types.relop -> int -> int -> bool = function
  | `Eq -> ((=) : int -> int -> bool)
  | `Neq -> ((<>) : int -> int -> bool)
  | `Geq -> ((>=) : int -> int -> bool)
  | `Gt -> ((>) : int -> int -> bool)
  | `Leq -> ((<=) : int -> int -> bool)
  | `Lt -> ((<) : int -> int -> bool)

module Make (Context : S.CONTEXT) = struct
  type restriction = {
    kind : [ `Ensure | `Prevent ];
    expr : (Cudf_types.relop * Cudf_types.version) list; (* TODO: might not be a list *)
    (* NOTE: each list is a raw or the list is an OR case (see Cudf_types.vpkgforula) *)
  }

  type real_role = {
    context : Context.t;
    name : Cudf_types.pkgname;
  }

  type role =
    | Real of real_role               (* A role is usually an opam package name *)
    | Virtual of int * impl list      (* (int just for sorting) *)
  and real_impl = {
    pkg : Cudf.package;
    requires : dependency list;
  }
  and dependency = {
    drole : role;
    importance : [ `Essential | `Recommended | `Restricts ];
    restrictions : restriction list;
  }
  and impl =
    | RealImpl of real_impl                     (* An implementation is usually an opam package *)
    | VirtualImpl of int * dependency list      (* (int just for sorting) *)
    | Reject of (Cudf_types.pkgname * Cudf_types.version)
    | Dummy                                     (* Used for diagnostics *)

  let rec pp_version f = function
    | RealImpl impl -> Format.pp_print_int f impl.pkg.Cudf.version
    | Reject pkg -> Format.pp_print_int f (snd pkg)
    | VirtualImpl (_i, deps) ->
        Format.pp_print_string f
          (String.concat "&" (List.map (fun d -> Format.asprintf "%a" pp_role d.drole) deps))
    | Dummy -> Format.pp_print_string f "(no version)"
  and pp_impl f = function
    | RealImpl impl -> Format.fprintf f "%s.%d" impl.pkg.Cudf.package impl.pkg.Cudf.version
    | Reject pkg -> Format.fprintf f "%s.%d" (fst pkg) (snd pkg)
    | VirtualImpl _ as x -> pp_version f x
    | Dummy -> Format.pp_print_string f "(no solution found)"
  and pp_role f = function
    | Real t -> Format.pp_print_string f t.name
    | Virtual (_, impls) ->
        Format.pp_print_string f
          (String.concat "|" (List.map (Format.asprintf "%a" pp_impl) impls))

  let pp_impl_long = pp_impl

  module Role = struct
    type t = role

    let pp = pp_role

    let compare a b =
      match a, b with
      | Real a, Real b -> String.compare a.name b.name
      | Virtual (a, _), Virtual (b, _) -> Int.compare a b
      | Real _, Virtual _ -> -1
      | Virtual _, Real _ -> 1
  end

  let role context name = Real { context; name }

  let virtual_impl ~context ~depends () =
    let depends =
      List.map (fun (name, importance) ->
        let drole = role context name in
        let importance = (importance :> [ `Essential | `Recommended | `Restricts ]) in
        { drole; importance; restrictions = []}
      ) depends
    in
    VirtualImpl (Context.fresh_id context, depends)

  let virtual_role ~context impls =
    Virtual (Context.fresh_id context, impls)

  type command = |          (* We don't use 0install commands anywhere *)
  type command_name = private string
  let pp_command _ = function (_:command) -> .
  let command_requires _role = function (_:command) -> .
  let get_command _impl _command_name = None

  type dep_info = {
    dep_role : Role.t;
    dep_importance : [ `Essential | `Recommended | `Restricts ];
    dep_required_commands : command_name list;
  }

  type requirements = {
    role : Role.t;
    command : command_name option;
  }

  let dummy_impl = Dummy

  (* Turn an CUDF formula into a 0install list of dependencies. *)
  let list_deps ~context ~importance ~kind ~pname ~pver ~acc deps =
    let rec aux acc = function
      | [] -> acc
      | [[(name, _)]] when String.equal name pname -> acc
      | [[(name, c)]] ->
        let drole = role context name in
        let restrictions =
          match kind, c with
          | `Prevent, None -> [{ kind; expr = [] }]
          | `Ensure, None -> []
          | kind, Some c -> [{ kind; expr = [c] }]
        in
        { drole; restrictions; importance } :: acc
      | x::(_::_ as y) -> aux (aux acc y) [x]
      | [o] ->
        let impls = group_ors [] o in
        let drole = virtual_role ~context impls in
        (* Essential because we must apply a restriction, even if its
           components are only restrictions. *)
        { drole; restrictions = []; importance = `Essential } :: acc
    and group_ors acc = function
      | x::(_::_ as y) -> group_ors (group_ors acc y) [x]
      | [expr] -> VirtualImpl (Context.fresh_id context, aux [] [[expr]]) :: acc
      | [] -> Reject (pname, pver) :: acc
    in
    aux acc deps

  let requires _ = function
    | Dummy | Reject _ -> [], []
    | VirtualImpl (_, deps) -> deps, []
    | RealImpl impl -> impl.requires, []

  let dep_info { drole; importance; restrictions = _ } =
    { dep_role = drole; dep_importance = importance; dep_required_commands = [] }

  type role_information = {
    replacement : Role.t option;
    impls : impl list;
  }

  type machine_group = private string   (* We don't use machine groups because opam is source-only. *)
  let machine_group _impl = None

  type conflict_class = string

  let conflict_class _impl = []

  let prevent f =
    List.map (fun x -> [x]) f

  let ensure =
    Fun.id

  (* Get all the candidates for a role. *)
  let implementations = function
    | Virtual (_, impls) -> { impls; replacement = None }
    | Real role ->
      let context = role.context in
      let impls =
        List.filter_map (function
          | _, Error _rejection -> None
          | version, Ok pkg ->
              let requires =
                let make_deps importance kind xform deps acc =
                  list_deps ~context ~importance ~kind
                    ~pname:role.name ~pver:version
                    ~acc (xform deps)
                in
                make_deps `Essential `Ensure ensure pkg.Cudf.depends @@
                make_deps `Restricts `Prevent prevent pkg.Cudf.conflicts []
              in
              Some (RealImpl { pkg; requires })
          ) (Context.candidates context role.name)
      in
      { impls; replacement = None }

  let restrictions dependency = dependency.restrictions

  let meets_restriction impl { kind; expr } =
    match impl with
    | Dummy -> true
    | VirtualImpl _ -> assert false        (* Can't constrain version of a virtual impl! *)
    | Reject _ -> false
    | RealImpl impl ->
        let result = match expr with
          | [] -> true
          | _ -> List.exists (fun (c, v) -> fop c impl.pkg.Cudf.version v) expr
        in
        match kind with
        | `Ensure -> result
        | `Prevent -> not result

  type rejection = Context.rejection

  let rejects role =
    match role with
    | Virtual _ -> [], []
    | Real role ->
      let context = role.context in
      let rejects =
        List.filter_map (function
          | _, Ok _ -> None
          | version, Error reason ->
              let pkg = (role.name, version) in
              Some (Reject pkg, reason)
          ) (Context.candidates context role.name)
      in
      let notes = [] in
      rejects, notes

  let compare_version a b =
    match a, b with
    | RealImpl a, RealImpl b -> Int.compare a.pkg.Cudf.version b.pkg.Cudf.version
    | VirtualImpl (ia, _), VirtualImpl (ib, _) -> Int.compare ia ib
    | Reject (_, a), Reject (_, b) -> Int.compare a b
    | Dummy, Dummy -> 0
    | RealImpl _, (VirtualImpl _ | Reject _ | Dummy) -> -1
    | VirtualImpl _, RealImpl _ -> 1
    | VirtualImpl _, (Reject _ | Dummy) -> -1
    | Reject _, (RealImpl _ | VirtualImpl _) -> 1
    | Reject _, Dummy -> -1
    | Dummy, (RealImpl _ | VirtualImpl _ | Reject _) -> 1

  let user_restrictions = function
    | Virtual _ -> None
    | Real role ->
      match Context.user_restrictions role.context role.name with
      | [] -> None
      | f -> Some { kind = `Ensure; expr = f }

  let format_machine _impl = "(src)"

  let string_of_op = function
    | `Eq -> "="
    | `Geq -> ">="
    | `Gt -> ">"
    | `Leq -> "<="
    | `Lt -> "<"
    | `Neq -> "<>"

  let string_of_version_formula f = String.concat " & " (List.map (fun (rel, v) ->
      Printf.sprintf "%s %s" (string_of_op rel) (string_of_int v)
    ) f)

  let string_of_restriction = function
    | { kind = `Prevent; expr = [] } -> "conflict with all versions"
    | { kind = `Prevent; expr } -> Format.asprintf "not(%s)" (string_of_version_formula expr)
    | { kind = `Ensure; expr } -> string_of_version_formula expr

  let describe_problem _impl = Format.asprintf "%a" Context.pp_rejection

  let version = function
    | RealImpl impl -> Some (impl.pkg.Cudf.package, impl.pkg.Cudf.version)
    | Reject pkg -> Some pkg
    | VirtualImpl _ -> None
    | Dummy -> None
end
