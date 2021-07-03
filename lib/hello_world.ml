open! Base

module Term = struct
  type t =
    | Int_lit of int
    | Var of string
    | Lam of
        { name : string
        ; body : t
        }
    | App of
        { lhs : t
        ; rhs : t
        }
    | Rcd of { fields : (string * t) list }
    | Sel of
        { rcv : t
        ; field : string
        }
    | Let of
        { is_rec : bool
        ; name : string
        ; rhs : t
        ; body : t
        }
      [@@deriving sexp]
end

module Simple_type = struct
  type t =
    | Variable of state
    | Primitive of string
    | Function of
        { param : t
        ; body : t
        }
    | Record of { fields : (string * t) list }

  and state =
    { id : int
    ; mutable lower : t list
    ; mutable upper : t list
    }
  [@@deriving equal, compare, sexp]
end

module Ctx = struct
  type t = Simple_type.t Base.Map.M(String).t

  let add = Map.add_exn

  let empty = Map.empty (module String)

  let find_or_err t k ~msg =
    match Map.find t k with
    | Some x -> x
    | None -> failwith msg
  ;;
end

module Cache = struct
  module Pair = struct
    module T = struct
      type t = Simple_type.t * Simple_type.t
      [@@deriving equal, compare, sexp]
    end

    include T
    include Comparator.Make (T)
  end

  type t = Pair.t list ref

  let empty () = ref []
  let contains t a b = List.mem !t (a, b) ~equal:phys_equal
  let insert t a b = t := (a, b) :: !t
end

let fresh_state =
  let cur = ref 0 in
  fun () ->
    let id = !cur in
    cur := id + 1;
    { Simple_type.id; lower = []; upper = [] }
;;

let fresh () = Simple_type.Variable (fresh_state ())

let rec type_term (term : Term.t) ~(ctx : Ctx.t) : Simple_type.t =
  match term with
  | Int_lit _ -> Primitive "int"
  | Var name -> Ctx.find_or_err ctx name ~msg:("not found " ^ name)
  | Rcd { fields } ->
    let fields =
      List.map fields ~f:(fun (k, t) -> k, type_term t ~ctx)
    in
    Record { fields }
  | Lam { name; body } ->
    let param = fresh () in
    let ctx = Ctx.add ctx ~key:name ~data:param in
    Function { param; body = type_term body ~ctx }
  | App { lhs; rhs } ->
    let res = fresh () in
    constrain
      (type_term lhs ~ctx)
      (Simple_type.Function { param = type_term rhs ~ctx; body = res });
    res
  | Sel { rcv; field } ->
    let res = fresh () in
    constrain
      (type_term rcv ~ctx)
      (Record { fields = [ field, res ] });
    res
  | Let { is_rec; name; rhs; body } ->
    let res =
      if is_rec
      then (
        let e = fresh () in
        let ty = type_term rhs ~ctx:(Ctx.add ctx ~key:name ~data:e) in
        constrain ty e;
        e)
      else type_term rhs ~ctx
    in
    type_term body ~ctx:(Ctx.add ctx ~key:name ~data:res)

and constrain (a : Simple_type.t) (b : Simple_type.t) =
  let cache = Cache.empty () in
  let rec constrain a b =
    if Cache.contains cache a b
    then ()
    else (
      Cache.insert cache a b;
      match a, b with
      | Simple_type.Primitive n0, Simple_type.Primitive n1
        when String.equal n0 n1 -> ()
      | ( Function { param = param0; body = body0 }
        , Function { param = param1; body = body1 } ) ->
        constrain body1 body0;
        constrain param0 param1
      | Record { fields = fs0 }, Record { fields = fs1 } ->
        List.iter fs1 ~f:(fun (n1, t1) ->
            match
              List.find fs0 ~f:(fun (n0, _) -> String.equal n1 n0)
            with
            | None ->
              raise_s
                [%message
                  "missing field"
                    (n1 : string)
                    "in"
                    (fs0 : (string * Simple_type.t) list)]
            | Some (_, t0) -> constrain t0 t1)
      | Variable lhs, rhs ->
        lhs.upper <- rhs :: lhs.upper;
        List.iter lhs.lower ~f:(fun a -> constrain a rhs)
      | lhs, Variable rhs ->
        rhs.lower <- lhs :: rhs.lower;
        List.iter rhs.upper ~f:(fun b -> constrain lhs b)
      | lhs, rhs ->
        raise_s
          [%message
            "cannot constrain"
              (lhs : Simple_type.t)
              (rhs : Simple_type.t)])
  in
  constrain a b
;;

module Type = struct
  type t =
    | Top
    | Bot
    | Union of
        { lhs : t
        ; rhs : t
        }
    | Inter of
        { lhs : t
        ; rhs : t
        }
    | FunctionType of
        { param : t
        ; body : t
        }
    | RecordType of { fields : (string * t) list }
    | RecursiveType of
        { name : int
        ; body : t
        }
    | Type_variable of int
    | PrimitiveType of string
    [@@deriving sexp]

  type polar = Simple_type.state * bool

  let polar_equal (a_s, a_pol) (b_s, b_pol) =
    phys_equal a_s b_s && Bool.equal a_pol b_pol
  ;;

  let coalesce_type (ty : Simple_type.t) : t =
    let recursive = ref [] in
    let rec go ty ~polar ~in_process =
      match ty with
      | Simple_type.Primitive n -> PrimitiveType n
      | Function { param; body } ->
        let param = go param ~polar:(not polar) ~in_process in
        let body = go body ~polar ~in_process in
        FunctionType { param; body }
      | Record { fields } ->
        let fields =
          List.map fields ~f:(fun (name, ty) ->
              name, go ty ~polar ~in_process)
        in
        RecordType { fields }
      | Variable vs ->
        let vs_pol = vs, polar in
        if List.mem in_process vs_pol ~equal:polar_equal
        then (
          match
            List.Assoc.find !recursive vs_pol ~equal:polar_equal
          with
          | None ->
            let var = fresh_state () in
            recursive := (vs_pol, var.id) :: !recursive;
            Type_variable var.id
          | Some v -> Type_variable v)
        else (
          let bounds = if polar then vs.lower else vs.upper in
          let bound_types =
            List.map bounds ~f:(fun ty ->
                go ty ~polar ~in_process:(vs_pol :: in_process))
          in
          let mrg =
            if polar
            then fun lhs rhs -> Union { lhs; rhs }
            else fun lhs rhs -> Inter { lhs; rhs }
          in
          let res =
            List.fold_left
              bound_types
              ~init:(Type_variable vs.id)
              ~f:mrg
          in
          match
            List.Assoc.find !recursive vs_pol ~equal:polar_equal
          with
          | None -> res
          | Some a -> RecursiveType { name = a; body = res })
    in
    go ty ~polar:true ~in_process:[]
  ;;
end

let print_hello_world () = Stdio.print_endline "hello world"
