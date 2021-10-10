(* TODO document *)

exception Cannot_get_value

open Misc
module Mono = Smol.Monomial.Make (Literal.Class)
module Mono_Uid = Smol.Monomial.Make (Z)
module Poly_Uid = Smol.Polynomial.Make (Z)
module Vect_Class = Smol.Vector.Make (Literal.Class)
module Mat_Class = Smol.Matrix.Make (Literal.Class)
module LUidMap = Map.Make (Z)

type 'a pp = 'a Poly_Class.p Poly_Uid.p

type 'a op =
  | Seq (* 1 / 1-x *) of 'a Poly_Uid.p
  | Seq_at_most of (* deriv degree, max size, poly *) int * int * 'a Poly_Uid.p
  | Id (* lazy *) of 'a Poly_Uid.p
  | Set (* exp *) of 'a Poly_Uid.p
  | Cycle (* log (1/1-x) *) of 'a Poly_Uid.p

type 'a s = 'a pp * 'a Poly_Class.p op LUidMap.t

(** Unique ids for the companion map *)
module Uid = struct
  let cpt = ref Z.zero

  let create () : Z.t =
    cpt := Z.succ !cpt ;
    !cpt
end

(* Invariant for species:
   uids can only reference older uids. The dag is included in the total order on their ids
   Proof by induction
*)
let get_dag (l : 'a LUidMap.t) : (Z.t * 'a) list =
  LUidMap.bindings l |> List.sort (fun (a, _) (b, _) -> Z.compare a b)

module Make_R (K : Scalar.Ring_ext) = struct
  module P = Poly_Class.Make_Ring (K)
  module PP = Poly_Uid.Make_Ring (P)

  let deriv_pk v p =
    let p_r = P.deriv v p in
    P.map (fun (i, k) -> K.mul_int i k) p_r

  let deriv_ppk v p =
    let p_r = PP.deriv v p in
    PP.map (fun (i, k) -> P.mul_scalar (K.mul_int i K.one) k) p_r

  (* to only be used when the result is not a species, like equal,
     or in freshen_up. Otherwise use map_fresh *)
  let map_ f (a, l) =
    let aux = function
      | Seq s -> Seq (f s)
      | Seq_at_most (d, n, s) -> Seq_at_most (d, n, f s)
      | Id s -> Id (f s)
      | Set s -> Set (f s)
      | Cycle s -> Cycle (f s)
    in
    (f a, LUidMap.map aux l)

  type t = K.t s

  let zero : t = (PP.zero, LUidMap.empty)

  let equal_op_raw op1 op2 =
    match (op1, op2) with
    | (Seq p1, Seq p2) -> PP.equal p1 p2
    | (Seq_at_most (d1, n1, p1), Seq_at_most (d2, n2, p2)) ->
        Int.equal d1 d2 && Int.equal n1 n2 && PP.equal p1 p2
    | (Id p1, Id p2) -> PP.equal p1 p2
    | (Set p1, Set p2) -> PP.equal p1 p2
    | (Cycle p1, Cycle p2) -> PP.equal p1 p2
    | _ -> false

  let is_zero ((a, l) : t) =
    let dag = get_dag l in
    let update_maps v op lsimp leq =
      LUidMap.filter (fun _ val_done -> equal_op_raw op val_done) leq
      |> LUidMap.choose_opt
      |> function
      | None -> (lsimp, LUidMap.add v op leq)
      | Some (u, _) -> (LUidMap.add v (PP.of_literal u) lsimp, leq)
    in
    let rec aux lsimp leq = function
      | [] -> lsimp
      | (v, op) :: t -> (
          match op with
          | Seq x ->
              let x = PP.substitution lsimp x in
              if PP.is_zero x then aux (LUidMap.add v PP.one lsimp) leq t
              else
                let (lsimp, leq) = update_maps v (Seq x) lsimp leq in
                aux lsimp leq t
          | Set x ->
              let x = PP.substitution lsimp x in
              if PP.is_zero x then aux (LUidMap.add v PP.one lsimp) leq t
              else
                let (lsimp, leq) = update_maps v (Set x) lsimp leq in
                aux lsimp leq t
          | Seq_at_most (d, n, x) ->
              let x = PP.substitution lsimp x in
              if d > n || PP.is_zero x then
                aux (LUidMap.add v PP.zero lsimp) leq t
              else
                let (lsimp, leq) =
                  update_maps v (Seq_at_most (d, n, x)) lsimp leq
                in
                aux lsimp leq t
          | Id x ->
              let x = PP.substitution lsimp x in
              if PP.is_zero x then aux (LUidMap.add v PP.zero lsimp) leq t
              else
                let (lsimp, leq) = update_maps v (Id x) lsimp leq in
                aux lsimp leq t
          | Cycle x ->
              let x = PP.substitution lsimp x in
              if PP.is_zero x then aux (LUidMap.add v PP.zero lsimp) leq t
              else
                let (lsimp, leq) = update_maps v (Cycle x) lsimp leq in
                aux lsimp leq t)
    in
    let lsimp = aux LUidMap.empty LUidMap.empty dag in
    PP.is_zero (PP.substitution lsimp a)

  let one : t = (PP.one, LUidMap.empty)

  (* Rename literals in the companion map to have fresh names. This avoids loops and ensures
     that uids only refer to newer ones, even after substitution *)
  let freshen_up (a, l) : t =
    let dag = get_dag l |> List.map fst in
    let freshed =
      (* Keep same order of creation *)
      List.fold_left
        (fun acc x -> LUidMap.add x (Uid.create ()) acc)
        LUidMap.empty
        dag
    in
    let subbed = LUidMap.map PP.of_literal freshed in
    let (a, l) = map_ (PP.substitution subbed) (a, l) in
    let l =
      LUidMap.fold
        (fun li s acc -> LUidMap.add (LUidMap.find li freshed) s acc)
        l
        LUidMap.empty
    in
    (a, l)

  let map_fresh f s = map_ f s |> freshen_up

  let map (f : 'a -> K.t) : 'a s -> t =
    let g = PP.map (P.map f) in
    map_fresh g

  let add ((sa, la) : t) ((sb, lb) : t) : t =
    (PP.add sa sb, LUidMap.union (fun _ a _ -> Some a) la lb)

  let neg ((s, l) : t) = (PP.neg s, l)

  let sub a b = add a (neg b)

  let equal a b = is_zero (sub a b)

  let mul ((sa, la) : t) ((sb, lb) : t) : t =
    (PP.mul sa sb, LUidMap.union (fun _ a _ -> Some a) la lb)

  let mul_scalar k (a, l) : t = (PP.map (P.mul_scalar k) a, l)

  let seq (a, l) =
    let new_name = Uid.create () in
    (PP.of_literal new_name, LUidMap.add new_name (Seq a) l)

  let set (a, l) =
    let new_name = Uid.create () in
    (PP.of_literal new_name, LUidMap.add new_name (Set a) l)

  let cycle (a, l) =
    let new_name = Uid.create () in
    (PP.of_literal new_name, LUidMap.add new_name (Cycle a) l)

  let pow c n =
    let m = Mono_Uid.singleton c n in
    PP.of_monomial m

  let seq_at_least_n n (a, l) =
    if n <= 0 then seq (a, l)
    else
      let new_name = Uid.create () in
      let ida = Uid.create () in
      ( PP.mul (pow ida n) (PP.of_literal new_name),
        LUidMap.add new_name (Seq a) l |> LUidMap.add ida (Id a) )

  let seq_at_most_n n (a, l) =
    if n < 0 then zero
    else if n = 0 then one
    else
      let new_name = Uid.create () in
      (PP.of_literal new_name, LUidMap.add new_name (Seq_at_most (0, n, a)) l)

  let tuple_n n (a, l) =
    if n < 0 then zero
    else if n = 0 then one
    else if n = 1 then (a, l)
    else
      let ida = Uid.create () in
      (pow ida n, LUidMap.add ida (Id a) l)

  let seq_bounded ~min ~max (a, l) =
    if max < 0 || min > max then zero
    else if min <= 0 then seq_at_most_n max (a, l)
    else if min = max then tuple_n min (a, l)
    else
      let new_name = Uid.create () in
      let ida = Uid.create () in
      let pp = PP.mul (pow ida min) (PP.of_literal new_name) in
      ( pp,
        LUidMap.add new_name (Seq_at_most (0, max - min, a)) l
        |> LUidMap.add ida (Id a) )

  let of_scalar k = (PP.of_scalar (P.of_scalar k), LUidMap.empty)

  let of_class c = (PP.of_scalar (P.of_literal c), LUidMap.empty)

  let eval lcm s = map_fresh (PP.map (P.eval lcm)) s

  module PPP = Poly_Uid.Make_Ring (PP)

  let subst_aux (polmaps : PP.t LClassMap.t) (pp : PP.t) : PP.t =
    PPP.map
      (fun p ->
        P.fold
          (fun m k acc ->
            Mono.apply (module PP) m polmaps |> fun (ap, mr) ->
            PP.add acc (PP.mul_scalar (P.mul_scalar k (P.of_monomial mr)) ap))
          p
          PP.zero)
      pp
    |> PP.flatten

  let substitution lcm s =
    let polmaps = LClassMap.map fst lcm in
    let (a, l) = map_fresh (subst_aux polmaps) s in
    let l =
      LClassMap.fold
        (fun _ (_, lv) acc -> LUidMap.union (fun _ a _ -> Some a) lv acc)
        lcm
        l
    in
    (a, l)

  let op_deriv_rule name op =
    match op with
    (* Seq'(f) = f' * Seq(f) * Seq(f) *)
    | Seq x ->
        let s = PP.of_literal name in
        (PP.mul s s, x, LUidMap.empty)
    (* Increase d *)
    | Seq_at_most (d, n, x) ->
        if d >= n then (PP.zero, x, LUidMap.empty)
        else
          let new_s = Uid.create () in
          let pp = PP.of_literal new_s in
          let new_op = Seq_at_most (d + 1, n, x) in
          (pp, x, LUidMap.singleton new_s new_op)
    | Id x -> (PP.one, x, LUidMap.empty)
    (* exp' = exp *)
    | Set x -> (PP.of_literal name, x, LUidMap.empty)
    (* [log(1/1-f)]' = f'/(1-f) *)
    | Cycle x ->
        let new_s = Uid.create () in
        let pp = PP.of_literal new_s in
        (pp, x, LUidMap.singleton new_s (Seq x))

  let deriv (deriv_coeff : K.t -> K.t) (deriv_class : Literal.Class.t -> P.t)
      ((a, l) : t) : t =
    let deriv_p p =
      let lc = P.get_support p in
      let rec aux acc = function
        | [] -> acc
        | v :: t -> aux (P.add (P.mul (deriv_pk v p) (deriv_class v)) acc) t
      in
      aux (P.map deriv_coeff p) lc
    in

    let rec deriv_pp pp mem lnew =
      let lu = PP.get_support pp in
      let deriv_op s mem lnew =
        match LUidMap.find_opt s mem with
        | Some d -> (d, mem, lnew)
        | None ->
            let op = LUidMap.find s l in
            let (pp_chain_rule, to_deriv, new_symbols) = op_deriv_rule s op in
            let (op_derivd, lnew) = deriv_pp to_deriv mem lnew in
            let res = PP.mul pp_chain_rule op_derivd in
            let lnew = LUidMap.union (fun _ a _ -> Some a) lnew new_symbols in
            let mem = LUidMap.add s res mem in
            (res, mem, lnew)
      in
      let rec aux mem acc lnew = function
        | [] -> (acc, lnew)
        | v :: t ->
            let (v_derivd, mem, lnew) = deriv_op v mem lnew in
            let vderiv_res = PP.mul v_derivd (deriv_ppk v pp) in
            aux mem (PP.add vderiv_res acc) lnew t
      in
      aux mem (PP.map deriv_p pp) lnew lu
    in
    let (a, lnew) = deriv_pp a LUidMap.empty LUidMap.empty in
    (a, LUidMap.union (fun _ a _ -> Some a) l lnew)

  let deriv_class c s =
    deriv
      (fun _ -> K.zero)
      (fun x -> if Literal.Class.equal c x then P.one else P.zero)
      s

  module S_tmp : Smol.Algebra.Ring_S with type t = t = struct
    type t = K.t s

    let one = one

    let mul = mul

    let equal = equal

    let to_string _ = ""

    let zero = zero

    let add = add

    let neg = neg

    let sub = sub
  end

  let make_jacobian (v : t Vect_Class.v) : t Mat_Class.m =
    let module M = Mat_Class.Make_R (S_tmp) in
    let supp = Vect_Class.get_support v in
    let mat_supp =
      List.map (fun x -> List.map (fun y -> (x, y)) supp) supp |> List.flatten
    in
    List.fold_left
      (fun acc (x, y) ->
        let em = Vect_Class.get_entry x v |> Option.get |> deriv_class y in
        M.set_entry x y em acc)
      (M.zero supp)
      mat_supp

  (* I'm going to do what is called a pro gamer move *)
  (* Semiring for deg values, similar to a tropical semiring *)
  (* None : not polynomial *)
  (* Some x: polynomial of degree x. x < 0 iff polynomial is zero *)
  module Deg_semiring = struct
    type t = int option

    let equal x y =
      match (x, y) with
      | (Some x, Some y) -> if x < 0 then y < 0 else x = y
      | (None, None) -> true
      | _ -> false

    (* neutral for addition. Note that all negative degrees are equivalent *)
    let zero = Some (-1)

    (* neutral for multiplication *)
    let one = Some 0

    (* the degree of the sum of two polynomials is the max between them *)
    (* None does not have an inverse for the addition, we have a semiring *)
    let add x y =
      match (x, y) with (Some x, Some y) -> Some (max x y) | _ -> None

    (* the degree of the product of two polynomials is their sum *)
    (* zero is absorbant *)
    let mul x y =
      match (x, y) with
      | (Some x, Some y) -> if x < 0 || y < 0 then Some (-1) else Some (x + y)
      | (Some x, None) | (None, Some x) -> if x < 0 then Some x else None
      | _ -> None

    (* Useless *)
    let to_string = function
      | Some x -> "Some " ^ Int.to_string x
      | None -> "None"
  end

  (* oh boy here we go *)
  module P_deg = Poly_Uid.Make_Semiring (Deg_semiring)

  let deg_op_aux (f : P_deg.t -> int option) = function
    | Id x -> f x
    | Seq x | Set x -> (
        match f x with Some d when d <= 0 -> Some 0 | _ -> None)
    | Cycle x -> ( match f x with Some d when d <= 0 -> Some d | _ -> None)
    | Seq_at_most (d, n, x) -> (
        match f x with
        | None -> None
        | Some dx ->
            if dx < 0 then Some (-1)
            else (* if d > n it's still ok *) Some (dx * (n - d)))

  (* will be reused for deg_z later *)
  let deg_generic (f : P.t -> int option) (a, l) =
    let (a, l) = map_ (P_deg.map f) (a, l) in
    let dag = get_dag l in
    let rec aux map_acc = function
      | [] -> map_acc
      | (v, op) :: t ->
          (* that P_deg.eval is doing a lot of the work *)
          (* We can safely convert to scalar since we follow dag order *)
          let evald =
            deg_op_aux (fun x -> P_deg.eval map_acc x |> P_deg.to_scalar) op
          in
          aux (LUidMap.add v evald map_acc) t
    in
    P_deg.eval (aux LUidMap.empty dag) a |> P_deg.to_scalar

  (* it's as easy as that *)
  let deg_class c s = deg_generic (fun p -> Some (P.deg c p)) s

  let is_polynomial_wrt_class c s = Option.is_some (deg_class c s)

  (* TODO improve, it's quite scuffed atm *)
  let op_to_string lm = function
    | Seq x -> "Seq(" ^ (PP.eval lm x |> PP.to_string) ^ ")"
    | Seq_at_most (d, n, x) ->
        "Seq_at_most[" ^ Int.to_string n ^ "," ^ Int.to_string d ^ "]("
        ^ (PP.eval lm x |> PP.to_string)
        ^ ")"
    | Id x -> PP.eval lm x |> PP.to_string
    | Set x -> "Set(" ^ (PP.eval lm x |> PP.to_string) ^ ")"
    | Cycle x -> "Cycle(" ^ (PP.eval lm x |> PP.to_string) ^ ")"

  let to_string (a, l) =
    let dag = get_dag l in
    let rec aux val_acc = function
      | [] -> PP.eval val_acc a |> PP.to_scalar |> P.to_string
      | (v, op) :: t ->
          let g =
            op_to_string val_acc op |> Literal.Class.of_string |> P.of_literal
          in
          aux (LUidMap.add v g val_acc) t
    in
    aux LUidMap.empty dag
end

module Make_Sc (K : Scalar.S) = struct
  include Make_R (K)

  let factd d n =
    let rec aux k acc =
      if k <= 0 then acc else aux (k - 1) ((n - k + 1) * acc)
    in
    aux d 1

  let rec polyseq d n x xacc nmax acc =
    if n > nmax - d then acc
    else
      polyseq
        d
        (n + 1)
        x
        (K.mul x xacc)
        nmax
        (K.add acc (K.mul_int (factd d n) xacc))

  let eval_pp_f x lm f =
    PP.eval lm x |> PP.to_scalar_opt
    |> Option.map (fun x -> P.to_scalar_opt x)
    |> Option.join
    |> Option.map (fun x -> P.of_scalar (f x))

  let eval_op lm = function
    | Seq x -> eval_pp_f x lm (fun x -> K.(inv (sub one x)))
    | Seq_at_most (d, n, x) ->
        if d > n then Some P.zero
        else eval_pp_f x lm (fun x -> polyseq d 0 x K.one n K.zero)
    | Id x -> eval_pp_f x lm (fun x -> x)
    | Set x -> eval_pp_f x lm K.exp
    | Cycle x -> eval_pp_f x lm (fun x -> K.(log (inv (sub one x))))

  let get_value_aux (s, l) =
    let dag = get_dag l in
    let rec aux val_acc = function
      | [] -> PP.eval val_acc s
      | (v, op) :: t -> (
          match eval_op val_acc op with
          | None -> s
          | Some p -> aux (LUidMap.add v p val_acc) t)
    in
    aux LUidMap.empty dag

  let get_value_opt (s : t) =
    PP.to_scalar_opt (get_value_aux s)
    |> Option.map (fun x -> P.to_scalar_opt x)
    |> Option.join

  (** @raise [Cannot_get_value] if a value cannot be inferred *)
  let get_value s =
    try PP.to_scalar (get_value_aux s) |> P.to_scalar
    with Smol.Polynomial.Polynomial_is_not_scalar -> raise Cannot_get_value
end

module Make (K : Scalar.S) = struct
  module LVarMap = Map.Make (Literal.Variable)

  module P_z = struct
    include Poly_Var.Make_Ring (K)

    let mul_int i = map (K.mul_int i)
  end

  module PP_z = Poly_Class.Make_Ring (P_z)
  module S_applied = Make_Sc (K)

  module S_base = struct
    include Make_R (P_z)

    (* Idea: We could extend these definitions to any variables *)
    let eval_z z s =
      S_applied.map
        (fun p ->
          P_z.eval (LVarMap.singleton Literal.Variable.z z) p |> P_z.apply_at_0)
        s

    let eval_z_partial z s =
      map (fun p -> P_z.eval (LVarMap.singleton Literal.Variable.z z) p) s

    let deriv_z =
      deriv
        (fun p ->
          P_z.deriv Literal.Variable.z p
          |> P_z.map (fun (i, k) -> K.mul_int i k))
        (fun c -> PP_z.of_literal (Literal.Class.deriv c))

    module P_class_deg = Poly_Class.Make_Semiring (Deg_semiring)

    let deg_z s =
      let aux pz =
        P_class_deg.map (fun p -> Some (P_z.deg Literal.Variable.z p)) pz
        |> P_class_deg.eval
             (* a class variable is a polynomial of degree 0 in z *)
             (List.map (fun x -> (x, Some 0)) (PP_z.get_support pz)
             |> List.to_seq |> LClassMap.of_seq)
        |> P_class_deg.to_scalar
      in
      deg_generic aux s

    let is_polynomial_wrt_z s = Option.is_some (deg_z s)
  end
end
