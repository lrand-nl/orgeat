(* TODO refaire la doc *)

open Misc
module Vector = Smol.Vector.Make (Literal.Class)
module Matrix = Smol.Matrix.Make (Literal.Class)

(** This module takes care of approximating the partition function of a combinatorial class
    given a system of equations for which it is a solution.
    
    This module is based on the paper from Carine Pivoteau, Bruno Salvy and Michèle Soria, 
    "Algorithms for combinatorial structures: Well-founded systems and Newton iterations", published
    in the Journal of Combinatorial Theory, Series A 119 (2012) (pp. 1711-1773).
    Any mention to a definition, proposition, etc. in the comments of this module are refering
    to the corresponding part of that paper.
    
    The following functions are implementations of algorithms from the paper:
    - [zero_coord] implements "0-coord"
    - [is_well_founded_at_zero] implements "isWellFoundedAt0"
    - [is_polynomial] implements "isPolynomial"
    - [is_partially_polynomial] implements "isPartiallyPolynomial"
    - [is_well_founded] implements "isWellFounded"
 
 *)

module Make (K : Scalar.S) = struct
  module P_z = Poly_Var.Make_Ring (K)
  module P = Poly_Class.Make_Ring (K)
  module PP = Poly_Class.Make_Ring (P_z)
  module S = Species.Make (K)
  module S_z = S.S_base
  module S_a = S.S_applied
  module Combi = Combi.Make (K)
  module M_z = Matrix.Make_R (S_z)
  module M_a = Matrix.Make_R (S_a)
  module V_z = Vector.Make_R (S_z)
  module V_a = Vector.Make_R (S_a)
  module V_k = Vector.Make_R (K)

  (** [class_tree] without type. Used to compute the generating function(s).
     [Map] is absent because it only impacts the type of the generated object,
     not the computation of its generating function, so it is not used here
   *)
  type hollow_tree =
    (* Leaves *)
    | One
    | Z
    | Scalar of K.t
    | Empty
    (* Provide a key to access classes in a Map. *)
    | Class of Literal.Class.t
    (* Union type, sum of disjoint classes. *)
    | Union of hollow_tree list
    (* Product type. *)
    | Product of hollow_tree * hollow_tree
    (* Sequence constructor, for lists (not sets) *)
    | Sequence of Combi.sequence_kind * hollow_tree

  type hollow_system = hollow_tree LClassMap.t

  type species_system = S_z.t LClassMap.t

  type solution_kind =
    | Poly of species_system
    | Seq of K.t
    | Tree of (K.t * K.t LClassMap.t)

  (** [hollow key c init_h] returns an updated map of [init_h] containing all classes on which [c] depends 
    Assumes [key] is unique and only maps to [c]
    Does a depth-first search in the dependency graph of the classes involved in the definition of [c]. 
 *)
  let rec hollow :
      type a.
      Literal.Class.t -> a Combi.class_tree -> hollow_system -> hollow_system =
   fun key c init_h ->
    if LClassMap.mem key init_h then init_h
    else
      (* Binds [key] to a placeholder, to avoid infinite loops *)
      let h_tmp = LClassMap.add key Empty init_h in
      let rec aux :
          type a.
          hollow_system -> a Combi.class_tree -> hollow_system * hollow_tree =
       fun h -> function
        | Combi.One -> (h, One)
        | Combi.Z -> (h, Z)
        | Combi.Scalar x -> (h, Scalar x)
        | Combi.Empty -> (h, Empty)
        (* Unknown samplers are of size one *)
        | Combi.Sampler _ -> (h, One)
        | Combi.Class r ->
            let other_key = Combi.get_name r in
            let other_c = Combi.get_class r in
            let other_c = Option.value other_c ~default:Combi.Empty in
            let h = hollow other_key other_c h in
            (h, Class other_key)
        (* | Combi.Self ->
           (h, Class key)*)
        | Combi.Union cl ->
            let (h, hol_list) =
              List.fold_left
                (fun (h_fold, hol_list_fold) c_cur ->
                  let (h_fold, hol_fold) = aux h_fold c_cur in
                  (h_fold, hol_fold :: hol_list_fold))
                (h, [])
                cl
            in
            (h, Union hol_list)
        | Combi.Product (l, r) ->
            let (h, hl) = aux h l in
            let (h, hr) = aux h r in
            (h, Product (hl, hr))
        | Combi.Sequence (skind, cs) ->
            let (h, hs) = aux h cs in
            (h, Sequence (skind, hs))
        | Combi.Map (x, _) -> aux h x
      in
      let (h, hollowed_c) = aux h_tmp c in
      LClassMap.add key hollowed_c h

  (*
  (** Same as [hollow], but for a whole list. Initial system is usually empty. *)
  let rec hollow_list :
      type a. a Combi.class_list -> hollow_system -> hollow_system =
   fun cl h ->
    match cl with
    | Combi.Single r ->
        let (key, c, _) = !r in
        let c = Option.value c ~default:Combi.Self in
        hollow key c h
    | Combi.Cons (r, t) ->
        let (key, c, _) = !r in
        let c = Option.value c ~default:Combi.Self in
        let h = hollow key c h in
        hollow_list t h
   *)

  (** Transforms a equation on species into a rationnal fraction for the given class.
    Also returns the known samplers used in the definition of the class. 
 *)
  let apply_single : hollow_tree -> S_z.t =
   fun tree ->
    (* TODO tail rec (?) *)
    let rec aux = function
      | One -> S_z.one
      | Z ->
          (* We can imagine having any kind of stat variable here *)
          S_z.of_scalar (P_z.of_literal Literal.Variable.z)
      | Empty -> S_z.zero
      | Scalar x -> S_z.of_scalar (P_z.of_scalar x)
      | Class key -> S_z.of_class key
      | Union tree_list ->
          List.fold_left S_z.add S_z.zero (List.rev_map aux tree_list)
      | Product (t1, t2) -> S_z.mul (aux t1) (aux t2)
      | Sequence ({min; max}, t) -> (
          match max with
          | None -> S_z.seq_at_least_n min (aux t)
          | Some max -> S_z.seq_bounded ~min ~max (aux t))
    in
    aux tree

  (** Transforms a system of equations on species into a list of rationnal fractions.
    Also gives a mapping of known samplers.
 *)
  let h_of_system : hollow_system -> species_system =
   fun hs -> LClassMap.map apply_single hs

  (** Translate a [class_tree] into a system of equations
    Composition of [h_of_system] and [hollow]
 *)
  let translate :
      type a. Literal.Class.t -> a Combi.class_tree -> species_system =
   fun key c -> h_of_system (hollow key c LClassMap.empty)

  let translate_class : type a. a Combi.combi_class -> species_system =
   fun cc ->
    let name = Combi.get_name cc in
    let t = Combi.get_class cc |> Option.value ~default:Combi.Empty in
    translate name t

  let include_deriv s =
    LClassMap.fold
      (fun name v -> LClassMap.add (Literal.Class.deriv name) (S_z.deriv_z v))
      s
      s

  (** Algorithm 0-coord
    Detection of zero coordinates in the solution of a system
    See Lemma 3.4

    @param s the mapping of known samplers appearing in the system
    @param h a vector of species such that h(0,0) = 0, and its Jacobian matrix is nilpotent
    @return the list of 0-coordinates in the solution of the system Y = h(Z,Y)
 *)
  let zero_coord (h : species_system) : Literal.Class.t list =
    let m = Vector.of_map h |> Vector.cardinal in
    let u = LClassMap.map (fun _ -> S_z.zero) h in
    let rec iter f k =
      if k <= 0 then f
      else
        let tmp = LClassMap.map (S_z.substitution f) h in
        iter
          (LClassMap.map
             (fun x ->
               if S_z.is_zero x then S_z.zero
               else S_z.of_scalar (P_z.of_literal Literal.Variable.z))
             tmp)
          (k - 1)
    in
    iter u m
    (* Return the zero entries *)
    |> LClassMap.filter (fun _ a -> S_z.is_zero a)
    |> Vector.of_map |> Vector.get_support

  (** Algorithm isWellFoundedAt0
    Characterization of well-founded systems at 0
    See Definition 3.5 and Theorem 3.6
    
    @param s the mapping of known samplers appearing in the system
    @param h a vector of species such that h(0,0) = 0
    @param j the Jacobian of h
    @return - [Some []] if the system Y = h(Z,Y) is well-founded at 0,
            - [Some l] if the solution to the system Y = h(Z,Y) has zero coordinates, 
            which are then listed in l,
            - [None] if the Jacobian matrix is not nilpotent
 *)
  let is_well_founded_at_0 (h : species_system) (j : M_z.t) :
      Literal.Class.t list option =
    let j0 = M_a.map (S_a.map P_z.apply_at_0) j in
    if M_a.is_nilpotent j0 then Some (zero_coord h) else None

  (** Algorithm isPolynomial
    Detection of implicit polynomial species
    See Proposition 4.2


    @param s the mapping of known samplers appearing in the system
    @param h a vector of species such that h(0,0) = 0 and its Jacobian matrix is nilpotent
    @return [Some s] if the solution of Y = h(Z,Y) is polynomial and is [s], [None] otherwise.
            Ensures that [s] is a vector of polynomials in z with no sampler variable appearing.
 *)
  let is_polynomial (h : species_system) : species_system option =
    let m = Vector.of_map h |> Vector.cardinal in
    let u = LClassMap.map (fun _ -> S_z.zero) h in
    let aux_sub h u = LClassMap.map (S_z.substitution u) h in
    let rec iter u k = if k <= 0 then u else iter (aux_sub h u) (k - 1) in
    let u = iter u m in
    let v = aux_sub h u in
    if
      V_z.equal (Vector.of_map u) (Vector.of_map v)
      && LClassMap.for_all (fun _ -> S_z.is_polynomial_wrt_z) u
    then Some u
    else None

  (** Algorithm isPartiallyPolynomial
    Characterization of implicit partially polynomial species
    See proposition 4.5. In the algorithm, Z{_ 1 } will be the variable ["z1"], and
    Z{_ 2 } will be the variable ["z"].
    
    @param s the mapping of known samplers appearing in the system
    @param h a vector of species such that Y = H(Z{_ 1 },Z{_ 2 },Y) is well founded at 0
    @return true iff the solution of Y = H(Z{_ 1 },Z{_ 2 },Y) is polynomial in Z{_ 1 }.
 *)
  let is_partially_polynomial (z1 : Literal.Variable.t) (h : species_system) :
      bool =
    (* We should first check that h is polynomial wrt z1, however by construction in our case,
       it is always true, so this step can be safely skipped. *)
    (* assert (Literal.Map.for_all (fun _ x -> RF.is_polynomial_wrt_var x "x1") h); *)
    let h_z0 =
      LClassMap.map
        (fun s ->
          (* h[z = 0] *)
          S_z.eval_z_partial K.zero s
          (* h[z1 <- z] because is_poly only checks polynomiality wrt the main variable z *)
          |> S_z.map
               (P_z.substitution
                  (LVarMap.singleton z1 (P_z.of_literal Literal.Variable.z))))
        h
    in
    match is_polynomial h_z0 with
    | None -> false
    | Some s0 ->
        (* We also skip computing the Jacobian, since in our use case it is the same as the
           original system's Jacobian, so it must be nilpotent at this stage. See the comments
           after Proposition 4.5, p.1728, for more details on the two skipped steps. *)
        LClassMap.for_all
          (fun lit s ->
            (* Either the polynomial is zero *)
            S_z.is_zero s
            (* Or it is not, and h must be polynomial wrt this entry *)
            || LClassMap.for_all
                 (fun _ sh -> S_z.is_polynomial_wrt_class lit sh)
                 h)
          s0

  (** Algorithm isWellFounded
    Characterization of well-founded systems
    See Definition 5.3 and Theorem 5.5. This condition is sufficient to use Newton's
    iteration to evaluate the generating function of the combinatorial system.

    @param s the mapping of known samplers appearing in the system
    @param h a vector of species
    @param j the Jacobian of h. Note that it is also the Jacobian of the companion
           system [k], so it does not need to be computed multiple times.
    @return true iff the system Y = H(Z,Y) is well founded
*)
  let is_well_founded (h : species_system) (j : M_z.t) : bool =
    let zero = LClassMap.map (fun _ -> K.zero) h in
    let h_0 =
      LClassMap.map
        (fun s -> S_z.eval_z K.zero s |> S_a.eval zero |> S_z.map P_z.of_scalar)
        h
      |> Vector.of_map
    in
    let h = Vector.of_map h in
    let z1 = Literal.Variable.of_string "z1" in
    let sz1 = S_z.of_scalar (P_z.of_literal z1) in
    let k = V_z.Infix.(h - h_0 + (sz1 *. h_0)) |> Vector.to_map in
    match is_well_founded_at_0 k j with
    | Some [] -> is_partially_polynomial z1 k
    | _ -> false

  (** Newton iteration
   
    @param s the mapping of known samplers appearing in the system
    @param h a vector of species such that Y = h(Z,Y) is well founded
    @param j the Jacobian of h
    @param epsilon the precision of the evaluation
    @param z the point of evaluation
    @return some value approximating the solution at [z] with precision (at least) [epsilon], 
            or None if the iteration does not converges with the given parameters.
 *)
  let newton_iteration (h : species_system) (j : M_z.t) :
      K.t -> K.t -> K.t LClassMap.t option =
    (* assert (is_well_founded h j); *)
    let support = Vector.(get_support (of_map h)) in
    let size = List.length support in
    let module V = struct
      include Vector.Make_R (K)

      let zero = zero support
    end in
    let module M = struct
      include Matrix.Make_R (K)

      let one = one support
    end in
    let iter (h : V_a.t) (j : M_a.t) (u : M.t) (y : V.t) : M.t * V.t =
      let jy =
        M.map (fun x -> S_a.eval (Vector.to_map y) x |> S_a.get_value) j
      in
      let hy =
        Vector.map (fun x -> S_a.eval (Vector.to_map y) x |> S_a.get_value) h
      in
      let u = M.(Infix.(u + (u * ((jy * u) - u + one)))) in
      let y = V.(Infix.(y + M.mul_vect u (hy - y))) in
      (u, y)
    in
    let h = Vector.of_map h in
    fun (e : K.t) (z : K.t) ->
      let h_z = Vector.map (S_z.eval_z z) h in
      let j_z = M_a.map (S_z.eval_z z) j in
      let y = V.zero in
      let u = M.one in
      let iter_a = iter h_z j_z in
      let rec aux step_n delta u y =
        let (u, n_y) = iter_a u y in
        (* let n_val = Vector.fold (fun _ x acc -> K.(add x acc)) n_y K.zero in *)
        let n_delta =
          Vector.union
            (fun _ a b -> Some (K.abs (K.sub a b)))
            (Vector.filter (fun k _ -> Literal.Class.is_base k) y)
            (Vector.filter (fun k _ -> Literal.Class.is_base k) n_y)
          |> fun x -> V.mul_dot x (Vector.map (fun _ -> K.one) x)
        in
        (* Minimum number of steps is the size of the system *)
        if step_n < size + 1 then aux (step_n + 1) n_delta u n_y
          (* If the delta increases, the method diverges. Also interupts in
             case the delta reaches an impossible value *)
        else if K.gt n_delta delta || K.lt n_delta K.zero then None
          (* Otherwise, check if the delta is below the given epsilon.
             If it is the case, we reached the solution. Otherwise, keep iterating *)
        else if K.leq n_delta e then Some (Vector.to_map n_y)
        else aux (step_n + 1) n_delta u n_y
      in
      aux 0 K.zero u y

  (** Estimation of the convergence radius. Since the system is well founded, it exists and is
    between 0 and 1. Uses a bisection method: the newtown iteration method converges for a
    certain value iff it is inside the convergence disk (TODO: citation needed).
   
    @param s the mapping of known samplers appearing in the system
    @param h a vector of species such that Y = h(Z,Y) is well founded
    @param j the Jacobian of h
    @param epsilon the precision of the bisection method. If rc is the expected value
    and rc_e is the one obtained, then we have rc >= rc_e >= (1-epsilon)*rc
    @return approximation of the convergence radius of the system with precision [epsilon].
 *)
  let eval_convergence_radius (h : species_system) (j : M_z.t) (epsilon : K.t) :
      K.t * K.t LClassMap.t option =
    (* assert (is_well_founded h j); *)
    let khalf = K.(inv (add one one)) in
    let gen_f = newton_iteration h j in
    let dist_2 x y =
      let df =
        Vector.union
          (fun _ a b -> Some (K.abs (K.sub a b)))
          (Vector.filter (fun k _ -> Literal.Class.is_base k) (Vector.of_map x))
          (Vector.filter (fun k _ -> Literal.Class.is_base k) (Vector.of_map y))
      in
      V_k.mul_dot df (Vector.map (fun _ -> K.one) df)
    in
    let rec aux step rc_tmp v0 v1 v2 last_ok last_ok_val okcpt =
      (* Bisection method. Returns the last element for which the newton method converged *)
      let (new_rc, last_ok, v3, last_ok_val, okcpt) =
        match gen_f epsilon rc_tmp with
        | Some x ->
            (* converges *) (K.add rc_tmp step, rc_tmp, Some x, x, okcpt + 1)
        | None ->
            (* diverges *)
            (K.add last_ok step, last_ok, None, last_ok_val, okcpt)
      in
      let (v0, v1, v2) =
        match v3 with
        | None -> (v0, v1, v2)
        | Some x ->
            if okcpt = 1 then (x, x, x)
            else if okcpt = 2 then (v1, x, x)
            else (v1, v2, x)
      in
      if K.lt step (K.mul khalf epsilon) then
        if K.(lt (dist_2 v1 v2) (dist_2 v0 v1)) then (last_ok, Some last_ok_val)
        else (last_ok, None)
      else aux (K.mul step khalf) new_rc v0 v1 v2 last_ok last_ok_val okcpt
    in
    aux
      khalf
      K.zero
      LClassMap.empty
      LClassMap.empty
      LClassMap.empty
      K.zero
      LClassMap.empty
      0

  let classify (h : species_system) (j : M_z.t) (epsilon : K.t) =
    match is_polynomial h with
    | Some s -> Poly s
    | None -> (
        match eval_convergence_radius h j epsilon with
        | (rc, None) -> Seq rc
        | (rc, Some evald) -> Tree (rc, evald))

  let get_exp_seq h j lit epsilon z =
    match newton_iteration h j epsilon z with
    | None -> assert false
    | Some v ->
        let f = LClassMap.find lit v in
        let f' = LClassMap.find (Literal.Class.deriv lit) v in
        K.(div (mul z f') f)

  let find_z_seq h j lit epsilon rc n =
    let n = K.of_Q (Q.of_int n) in
    let khalf = K.(inv (add one one)) in
    let start = K.mul rc khalf in
    let rec aux step z =
      let exp = get_exp_seq h j lit epsilon z in
      if K.lt (K.abs (K.sub exp n)) epsilon then z
      else
        let step = K.mul step khalf in
        if K.lt exp n then aux step (K.sub z step) else aux step (K.add z step)
    in
    aux start start

  (* TODO ? *)
  let find_z_poly _h _lit _epsilon n = K.of_Q (Q.of_int n)

  let find_best_z (h : species_system) (lit : Literal.Class.t) (j : M_z.t)
      (epsilon : K.t) (avg_size : int) =
    match classify h j epsilon with
    | Poly s -> find_z_poly s lit epsilon avg_size
    | Seq rc -> find_z_seq h j lit epsilon rc avg_size
    | Tree (rc, _) -> rc

  let solve (h : species_system) (lit : Literal.Class.t) (epsilon : K.t)
      (avg_size : int) =
    let j = S_z.make_jacobian (Vector.of_map h) in
    let z = find_best_z h lit j epsilon avg_size in
    let res = newton_iteration h j epsilon z in
    (z, Option.map (LClassMap.filter (fun k _ -> Literal.Class.is_base k)) res)

  let solve_class cc =
    let name = Combi.get_name cc in
    let h = translate_class cc in
    let h = include_deriv h in
    solve h name
end
