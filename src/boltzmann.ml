open Misc

exception Size_stop

module Sampling (K : Scalar.S) = struct
  module Combi = Combi.Make (K)
  module Boltzmann = Sampler.Boltzmann (K)
  module Solver = Solver.Make (K)

  let rec unsolve : type c. c Combi.combi_class -> unit =
   fun cc ->
    let rec aux : type a. a Combi.solved_tree -> unit =
     fun t ->
      let (T (_, t)) = t in
      match t with
      | Combi.S_One | Combi.S_Z | Combi.S_Empty | Combi.S_Sampler _ -> ()
      | Combi.S_Union l -> List.iter aux l
      | Combi.S_Product (a, b) ->
          aux a ;
          aux b
      | Combi.S_Sequence (_, a) -> aux a
      | Combi.S_Map (a, _) -> aux a
      | Combi.S_Class cc -> unsolve cc
    in
    let t = Combi.get_solved cc in
    Combi.reset_solved cc ;
    match t with None -> () | Some t -> aux t

  let rec solve_tree :
      type a.
      K.t -> K.t LClassMap.t -> a Combi.class_tree -> a Combi.solved_tree =
   fun z sp ct ->
    match ct with
    | Combi.One -> T (K.one, S_One)
    | Sampler s -> T (K.one, S_Sampler s)
    | Z -> T (z, S_Z)
    | Empty -> T (K.zero, S_Empty)
    | Scalar x -> if K.(equal x zero) then T (K.zero, S_Empty) else T (x, S_One)
    | Class o_cc ->
        let o_name = Combi.get_name o_cc in
        T (LClassMap.find o_name sp, S_Class o_cc)
    | Union ctl ->
        let ctl_s = List.map (solve_tree z sp) ctl in
        let sum =
          List.fold_left
            (fun x y ->
              let (Combi.T (v, _)) = y in
              K.add x v)
            K.zero
            ctl_s
        in
        T (sum, S_Union ctl_s)
    | Product (act, bct) ->
        let (T (va, _) as sta) = solve_tree z sp act in
        let (T (vb, _) as stb) = solve_tree z sp bct in
        T (K.mul va vb, S_Product (sta, stb))
    | Sequence ({min; max}, st) ->
        let (T (vs, _) as ts) = solve_tree z sp st in
        let ki = K.(inv (sub one vs)) in
        let module M = Smol.Monomial.Make (Literal.Variable) in
        let app_m m =
          M.apply (module K) m (LVarMap.singleton Literal.Variable.z vs) |> fst
        in
        let m1 = app_m (M.singleton Literal.Variable.z min) in
        let m2 =
          match max with
          | None -> K.zero
          | Some max -> app_m (M.singleton Literal.Variable.z (max - 1))
        in
        T (K.mul (K.sub m1 m2) ki, S_Sequence ({min; max}, ts))
    | Map (t, tr) ->
        let (T (v, _) as s) = solve_tree z sp t in
        T (v, S_Map (s, tr))

  let get_solved_tree :
      type a.
      K.t -> K.t LClassMap.t -> a Combi.combi_class -> a Combi.solved_tree =
   fun z sp cc ->
    let b = Combi.get_class cc in
    let st = Combi.get_solved cc in
    let b_unopt = Option.value b ~default:Combi.Empty in
    match st with
    | Some t -> t
    | None ->
        let t = solve_tree z sp b_unopt in
        Combi.update_solved cc t ;
        t

  let check_size ~max_size size =
    match max_size with Some ms when size > ms -> raise Size_stop | _ -> ()

  type _ konts =
    | K_Left :
        'right Combi.stub * (int * 'left -> int * 'right -> int * 'root)
        -> ('left -> 'root) konts
    | K_Right : (int * 'right -> int * 'root) -> ('right -> 'root) konts
    | K_Map : ('a -> 'b) -> ('a -> 'b) konts

  type _ klist =
    | K_Empty : ('a -> 'a) klist
    | K_Cons : (('a -> 'b) konts * ('b -> 'c) klist) -> ('a -> 'c) klist

  let konts_to_string = function
    | K_Left (_, _) -> "L"
    | K_Right _ -> "R"
    | K_Map _ -> "M"

  let rec klist_to_string : type a. a klist -> string = function
    | K_Empty -> "[]"
    | K_Cons (k, t) -> konts_to_string k ^ ":" ^ klist_to_string t

  let rec sample :
      type a.
      ?min_size:int ->
      ?max_size:int ->
      K.t ->
      K.t LClassMap.t ->
      a Combi.combi_class ->
      Random.State.t ->
      int * a =
   fun ?min_size ?max_size z sp cc state ->
    (* Sample a combi_class from its root. May return an exception when the
        generated object is too big (ceiled sampler) *)
    let rec sample_exn :
        type root.
        int ->
        root Combi.combi_class ->
        (root -> a) klist ->
        Random.State.t ->
        int * a =
     fun reserved_size cc k_root state ->
      let (T (_, t)) = get_solved_tree z sp cc in
      aux reserved_size t k_root state
    (* Auxiliary function, sample a sub tree *)
    and aux :
        type b.
        int -> b Combi.stub -> (b -> a) klist -> Random.State.t -> int * a =
     fun rs t k state ->
      match t with
      | Combi.S_One ->
          (* Size 0 *)
          eval rs k (Boltzmann.one.gen K.one state) state
      | S_Z ->
          (* Size 1 *)
          eval rs k (Boltzmann.z.gen K.one state) state
      | S_Empty ->
          (* Note: this case should never be matched. *)
          eval rs k (Boltzmann.zero.gen K.one state) state
      | S_Sampler s -> eval rs k (0, s state) state
      | S_Class c -> sample_exn rs c k state
      | S_Union l ->
          let l = List.map (fun (Combi.T (k, t)) -> (k, t)) l in
          let c = random_from_list (module K) l state in
          aux rs c k state
      | S_Product (T (_, t1), T (_, t2)) ->
          let prod (i1, left) (i2, right) = (i1 + i2, (left, right)) in
          aux rs t1 (K_Cons (K_Left (t2, prod), k)) state
      | S_Sequence (_skind, T (w, t)) as seq_t ->
          (* We treat sequences as combs when building them *)
          let append (i1, left) (i2, right) = (i1 + i2, left :: right) in
          if random_bern (module K) w state then
            aux rs t (K_Cons (K_Left (seq_t, append), k)) state
          else eval rs k (0, []) state
      | S_Map (T (_, t), tr) -> aux rs t (K_Cons (K_Map tr, k)) state
    (* Evaluates the continuations *)
    and eval :
        type b. int -> (b -> a) klist -> int * b -> Random.State.t -> int * a =
     fun rs k (s, t) state ->
      match k with
      | K_Empty -> (s, t)
      | K_Cons (K_Left (right_stub, app), krest) ->
          check_size ~max_size (s + rs) ;
          aux (s + rs) right_stub (K_Cons (K_Right (app (s, t)), krest)) state
      | K_Cons (K_Right app, krest) ->
          let (s, t) = app (s, t) in
          check_size ~max_size (s + rs) ;
          eval (s + rs) krest (s, t) state
      | K_Cons (K_Map tr, krest) ->
          (* We do not want maps to change the size of the objects anyways *)
          eval rs krest (s, tr t) state
    in
    (* Main "loop", retries until it generates an object between two size boundaries
        (rejecton sampler) *)
    try
      let (s, a) = sample_exn 0 cc K_Empty state in
      match min_size with
      | Some min_s when s < min_s -> raise Size_stop
      | _ -> (s, a)
    with Size_stop -> (sample [@tailrec]) ?min_size ?max_size z sp cc state

  let get_singular_boltzmann_sampler :
      type a.
      ?min_size:int ->
      ?max_size:int ->
      a Combi.combi_class ->
      K.t ->
      Random.State.t ->
      int * a =
   fun ?(min_size = 0) ?(max_size = 10) cc epsilon ->
    assert (min_size <= max_size) ;
    unsolve cc ;
    let (z, fz) = Solver.solve_class cc epsilon ((min_size + max_size) / 2) in
    match fz with
    | None ->
        assert false
        (* TODO this case should not happen, remove the option type *)
    | Some fz -> sample ~min_size ~max_size z fz cc
end
