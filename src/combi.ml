open Misc

module Make (K : Scalar.S) = struct
  module Boltzmann = Sampler.Boltzmann (K)

  (**
   Tree representation of the definition of a combinatorial class

Note: the functions in Map should be bijections whenever possible.
   Not doing so is not a problem in itself, but we can predict what will happen:
   - without injectivity, some elements will have a greater probability of occurence;
   - without surjectivity, the sampling will not be exhaustive.
   Please keep this notion in mind when manually creating [class_tree]s.
 *)

  type sequence_kind = {min : int; max : int option}

  let unbounded_seq = {min = 0; max = None}

  let bounded_seq min max = {min; max}

  type _ class_tree =
    (* Leaves of the tree *)
    | One : unit class_tree
    (* Skew *)
    | Scalar : K.t -> unit class_tree
    | Z : unit class_tree
    | Empty : 'a class_tree
    (* Arbitrary sampler, size one *)
    | Sampler : 'a Sampler.t -> 'a class_tree
    (* Reference to a class, used for recursion. *)
    | Class : 'a combi_class -> 'a class_tree
    | Union : 'a class_tree list -> 'a class_tree
    (* Product type, builds couples *)
    | Product : 'a class_tree * 'b class_tree -> ('a * 'b) class_tree
    (* Sequence constructor, for lists (not sets) *)
    | Sequence : sequence_kind * 'a class_tree -> 'a list class_tree
    (* Mapping, for types. *)
    | Map : 'a class_tree * ('a -> 'b) -> 'b class_tree

  and 'a solved_tree = T : (K.t * 'a stub) -> 'a solved_tree

  and 'a stub =
    | S_One : unit stub
    | S_Z : unit stub
    | S_Sampler : 'a Sampler.t -> 'a stub
    | S_Empty : 'a stub
    | S_Class : 'a combi_class -> 'a stub
    | S_Union : 'a solved_tree list -> 'a stub
    | S_Product : 'a solved_tree * 'b solved_tree -> ('a * 'b) stub
    | S_Sequence : sequence_kind * 'a solved_tree -> 'a list stub
    | S_Map : 'a solved_tree * ('a -> 'b) -> 'b stub

  (** Reference to a [class_tree] with a name.
    Allows for mutual recursion. *)
  and 'a combi_class = {
    name : Literal.Class.t;
    mutable class_tree : 'a class_tree option;
    mutable solved_tree : 'a solved_tree option;
  }

  let get_name cc = cc.name

  let get_class cc = cc.class_tree

  let get_solved cc = cc.solved_tree

  let new_class name : 'a combi_class =
    {name; class_tree = None; solved_tree = None}

  let new_class_of_str name = new_class (Literal.Class.of_string name)

  let reset_class cc = cc.class_tree <- None

  let update_class cc t = cc.class_tree <- Some t

  let reset_solved cc = cc.solved_tree <- None

  let update_solved cc t = cc.solved_tree <- Some t

  (** [tupn] generates a [t class_tree] where [t] is a tuple of size [n] 
    Useful before a Map to build records. *)
  let tup2 a b = Product (a, b)

  let tup3 a b c = Map (Product (tup2 a b, c), fun ((a, b), c) -> (a, b, c))

  let tup4 a b c d =
    Map (Product (tup3 a b c, d), fun ((a, b, c), d) -> (a, b, c, d))

  let tup5 a b c d e =
    Map (Product (tup4 a b c d, e), fun ((a, b, c, d), e) -> (a, b, c, d, e))

  (* etc... *)

  (** [mul_scalar k t] multiplies the given tree [t] with a weight [k].
   Used to skew the distribution without changing the generated objects.
 *)
  let mul_scalar k t =
    if K.(equal k zero) then Empty else Map (Product (Scalar k, t), snd)

  let ( + ) a b =
    match (a, b) with
    | (Union la, Union lb) -> Union (la @ lb)
    | (Union la, _) -> Union (la @ [b])
    | (_, Union lb) -> Union (a :: lb)
    | _ -> Union [a; b]

  let ( * ) = tup2

  let z a = Map (Z * a, snd)

  let seq a = Sequence (unbounded_seq, a)

  let seq_bounded ~min ?max a = Sequence (bounded_seq min max, a)

  let option a = Map (One, fun _ -> None) + Map (a, fun x -> Some x)

  let stub_node_to_string : type a. a stub -> string = function
    | S_One -> "1"
    | S_Z -> "Z"
    | S_Empty -> "∅"
    | S_Sampler _ -> "Sampler"
    | S_Class c -> "Class " ^ Literal.Class.to_string c.name
    | S_Union _ -> "Union"
    | S_Product (_, _) -> "Product"
    | S_Sequence _ -> "List of"
    | S_Map _ -> "Map"

  let solved_node_to_string : type a. a solved_tree -> string = function
    | T (z, stub) ->
        Format.asprintf "(w:%s) %s" (K.to_string z) (stub_node_to_string stub)

  let rec solved_to_strings : type a. a solved_tree -> string list =
   fun a ->
    let (T (_, stub)) = a in
    match stub with
    | S_One | S_Z | S_Empty | S_Class _ | S_Sampler _ ->
        pp_tree (solved_node_to_string a) []
    | S_Union l ->
        pp_tree (solved_node_to_string a) (List.map solved_to_strings l)
    | S_Product (l, r) ->
        pp_tree
          (solved_node_to_string a)
          [solved_to_strings l; solved_to_strings r]
    | S_Sequence (_skind, s) ->
        pp_tree (solved_node_to_string a) [solved_to_strings s]
    | S_Map (s, _) -> solved_to_strings s

  let pp_solved_tree fmt a = pp_string_list fmt (solved_to_strings a)
end
