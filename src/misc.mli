exception Random_from_list_empty_input

module StringMap : Map.S with type key = string

module StringMatrix : Map.S with type key = string * string

module Poly_Class : module type of Smol.Polynomial.Make (Literal.Class)

module Poly_Var : module type of Smol.Polynomial.Make (Literal.Variable)

module LClassMap : module type of Map.Make (Literal.Class)

module LVarMap : module type of Map.Make (Literal.Variable)

(* Random functions on K.t *)

(** [random_from_list state l] picks a random element from [l].
    Each element of [l] is given a weight which describes the distribution 
    probability of [l]. An element with a bigger weight relative to the other 
    elements of [l] will occur more frequently.
 *)
val random_from_list :
  (module Scalar.S with type t = 'k) -> ('k * 'a) list -> Random.State.t -> 'a

(** Bernouilli distribution.
    [random_bern state x] returns [true] with probability [x], and [false]
    with probability [1-x].
 *)

val random_bern :
  (module Scalar.S with type t = 'k) -> 'k -> Random.State.t -> bool

(* Tree printer helpers *)

(** [pp_tree root_tag sub_trees] prints a tree, from a tag for the root [root_tag], 
    and a list of sub-trees, each represented by its list of lines to print. *)
val pp_tree : string -> string list list -> string list

(** [pp_string_list] formats a list of string by separating them with newlines *)
val pp_string_list : Format.formatter -> string list -> unit
