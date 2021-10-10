exception Cannot_get_value

type 'a s

module Make_R (K : Scalar.Ring_ext) : sig
  type t = K.t s

  val deriv :
    (K.t -> K.t) ->
    (Literal.Class.t -> K.t Smol.Polynomial.Make(Literal.Class).p) ->
    t ->
    t

  val zero : t

  val is_zero : t -> bool

  val one : t

  val equal : t -> t -> bool

  val map : ('a -> K.t) -> 'a s -> t

  (** Operations **)
  val add : t -> t -> t

  val neg : t -> t

  val sub : t -> t -> t

  val mul : t -> t -> t

  val mul_scalar : K.t -> t -> t

  (** Constructors **)

  val seq : t -> t

  val set : t -> t

  val cycle : t -> t

  val seq_at_least_n : int -> t -> t

  val seq_at_most_n : int -> t -> t

  val tuple_n : int -> t -> t

  val seq_bounded : min:int -> max:int -> t -> t

  val of_scalar : K.t -> t

  val of_class : Literal.Class.t -> t

  val deriv_class : Literal.Class.t -> t -> t

  val substitution : t Map.Make(Literal.Class).t -> t -> t

  val eval : K.t Map.Make(Literal.Class).t -> t -> t

  val deg_class : Literal.Class.t -> t -> int option

  val is_polynomial_wrt_class : Literal.Class.t -> t -> bool

  val make_jacobian :
    t Smol.Vector.Make(Literal.Class).v -> t Smol.Matrix.Make(Literal.Class).m

  val to_string : t -> string
end

(** We can only evaluate species if they are defined on a ring *)
module Make_Sc (K : Scalar.S) : sig
  include module type of Make_R (K)

  (** @raise [Cannot_get_value] if a value cannot be inferred *)
  val get_value : t -> K.t

  val get_value_opt : t -> K.t option
end

module Make (K : Scalar.S) : sig
  module S_applied : module type of Make_Sc (K)

  module P_z :
    Scalar.Ring_ext with type t = K.t Smol.Polynomial.Make(Literal.Variable).p

  module S_base : sig
    include module type of Make_R (P_z)

    val eval_z_partial : K.t -> t -> t

    val eval_z : K.t -> t -> S_applied.t

    val deriv_z : t -> t

    val deg_z : t -> int option

    val is_polynomial_wrt_z : t -> bool
  end
end
