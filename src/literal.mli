open Smol

module Class : sig
  include Literal.S

  val of_string : string -> t

  val deriv : t -> t

  val is_base : t -> bool
end

module Variable : sig
  include Literal.S

  val z : t

  val of_string : string -> t
end
