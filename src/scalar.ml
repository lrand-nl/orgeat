open Smol

module type Ring_ext = sig
  include Algebra.Ring_S

  val mul_int : int -> t -> t
end

module type Ordered_S = sig
  type t

  val compare : t -> t -> int

  val leq : t -> t -> bool

  val geq : t -> t -> bool

  val lt : t -> t -> bool

  val gt : t -> t -> bool
end

module type S = sig
  type t

  include Algebra.Field_S with type t := t

  include Ordered_S with type t := t

  val mul_int : int -> t -> t

  val abs : t -> t

  val exp : t -> t

  val log : t -> t

  val of_Q : Q.t -> t

  val of_float : float -> t
end

module F : S with type t = Float.t = struct
  include Float

  let mul_int i = mul (Float.of_int i)

  let of_Q x = Q.to_float x

  let of_float x = x

  let inv = div one

  let gt a b = compare a b > 0

  let geq a b = compare a b >= 0

  let lt a b = compare a b < 0

  let leq a b = compare a b <= 0
end

let float_scalar_with ~n_bits =
  let module M : S = struct
    type t = Q.t * int

    let zero = (Q.zero, 0)

    let one = (Q.one, 0)

    let shift_z z =
      let k = max 0 (Z.numbits z - n_bits) in
      (Z.shift_right z k, k)

    let of_Q q =
      let (num, ni) = shift_z (Q.num q) in
      let (den, di) = shift_z (Q.den q) in
      (Q.make num den, ni - di)

    let of_float x = of_Q (Q.of_float x)

    let to_Q (q, i) =
      if i > 0 then Q.mul_2exp q i else if i < 0 then Q.div_2exp q (-i) else q

    let equal a b = Q.equal (to_Q a) (to_Q b)

    let compare a b = Q.compare (to_Q a) (to_Q b)

    let add a b = of_Q (Q.add (to_Q a) (to_Q b))

    let neg (q, i) = (Q.neg q, i)

    let sub a b = add a (neg b)

    let abs (q, i) = (Q.abs q, i)

    let mul (q1, i1) (q2, i2) =
      let (qr, ir) = of_Q (Q.mul q1 q2) in
      (qr, ir + i1 + i2)

    let mul_int i (q, e) =
      let (qr, ir) = of_Q (Q.mul (Q.of_int i) q) in
      (qr, ir + e)

    let inv (q, i) = (Q.inv q, -i)

    let div a b = mul a (inv b)

    let gt a b = compare a b > 0

    let geq a b = compare a b >= 0

    let lt a b = compare a b < 0

    let leq a b = compare a b <= 0

    let to_string t = Q.to_string (to_Q t)

    (* TODO fix *)
    let exp x = x

    let log x = x
  end in
  (module M : S)

module Q : S with type t = Q.t = struct
  module Q_ : S with type t = Q.t = struct
    include Q

    let mul_int _ = assert false

    let of_Q _ = assert false

    (* TODO fix *)
    let exp x = x

    let log x = x
  end

  include Q_

  let mul_int i = Q.mul (Q.of_int i)

  let of_Q x = x

  let gt a b = compare a b > 0

  let geq a b = compare a b >= 0

  let lt a b = compare a b < 0

  let leq a b = compare a b <= 0
end
