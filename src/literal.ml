module Class = struct
  type t = C of string | D of t

  let rec compare a b =
    match (a, b) with
    | (C a, C b) -> String.compare a b
    | (D a, D b) -> compare a b
    | (C _, D _) -> 1
    | (D _, C _) -> -1

  let rec equal a b =
    match (a, b) with
    | (C a, C b) -> String.equal a b
    | (D a, D b) -> equal a b
    | _ -> false

  let rec to_string = function C x -> x | D x -> "∂" ^ to_string x

  let is_base = function C _ -> true | _ -> false

  let of_string x = C x

  let deriv x = D x
end

module Variable = struct
  include String

  let of_string x = x

  let to_string x = x

  let z = "z"
end
