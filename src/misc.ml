exception Random_from_list_empty_input

module StringMap = Map.Make (String)

module StringPairs = struct
  type t = string * string

  let compare (x0, y0) (x1, y1) =
    match Stdlib.compare x0 x1 with 0 -> Stdlib.compare y0 y1 | c -> c
end

module StringMatrix = Map.Make (StringPairs)
module Poly_Class = Smol.Polynomial.Make (Literal.Class)
module Poly_Var = Smol.Polynomial.Make (Literal.Variable)
module LClassMap = Map.Make (Literal.Class)
module LVarMap = Map.Make (Literal.Variable)

(* Random functions on K.t *)

let random_from_list (type k) (module K : Scalar.S with type t = k)
    (l : (k * 'a) list) state : 'a =
  if l = [] then raise Random_from_list_empty_input
  else
    let (l, sum) =
      List.fold_left
        (fun (acc, s) (q, x) ->
          let sq = K.add s q in
          ((sq, x) :: acc, sq))
        ([], K.zero)
        l
    in
    let l =
      List.map (fun (q, i) -> (K.div q sum, i)) l
      |> List.sort (fun (a, _) (b, _) -> K.compare a b)
    in
    let rec aux x = function
      | [] -> x
      | l -> (
          (* We expand the interval to [0;2], then cut it in half *)
          let (l0, l1) =
            List.map (fun (k, j) -> (K.mul_int 2 k, j)) l
            |> List.partition (fun (k, _) -> K.leq k K.one)
          in
          if Random.State.bool state then
            (* We translate the interval to keep it at [0;1] *)
            List.map (fun (k, j) -> (K.sub k K.one, j)) l1 |> aux x
          else match l1 with [] -> aux x l0 | x :: _ -> aux x l0)
    in
    snd (aux (List.hd l) l)

let random_bern (type k) (module K : Scalar.S with type t = k) (x : k) state =
  if K.(geq x one) then true
  else
    let rec aux x =
      let x = K.mul_int 2 x in
      let b = Random.State.bool state in
      if b && K.lt x K.one then false
      else if (not b) && K.geq x K.one then true
      else if b then aux (K.sub x K.one)
      else aux x
    in
    aux x

let pp_tree (a : string) (ls : string list list) : string list =
  let rec aux_intern l =
    match l with [] -> [] | h :: t -> ("│   " ^ h) :: aux_intern t
  in
  let rec aux_extern l =
    match l with [] -> [] | h :: t -> ("    " ^ h) :: aux_extern t
  in
  let rec aux_main l =
    match l with
    | [] -> []
    | [h] -> (
        match h with [] -> [] | hh :: ht -> ("└── " ^ hh) :: aux_extern ht)
    | h :: i :: t -> (
        match h with
        | [] -> aux_main (i :: t)
        | hh :: ht -> (("├── " ^ hh) :: aux_intern ht) @ aux_main (i :: t))
  in
  a :: aux_main ls

let pp_string_list =
  Format.pp_print_list ~pp_sep:Format.pp_print_newline Format.pp_print_string
