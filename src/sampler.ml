open Misc

type 'a t = Random.State.t -> 'a

let gen _ _ = (0, ())

(* BOLTZMANN SAMPLERS *)

module Boltzmann (K : Scalar.S) = struct
  module P = struct
    include Poly_Var.Make_Ring (K)

    let mul_int i = map (K.mul_int i)
  end

  module S_applied = Species.Make_Sc (K)
  module S = Species.Make_R (P)

  (** The first parameter is a real between 0 and rc that controls the size of the generated objects. *)
  type 'a sampler = K.t -> Random.State.t -> int * 'a

  type 'a info = {gen : 'a sampler; f : S.t}

  let eval f z =
    S_applied.map
      (fun p ->
        P.eval (LVarMap.singleton Literal.Variable.z z) p |> P.apply_at_0)
      f
    |> S_applied.get_value

  let zero =
    {
      gen = (fun _ _ -> assert false);
      (* One cannot generate an element from the empty species. *)
      f = S.zero;
    }

  let one = {gen; f = S.one}

  let z =
    {
      gen = (fun _ _ -> (1, ()));
      f = S.of_scalar (P.of_literal Literal.Variable.z);
    }

  let scalar k =
    assert (k >= K.zero) ;
    if k = K.zero then zero else {gen; f = S.of_scalar (P.of_scalar k)}

  let info_of_sampler s = {one with gen = (fun _ state -> (0, s state))}

  let of_list = function
    | [] -> fun _ -> assert false
    | [e] -> fun _ -> e
    | _ :: _ as elements ->
        let size = List.length elements in
        let gen state = List.nth elements (Random.State.int state size) in
        (* valid, TODO think about it harder {(scalar (K.of_int size)) with gen} *)
        gen
end

(*** ---- For Data-encoding ---- ***)

let bool state = Random.State.bool state

let int ?(max = Int.shift_left 1 30 - 1) state = Random.State.int state max

let int32 ?(max = Int32.max_int) state = Random.State.int32 state max

let int64 ?(max = Int64.max_int) state = Random.State.int64 state max

let z_int ?max state = Z.of_int64 (int64 ?max state)

let n_int ?max state = Z.abs (z_int ?max state)

let ranged_int min max state = min + Random.State.int state (max - min + 1)

let ranged_float min max state = min +. Random.State.float state (max -. min)

let float ?(max = Float.max_float) state = Random.State.float state max

let bytes_fixed size state =
  Bytes.init size (fun _ -> Char.chr (ranged_int 20 126 state))

let bytes_var ?(max_size = 100) state =
  int ~max:max_size state |> fun s -> bytes_fixed s state

let string_fixed size state = bytes_fixed size state |> Bytes.to_string

let string_var ?(max_size = 100) state =
  bytes_var ~max_size state |> Bytes.to_string
