open Data_encoding__Encoding

(* TODO: modular K *)
module K = Scalar.F
module Combi = Combi.Make (K)
module Sampling = Boltzmann.Sampling (K)
module S = Sampler

type packed_class = P_class : 'a Combi.combi_class -> packed_class

exception Mu_Stop of packed_class

let based_info s = Combi.(z @@ Sampler s)

let based s = based_info s

(*** Invariant : P(0) = 0. Les feuilles sont pesées. On pourrait préférer peser les noeuds internes, 
     mais cela implique développer les Tups et Objs, et ce n'est pas forcément ce qu'on veut peser 
     pour les encodings en particulier ?
 ***)
let rec analyze_desc : type a. a desc -> a Combi.class_tree = function
  | Null -> Combi.Z
  | Empty -> Combi.Z
  | Ignore -> Combi.Z
  | Constant _ -> Combi.Z
  | Bool -> based S.bool
  | Int8 -> based (S.int ~max:10)
  | Uint8 -> based (S.int ~max:10)
  | Int16 -> based (S.int ~max:10)
  | Uint16 -> based (S.int ~max:10)
  | Int31 -> based (S.int ~max:10)
  | Int32 -> based S.int32
  | Int64 -> based S.int64
  | N -> based S.n_int
  | Z -> based S.z_int
  | RangedInt {minimum; maximum} -> based (S.ranged_int minimum maximum)
  | RangedFloat {minimum; maximum} -> based (S.ranged_float minimum maximum)
  | Float -> based (S.float ~max:3.)
  | Bytes sk -> (
      match sk with
      | `Variable -> based S.bytes_var
      | `Fixed size -> based (S.bytes_fixed size))
  | String sk -> (
      match sk with
      | `Variable -> based (S.string_var ~max_size:4)
      | `Fixed size -> based (S.string_fixed size))
  | Padded (a, _) -> analyze_desc a.encoding
  | String_enum (_, a) -> based_info (Combi.Boltzmann.of_list (Array.to_list a))
  | Array (max, a) ->
      Combi.(
        z
        @@ Map
             (Sequence ({min = 0; max}, analyze_desc a.encoding), Array.of_list))
  | List (max, a) ->
      Combi.(z @@ Sequence ({min = 0; max}, analyze_desc a.encoding))
  | Obj f -> (
      match f with
      | Req a -> analyze_desc a.encoding.encoding
      | Opt a -> Combi.(z @@ option (analyze_desc a.encoding.encoding))
      | Dft a -> analyze_desc a.encoding.encoding)
  | Objs {left; right; _} ->
      let left = analyze_desc left.encoding in
      let right = analyze_desc right.encoding in
      Combi.Product (left, right)
  | Tup a -> analyze_desc a.encoding
  | Tups {left; right; _} ->
      let left = analyze_desc left.encoding in
      let right = analyze_desc right.encoding in
      Combi.Product (left, right)
  | Union {cases; _} ->
      let l_cases =
        List.map
          (function
            | Case {encoding; inj; _} ->
                Combi.Map (analyze_desc encoding.encoding, inj))
          cases
      in
      Combi.Union l_cases
  | Conv {inj; encoding; _} -> Combi.Map (analyze_desc encoding.encoding, inj)
  | Describe {encoding; _} -> analyze_desc encoding.encoding
  | Splitted {encoding; _} -> analyze_desc encoding.encoding
  | Dynamic_size {encoding; _} -> analyze_desc encoding.encoding
  | Check_size {encoding; _} -> analyze_desc encoding.encoding
  | Mu {name; fix; kind; description; title} -> (
      try
        let new_cc = Combi.new_class (Literal.Class.of_string name) in
        let end_mu =
          Mu
            {
              name;
              fix = (fun _ -> raise (Mu_Stop (P_class new_cc)));
              kind;
              description;
              title;
            }
        in
        let fixed = (fix (make end_mu)).encoding in
        Combi.update_class new_cc (analyze_desc fixed) ;
        (* Alternative :Combi.(z @@ Class new_cc) *)
        Combi.(Class new_cc)
      with Mu_Stop (P_class p_cc) -> Combi.((* z @@ *) Class (Obj.magic p_cc)))
  | Delayed thunk ->
      let e = thunk () in
      analyze_desc e.encoding

(*** Temp, for tests only ***)

let sampler_of_encoding_with_sizes :
    type a. ?min_size:int -> ?max_size:int -> a encoding -> (int * a) Sampler.t
    =
 fun ?min_size ?max_size e ->
  let cc = Combi.new_class (Literal.Class.of_string "__root__") in
  Combi.update_class cc (analyze_desc e.encoding) ;
  Sampling.get_singular_boltzmann_sampler ?min_size ?max_size cc 0.00000001

let sampler_of_encoding :
    type a. ?min_size:int -> ?max_size:int -> a encoding -> a Sampler.t =
 fun ?min_size ?max_size e ->
  let si = sampler_of_encoding_with_sizes ?min_size ?max_size e in
  fun state -> snd (si state)
