open Orgeat

let seed = [|12345; 595; 10470|]

module BT = struct
  module K = Scalar.F
  module Sampling = Boltzmann.Sampling (K)
  module Combi = Combi.Make (K)

  type t = N of t * t | L

  let atom_to_string = function N _ -> "N" | L -> "L"

  let rec to_strings a =
    let open Misc in
    match a with
    | N (l, r) -> pp_tree (atom_to_string a) [to_strings l; to_strings r]
    | L -> pp_tree (atom_to_string a) []

  let pp ppf (n, a) =
    Format.fprintf ppf "%i\n%a" n Misc.pp_string_list (to_strings a)

  let c = Combi.new_class_of_str "t"

  let t_n = Combi.(Map (tup3 Z (Class c) (Class c), fun ((), a, b) -> N (a, b)))

  let t_l = Combi.(Map (Z, fun () -> L))

  let ct = Combi.(t_n + t_l)

  let () = Combi.update_class c ct

  let state = Random.State.make seed

  let test () =
    let sampler =
      Sampling.get_singular_boltzmann_sampler ~max_size:1000 c 0.000001
    in
    Format.printf "<><><><><><><><><><><><><><><><>\n%a\n\n" pp (sampler state) ;
    Format.printf "<><><><><><><><><><><><><><><><>\n%a\n\n" pp (sampler state) ;
    Format.printf "<><><><><><><><><><><><><><><><>\n%a\n\n" pp (sampler state) ;
    Format.printf "<><><><><><><><><><><><><><><><>\n%a\n\n" pp (sampler state) ;
    Alcotest.(check pass) "test" () ()
end

module CT = struct
  module K = Scalar.F
  module Sampling = Boltzmann.Sampling (K)
  module Combi = Combi.Make (K)

  type t = N of t list | L

  let atom_to_string = function N _ -> "N" | L -> "L"

  let rec to_strings a =
    let open Misc in
    match a with
    | N l -> pp_tree (atom_to_string a) (List.map to_strings l)
    | L -> pp_tree (atom_to_string a) []

  let pp ppf (n, a) =
    Format.fprintf ppf "%i\n%a" n Misc.pp_string_list (to_strings a)

  let c = Combi.new_class_of_str "t"

  let t_n = Combi.(Map (tup2 Z (seq (Class c)), fun ((), l) -> N l))

  let t_l = Combi.(Map (Z, fun () -> L))

  let ct = Combi.(t_n + t_l)

  let () = Combi.update_class c ct

  let state = Random.State.make seed

  let test () =
    let sampler =
      Sampling.get_singular_boltzmann_sampler ~max_size:1000 c 0.000001
    in
    Format.printf "<><><><><><><><><><><><><><><><>\n%a\n\n" pp (sampler state) ;
    Format.printf "<><><><><><><><><><><><><><><><>\n%a\n\n" pp (sampler state) ;
    Format.printf "<><><><><><><><><><><><><><><><>\n%a\n\n" pp (sampler state) ;
    Format.printf "<><><><><><><><><><><><><><><><>\n%a\n\n" pp (sampler state) ;
    Alcotest.(check pass) "test" () ()
end

module Seq = struct
  module K = Scalar.F
  module Sampling = Boltzmann.Sampling (K)
  module Combi = Combi.Make (K)

  type t = L | N of t

  let atom_to_string = function N _ -> "N" | L -> "L"

  let rec to_strings a =
    let open Misc in
    match a with
    | N l -> pp_tree (atom_to_string a) [to_strings l]
    | L -> pp_tree (atom_to_string a) []

  let pp ppf (n, a) =
    Format.fprintf ppf "%i\n%a" n Misc.pp_string_list (to_strings a)

  let c = Combi.new_class_of_str "t"

  let t_n = Combi.(Map (tup2 Z (Class c), fun ((), l) -> N l))

  let t_l = Combi.(Map (Z, fun () -> L))

  let ct = Combi.(t_n + t_l)

  let () = Combi.update_class c ct

  let state = Random.State.make seed

  let test () =
    let sampler =
      Sampling.get_singular_boltzmann_sampler ~max_size:1000 c 0.000001
    in
    Format.printf "<><><><><><><><><><><><><><><><>\n%a\n\n" pp (sampler state) ;
    Format.printf "<><><><><><><><><><><><><><><><>\n%a\n\n" pp (sampler state) ;
    Format.printf "<><><><><><><><><><><><><><><><>\n%a\n\n" pp (sampler state) ;
    Format.printf "<><><><><><><><><><><><><><><><>\n%a\n\n" pp (sampler state) ;
    Alcotest.(check pass) "test" () ()
end

module Poly = struct
  module K = Scalar.F
  module Sampling = Boltzmann.Sampling (K)
  module Combi = Combi.Make (K)

  type t = A | N of u

  and u = B | C

  let atom_to_string = function N _ -> "N" | A -> "A"

  let u_atom_to_string = function B -> "B" | C -> "C"

  let to_strings a =
    let open Misc in
    match a with
    | N l -> pp_tree (atom_to_string a) [[u_atom_to_string l]]
    | A -> pp_tree (atom_to_string a) []

  let pp ppf (n, a) =
    Format.fprintf ppf "%i\n%a" n Misc.pp_string_list (to_strings a)

  let c = Combi.new_class_of_str "t"

  let c_ = Combi.new_class_of_str "u"

  let t_n = Combi.(Map (tup2 Z (Class c_), fun ((), l) -> N l))

  let t_a = Combi.(Map (Z, fun () -> A))

  let ct = Combi.(t_n + t_a)

  let () = Combi.update_class c ct

  let u_b = Combi.(Map (Z, fun () -> B))

  let u_c = Combi.(Map (Z, fun () -> C))

  let cu = Combi.(u_b + u_c)

  let () = Combi.update_class c_ cu

  let state = Random.State.make seed

  let test () =
    let sampler =
      Sampling.get_singular_boltzmann_sampler ~max_size:1000 c 0.000001
    in
    Format.printf "<><><><><><><><><><><><><><><><>\n%a\n\n" pp (sampler state) ;
    Format.printf "<><><><><><><><><><><><><><><><>\n%a\n\n" pp (sampler state) ;
    Format.printf "<><><><><><><><><><><><><><><><>\n%a\n\n" pp (sampler state) ;
    Format.printf "<><><><><><><><><><><><><><><><>\n%a\n\n" pp (sampler state) ;
    Alcotest.(check pass) "test" () ()
end

module Encoded = struct
  type t = A of string | B of bool | I of int | F of float | R of t * t

  let cases_encoding : t Data_encoding.t =
    let open Data_encoding in
    mu "recursive" (fun recursive ->
        union
          [
            case
              (Tag 0)
              ~title:"A"
              string
              (function A s -> Some s | _ -> None)
              (fun s -> A s);
            case
              (Tag 1)
              ~title:"B"
              bool
              (function B bool -> Some bool | _ -> None)
              (fun bool -> B bool);
            case
              (Tag 2)
              ~title:"I"
              int31
              (function I int -> Some int | _ -> None)
              (fun int -> I int);
            case
              (Tag 3)
              ~title:"F"
              float
              (function F float -> Some float | _ -> None)
              (fun float -> F float);
            case
              (Tag 4)
              ~title:"R"
              (obj2 (req "field1" recursive) (req "field2" recursive))
              (function R (a, b) -> Some (a, b) | _ -> None)
              (fun (a, b) -> R (a, b));
          ])

  let atom_to_string = function
    | A s -> Format.sprintf "A %s" s
    | B b -> Format.sprintf "B %s" (Bool.to_string b)
    | I i -> Format.sprintf "I %i" i
    | F f -> Format.sprintf "F %f" f
    | R (_, _) -> "R"

  let rec to_strings (a : t) =
    let open Misc in
    match a with
    | A _ | B _ | I _ | F _ -> pp_tree (atom_to_string a) []
    | R (l, r) -> pp_tree (atom_to_string a) [to_strings l; to_strings r]

  let pp ppf (n, a) =
    Format.fprintf ppf "%i\n%a" n Misc.pp_string_list (to_strings a)

  let state = Random.State.make seed

  let test () =
    let sampler =
      Orgeat.From_encoding.sampler_of_encoding_with_sizes
        ~max_size:1000
        cases_encoding
    in
    Format.printf "<><><><><><><><><><><><><><><><>\n%a\n\n" pp (sampler state) ;
    Format.printf "<><><><><><><><><><><><><><><><>\n%a\n\n" pp (sampler state) ;
    Format.printf "<><><><><><><><><><><><><><><><>\n%a\n\n" pp (sampler state) ;
    Format.printf "<><><><><><><><><><><><><><><><>\n%a\n\n" pp (sampler state) ;
    Format.printf "<><><><><><><><><><><><><><><><>\n%a\n\n" pp (sampler state) ;
    Format.printf "<><><><><><><><><><><><><><><><>\n%a\n\n" pp (sampler state) ;
    Format.printf "<><><><><><><><><><><><><><><><>\n%a\n\n" pp (sampler state) ;
    Format.printf "<><><><><><><><><><><><><><><><>\n%a\n\n" pp (sampler state) ;
    Alcotest.(check pass) "test" () ()
end

let tests =
  [
    ( "Sampling",
      [
        ("test_binary", `Quick, BT.test);
        ("test_cayley", `Quick, CT.test);
        ("test_sequence", `Quick, Seq.test);
        ("test_polynomial", `Quick, Poly.test);
        ("test_encoding", `Quick, Encoded.test);
      ] );
  ]
