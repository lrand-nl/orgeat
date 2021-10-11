open Orgeat
open Misc
module Vector = Smol.Vector.Make (Literal.Class)

module type CONFIG = sig
  module K : Scalar.S

  val name : string

  val epsilon : K.t
end

module Float_config : CONFIG = struct
  module K = Scalar.F

  let name = "float"

  let epsilon = 1e-10
end

module Float_64_config : CONFIG = struct
  module K = (val Scalar.float_scalar_with ~n_bits:64)

  let name = "float_64"

  let epsilon = K.of_Q (Q.of_float 1e-10)
end

module Float_256_config : CONFIG = struct
  module K = (val Scalar.float_scalar_with ~n_bits:256)

  let name = "float_256"

  let epsilon = K.of_Q (Q.of_float 1e-10)
end

module TestEnvironment (Conf : CONFIG) = struct
  module K = Conf.K
  module Combi = Orgeat.Combi.Make (K)
  module V = Vector.Make_R (K)
  module S = Species.Make (K)
  module S_base = S.S_base
  module S_applied = S.S_applied

  open Solver.Make (K)

  type test_kind = Poly_k | Seq_k of K.t option | Tree_k of K.t option

  let u x = Combi.Map (x, fun _ -> ())

  let almost_equal_q e x y = K.(lt (abs (sub x y)) e)

  let almost_equal_vector e x y =
    Vector.merge
      (fun _ vx vy ->
        match (vx, vy) with
        | (Some ax, Some ay) -> Some (almost_equal_q e ax ay)
        | _ -> None)
      x
      y
    |> Vector.for_all (fun _ x -> x)

  let to_string_to_pp f fmt x = Format.pp_print_string fmt (f x)

  let t_q_e e =
    Alcotest.testable (to_string_to_pp K.to_string) (almost_equal_q e)

  let t_vect_e e =
    Alcotest.testable (to_string_to_pp V.to_string) (almost_equal_vector e)

  let epsilon = Conf.epsilon

  module type COMBI = sig
    val name : string

    val species : S_base.t LClassMap.t

    val is_well_founded : bool

    (** None is when not provided. Use Q.inf for polynomial species (which are not well founded btw) *)
    val kind : test_kind

    val test_values : (K.t * K.t * V.t option) list
  end

  module TestClass (C : COMBI) = struct
    let h = C.species

    let j = S_base.make_jacobian (Vector.of_map h)

    let full_test () =
      let iwf = C.is_well_founded in
      Alcotest.(check bool)
        (C.name ^ ":is_well_founded")
        iwf
        (is_well_founded h j) ;
      Format.print_flush () ;
      if iwf then (
        Format.printf "classification... \n" ;
        Format.print_flush () ;
        let rc =
          match (classify h j epsilon, C.kind) with
          | (Poly _, Poly_k) ->
              Alcotest.(check pass) (C.name ^ ":classified_as_poly_ok") () () ;
              K.one
          | (Seq rc, Seq_k None) ->
              Alcotest.(check pass) (C.name ^ ":classified_as_seq_ok") () () ;
              rc
          | (Tree (rc, _), Tree_k None) ->
              Alcotest.(check pass) (C.name ^ ":classified_as_tree_ok") () () ;
              rc
          | (Seq e_rc, Seq_k (Some rc)) ->
              Alcotest.check
                (t_q_e epsilon)
                (C.name ^ ":seq_eval_convergence_radius")
                rc
                e_rc ;
              rc
          | (Tree (e_rc, _), Tree_k (Some rc)) ->
              Alcotest.check
                (t_q_e epsilon)
                (C.name ^ ":tree_eval_convergence_radius")
                rc
                e_rc ;
              rc
          | _ ->
              Alcotest.(check reject) (C.name ^ ":wrong_classification") () () ;
              assert false
        in
        let nf = newton_iteration h j in
        List.iter
          (fun (z, eva, rv) ->
            match (nf epsilon z, rv) with
            | (None, _) ->
                Alcotest.(check bool)
                  (C.name ^ ":diverging_outside_of_convergence_disk")
                  true
                  (K.gt z rc)
            | (Some nv, Some cv) ->
                Alcotest.check
                  (t_vect_e (K.add epsilon eva))
                  (C.name ^ ":check_value_at:" ^ K.to_string z)
                  (Vector.of_map nv)
                  cv
            | (Some v, None) ->
                Format.printf
                  "f(%s)=\n%s\n"
                  (K.to_string z)
                  (V.to_string (Vector.of_map v)) ;
                Alcotest.(check bool)
                  (C.name ^ ":converging_inside_of_convergence_disk")
                  true
                  (K.lt z rc))
          C.test_values)

    let tests = [("Test " ^ C.name, `Quick, full_test)]
  end

  module BinaryTreesClass : COMBI = struct
    let name = "Binary_Trees"

    let c = Combi.new_class_of_str "t"

    let c_name = Combi.get_name c

    let self = Combi.Class c

    (** Binary trees: T = Z + ZT² *)
    let t = Combi.(Z + u (Z * self * self))

    let () = Combi.update_class c t

    let species = translate_class c

    let is_well_founded = true

    let kind = Tree_k (Some (K.of_float 0.5))

    let test_values =
      [
        ( K.of_float 0.1,
          K.of_float 0.0000000001,
          Some (Vector.singleton c_name (K.of_float 0.10102051443)) );
      ]
  end

  module BinaryTreesTests = TestClass (BinaryTreesClass)

  module CayleyTreesClass : COMBI = struct
    let name = "Cayley_Trees"

    let c = Combi.new_class_of_str "t"

    let c_name = Combi.get_name c

    let self = Combi.Class c

    (** Cayley Trees: T = Z.Seq(T) *)
    let t = Combi.(u (Z * seq self))

    let () = Combi.update_class c t

    let species = translate_class c

    let is_well_founded = true

    let kind = Tree_k (Some (K.of_float 0.25))

    let test_values =
      [
        ( K.of_float 0.1,
          K.of_float 0.000000000001,
          Some (Vector.singleton c_name (K.of_float 0.11270166537925831)) );
      ]
  end

  module CayleyTreesTests = TestClass (CayleyTreesClass)

  module ExampleClass : COMBI = struct
    let name = "Example"

    (** Fig 1 *)
    let c0_r = Combi.new_class_of_str "c0"

    let _c0 = Combi.Class c0_r

    let c1_r = Combi.new_class_of_str "c1"

    let c1 = Combi.Class c1_r

    let c2_r = Combi.new_class_of_str "c2"

    let c2 = Combi.Class c2_r

    let c3_r = Combi.new_class_of_str "c3"

    let c3 = Combi.Class c3_r

    let t0 = u Combi.(Z * c1 * c2 * c3 * (c1 + c2))

    let t1 = Combi.(Z + u (Z * seq (c1 * c1 * c3 * c3)))

    let t2 = Combi.(Z + u (Z * Z * seq (Z * c2 * c2 * seq Z) * seq c2))

    let t3 =
      Combi.(
        Z
        + u
            (Z
            * (mul_scalar (K.of_float 3.) Z + u (Z * Z) + u (Z * Z * c1 * c3))
            * seq (c1 * c1)))

    let () =
      Combi.update_class c0_r (u t0) ;
      Combi.update_class c1_r (u t1) ;
      Combi.update_class c2_r (u t2) ;
      Combi.update_class c3_r (u t3)

    (*
    let _s = Combi.(Cons (c0_r, Cons (c1_r, Cons (c2_r, Single c3_r))))
     *)

    let species = translate_class c0_r

    let is_well_founded = true

    let kind = Tree_k None

    let test_values = [(K.of_float 0.1, K.zero, None)]
  end

  module ExampleTests = TestClass (ExampleClass)

  module SequenceClass : COMBI = struct
    let name = "Sequence"

    (** T = Seq(Z) *)
    let t = Combi.(seq Z)

    let t_name = Literal.Class.of_string "t"

    let species = translate t_name t

    let is_well_founded = true

    (* Convergence seem to not be as precise for sequence types regarding their rc.
       TODO: investigate why. *)
    let kind = Seq_k (Some K.one)

    let test_values =
      [
        ( K.of_float 0.1,
          K.zero,
          Some (Vector.singleton t_name (K.of_Q (Q.of_ints 10 9))) );
      ]
  end

  module SequenceTests = TestClass (SequenceClass)

  module MichelineClass : COMBI = struct
    let name = "Micheline"

    let c = Combi.new_class_of_str "t"

    let self = Combi.Class c

    (** T = 3Z + 2Z*Seq(T) *)
    let t =
      Combi.(
        mul_scalar (K.of_float 3.) Z
        + u (mul_scalar (K.of_float 2.) Z * seq self))

    let () = Combi.update_class c t

    let species = translate_class c

    let is_well_founded = true

    let kind = Tree_k None

    let test_values = [(K.of_Q (Q.of_ints 1 40), K.zero, None)]
  end

  module MichelineTests = TestClass (MichelineClass)

  module Fail1Class : COMBI = struct
    let name = "Fail1"

    let c = Combi.new_class_of_str "t"

    let self = Combi.Class c

    (** T = T *)
    let t = self

    let () = Combi.update_class c t

    let species = translate_class c

    let is_well_founded = false

    let kind = Poly_k

    let test_values = []
  end

  module Fail1Tests = TestClass (Fail1Class)

  module Fail2Class : COMBI = struct
    let name = "Fail2"

    let c = Combi.new_class_of_str "t"

    let self = Combi.Class c

    (** T = T + Z*T *)
    let t = Combi.(self + u (Z * self))

    let () = Combi.update_class c t

    let species = translate_class c

    let is_well_founded = false

    let kind = Poly_k

    let test_values = []
  end

  module Fail2Tests = TestClass (Fail2Class)

  module Fail3Class : COMBI = struct
    let name = "Fail3"

    let c = Combi.new_class_of_str "t"

    let self = Combi.Class c

    (** T = Z*T *)
    let t = u Combi.(Z * self)

    let () = Combi.update_class c t

    let species = translate_class c

    let is_well_founded = false

    let kind = Poly_k

    let test_values = []
  end

  module Fail3Tests = TestClass (Fail3Class)

  module Fail4Class : COMBI = struct
    let name = "Fail4"

    (** Example 8 *)
    let c0_r = Combi.new_class_of_str "c0"

    let c0 = Combi.Class c0_r

    let c1_r = Combi.new_class_of_str "c1"

    let c1 = Combi.Class c1_r

    let t0 = Combi.(One + u (c1 * c0))

    let t1 = Combi.One

    let () =
      Combi.update_class c0_r (u t0) ;
      Combi.update_class c1_r (u t1)

    (*
    let s = Combi.(Cons (c0_r, Single c1_r))
     *)

    let species = translate_class c0_r

    let is_well_founded = false

    let kind = Poly_k

    let test_values = []
  end

  module Fail4Tests = TestClass (Fail4Class)

  module OK1Class : COMBI = struct
    let name = "OK1"

    (** Example 8 *)
    let c0_r = Combi.new_class_of_str "c0"

    let c0 = Combi.Class c0_r

    let c1_r = Combi.new_class_of_str "c1"

    let _c1 = Combi.Class c1_r

    let t0 = Combi.(One + u (Z * c0))

    let t1 = Combi.(One + u (c0 * c0))

    let () =
      Combi.update_class c0_r (u t0) ;
      Combi.update_class c1_r (u t1)

    (*
    let s = Combi.(Cons (c0_r, Single c1_r))
     *)

    let species = translate_class c0_r

    let is_well_founded = true

    let kind = Tree_k None

    let test_values = []
  end

  module OK1Tests = TestClass (OK1Class)

  module PolyClass : COMBI = struct
    let name = "Poly"

    (** T = 1 + Z + Z^2 *)
    let t = Combi.(One + Z + u (Z * Z))

    let t_name = Literal.Class.of_string "t"

    let species = translate t_name t

    let is_well_founded = true

    let kind = Poly_k

    let test_values =
      [(K.of_float 2., K.zero, Some (Vector.singleton t_name (K.of_float 7.)))]
  end

  module PolyTests = TestClass (PolyClass)

  (* TODO seq at least, seq at most, seq bounded, *)
  module SeqBoundedClass : COMBI = struct
    let name = "Seq Bounded"

    (** T = Seq_{10<=n<=100}(Z) *)
    let t = Combi.(seq_bounded ~min:10 ~max:100 Z)

    let t_name = Literal.Class.of_string "t"

    let species = translate t_name t

    let is_well_founded = true

    let kind = Poly_k

    let test_values =
      [(K.one, K.zero, Some (Vector.singleton t_name (K.of_float 91.)))]
  end

  module SeqBoundedTests = TestClass (SeqBoundedClass)

  module SeqAtLeastClass : COMBI = struct
    let name = "Seq At Least"

    (** T = Seq_{10<=n}(Z) *)
    let t = Combi.(seq_bounded ~min:10 Z)

    let t_name = Literal.Class.of_string "t"

    let species = translate t_name t

    let is_well_founded = true

    let kind = Seq_k None

    let test_values = [(K.of_float 0.1, K.zero, None)]
  end

  module SeqAtLeastTests = TestClass (SeqAtLeastClass)

  module SeqAtMostClass : COMBI = struct
    let name = "Seq At Most"

    (** T = Seq_{n<=100}(Z) *)
    let t = Combi.(seq_bounded ~min:0 ~max:100 Z)

    let t_name = Literal.Class.of_string "t"

    let species = translate t_name t

    let is_well_founded = true

    let kind = Poly_k

    let test_values =
      [(K.one, K.zero, Some (Vector.singleton t_name (K.of_float 101.)))]
  end

  module SeqAtMostTests = TestClass (SeqAtMostClass)

  let tests =
    [
      ("solver_binary_tree_" ^ Conf.name, BinaryTreesTests.tests);
      ("solver_cayley_" ^ Conf.name, CayleyTreesTests.tests);
      ("solver_example_" ^ Conf.name, ExampleTests.tests);
      ("solver_sequence_" ^ Conf.name, SequenceTests.tests);
      ("solver_micheline_" ^ Conf.name, MichelineTests.tests);
      ("solver_polynomial_" ^ Conf.name, PolyTests.tests);
      ("solver_fail1", Fail1Tests.tests);
      ("solver_fail2", Fail2Tests.tests);
      ("solver_fail3", Fail3Tests.tests);
      ("solver_fail4", Fail4Tests.tests);
      ("solver_ok1", OK1Tests.tests);
      ("solver_seqbounded", SeqBoundedTests.tests);
      ("solver_seqatmost", SeqAtMostTests.tests);
      ("solver_seqatleast", SeqAtLeastTests.tests);
    ]
end

module T_Float = TestEnvironment (Float_config)
module T_Float_64 = TestEnvironment (Float_64_config)
module T_Float_256 = TestEnvironment (Float_256_config)

let tests =
  List.sort_uniq
    (fun (a, _) (b, _) -> Stdlib.compare a b)
    (List.flatten [T_Float.tests; T_Float_64.tests; T_Float_256.tests])
