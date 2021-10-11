open Orgeat
open Misc
open Smol_helpers
module K = Scalar.Q
module S_ = Species.Make (K)
module S = S_.S_base
module Helpers = Test_helpers.Make (S)
module Helpers_bool = Test_helpers.Make (Bool)

module Deg = struct
  type t = int option

  let equal a b =
    match (a, b) with
    | (Some x, Some y) -> if x < 0 then y < 0 else x = y
    | (None, None) -> true
    | _ -> false

  let add x y =
    match (x, y) with (Some x, Some y) -> Some (max x y) | _ -> None

  let mul x y =
    match (x, y) with
    | (Some x, Some y) -> if x < 0 || y < 0 then Some (-1) else Some (x + y)
    | (Some x, None) | (None, Some x) -> if x < 0 then Some x else None
    | _ -> None

  let to_string = function
    | Some x -> "Some " ^ Int.to_string x
    | None -> "None"
end

module Helpers_deg = Test_helpers.Make (Deg)
module PS = Poly_Class.Make_Ring (S)
module Poly_VarK = Poly_Var.Make_Ring (K)
module Mono_Var = Smol.Monomial.Make (Literal.Variable)

let ampli = 256

let c1l = Literal.Class.of_string "[c1]"

let c2l = Literal.Class.of_string "[c2]"

let c3l = Literal.Class.of_string "[c3]"

let x = Literal.Variable.of_string "[x]"

let y = Literal.Variable.of_string "[y]"

let vars = [x; y; Literal.Variable.z]

let c1 = S.of_class c1l

let c2 = S.of_class c2l

let c3 = S.of_class c3l

let classes = [c1l; c2l; c3l]

let i () = Q.of_int (Random.int 10 - 5)

let random_mono l max_exp () =
  List.fold_left
    (fun m x -> LVarMap.add x (Random.int (max_exp + 1)) m)
    LVarMap.empty
    l
  |> Mono_Var.of_map

let random_poly l max_exp num_mono () =
  List.fold_left
    (fun acc _ ->
      Poly_VarK.add acc (Poly_VarK.singleton (random_mono l max_exp ()) (i ())))
    Poly_VarK.zero
    (List.init num_mono (fun _ -> ()))

let f x = x

let random_leaf () =
  List.nth
    [
      S.of_scalar (Poly_VarK.of_scalar (i ()));
      S.of_scalar (Poly_VarK.of_literal Literal.Variable.z);
    ]
    (Random.int 2)

let random_unary sp =
  let rk = Random.int 7 in
  if rk = 0 then S.seq sp
  else if rk = 1 then S.seq_at_least_n (Random.int 10) sp
  else if rk = 2 then S.seq_at_most_n (Random.int 10) sp
  else if rk = 3 then S.tuple_n (Random.int 10) sp
  else if rk = 4 then S.set sp
  else if rk = 5 then S.cycle sp
  else
    let m = Random.int 5 in
    S.seq_bounded ~min:m ~max:(m + Random.int 5) sp

let rec random_expr l max_length max_exp num_mono () =
  let lenl = List.length l in
  let e = List.nth l (Random.int lenl) in
  if lenl >= max_length then random_unary e
  else
    let rk = Random.int 9 in
    if rk = 0 then
      let new_e = S.mul_scalar (random_poly vars max_exp num_mono ()) e in
      random_expr (new_e :: l) max_length max_exp num_mono ()
    else if rk = 1 then
      let other_e = List.nth l (Random.int lenl) in
      let new_e = S.mul e other_e in
      random_expr (new_e :: l) max_length max_exp num_mono ()
    else if rk = 2 then
      let other_e = List.nth l (Random.int lenl) in
      let new_e = S.add e other_e in
      random_expr (new_e :: l) max_length max_exp num_mono ()
    else if rk = 3 then
      let other_e = List.nth l (Random.int lenl) in
      let new_e = S.sub e other_e in
      random_expr (new_e :: l) max_length max_exp num_mono ()
    else if rk = 4 || rk = 5 || rk = 6 then random_unary e
    else
      let new_e =
        S.of_class (List.nth classes (Random.int (List.length classes)))
      in
      random_expr (new_e :: l) max_length max_exp num_mono ()

let s_base max_depth ?(p = true) () =
  let rec aux rslt d =
    if d < 0 then rslt else aux (random_expr [rslt] 32 3 3 ()) (d - 1)
  in
  let a = aux (S.of_scalar (random_poly vars 3 3 ())) max_depth in
  if p then Format.printf "%a\n" Helpers.pp a ;
  a

let (name_tests, tests_algebra) =
  Test_helpers.make_tests_ring
    ~ampli
    ~name:"Species"
    ~commutative:true
    (module S)
    (s_base 4)

module Base = struct
  open Helpers

  let s () = s_base 3 ()

  let test_fresh () =
    let a = s () in
    check ~msg:"test_fresh" ~expected:a ~actual:(S.map (fun x -> x) a)

  let test_substitution_literal () =
    let a = s () in
    check
      ~msg:"test_substitution_literal_x"
      ~expected:a
      ~actual:(S.substitution (LClassMap.singleton c1l a) c1) ;
    check
      ~msg:"test_substitution_literal_y"
      ~expected:c2
      ~actual:(S.substitution (LClassMap.singleton c1l a) c2)

  let test_substitution_id () =
    let a = s () in
    check
      ~msg:"test_substitution_id"
      ~expected:a
      ~actual:(S.substitution (LClassMap.singleton c1l c1) a)

  let test_substitution_add () =
    let (a, b, c) = (s (), s (), s ()) in
    let l = LClassMap.singleton c1l c in
    let subst = S.substitution l in
    check
      ~msg:"test_substitution_add"
      ~expected:(S.add (subst a) (subst b))
      ~actual:(subst (S.add a b))

  let test_substitution_mul () =
    let (a, b, c) = (s (), s (), s ()) in
    let l = LClassMap.singleton c1l c in
    let subst = S.substitution l in
    check
      ~msg:"test_substitution_mul"
      ~expected:(S.mul (subst a) (subst b))
      ~actual:(subst (S.mul a b))

  let test_substitution_comp () =
    let (a, b, c) = (s (), s (), s ()) in
    let su = S.substitution in
    let l1 = LClassMap.singleton c1l c in
    let l2 = LClassMap.singleton c1l b in
    let bc = su l1 b in
    let l3 = LClassMap.singleton c1l bc in
    check
      ~msg:"test_substitution_comp"
      ~expected:(su l2 a |> su l1)
      ~actual:(su l3 a)

  let test_deriv_add () =
    let (a, b) = (s (), s ()) in
    let ab = S.add a b in
    let da = S.deriv_class c1l a in
    let db = S.deriv_class c1l b in
    let dab = S.deriv_class c1l ab in
    check ~msg:"test_deriv_add" ~expected:(S.add da db) ~actual:dab

  let test_deriv_mul () =
    let (a, b) = (s (), s ()) in
    let ab = S.mul a b in
    let da = S.deriv_class c1l a in
    let db = S.deriv_class c1l b in
    let dab = S.deriv_class c1l ab in
    check
      ~msg:"test_deriv_mul"
      ~expected:(S.add (S.mul a db) (S.mul da b))
      ~actual:dab

  let test_deriv_seq () =
    let a = s () in
    let sa = S.seq a in
    let da = S.deriv_class c1l a in
    let dsa = S.deriv_class c1l sa in
    check ~msg:"test_deriv_seq" ~expected:(S.mul da (S.mul sa sa)) ~actual:dsa

  let test_deriv_seq_at_least () =
    let a = s () in
    let n = Random.int 10 in
    Format.printf "n = %i\n" n ;
    let sqa = S.seq a in
    let sa = S.seq_at_least_n n a in
    let sda = S.seq_at_least_n (n - 1) a in
    let da = S.deriv_class c1l a in
    let dactual = S.deriv_class c1l sa in
    let sn = S.of_scalar (S_.P_z.mul_int n S_.P_z.one) in
    check
      ~msg:"test_deriv_seq_at_least"
      ~expected:(S.mul da (S.add (S.mul sn sda) (S.mul sqa sa)))
      ~actual:dactual

  let test_deriv_set () =
    let a = s () in
    let sa = S.set a in
    let da = S.deriv_class c1l a in
    let dsa = S.deriv_class c1l sa in
    check ~msg:"test_deriv_set" ~expected:(S.mul da sa) ~actual:dsa

  let test_deriv_cycle () =
    let a = s () in
    let sa = S.cycle a in
    let seqa = S.seq a in
    let da = S.deriv_class c1l a in
    let dsa = S.deriv_class c1l sa in
    check ~msg:"test_deriv_cycle" ~expected:(S.mul da seqa) ~actual:dsa

  let test_poly () =
    let a = s () in
    Helpers_bool.check
      ~msg:"test_poly"
      ~expected:(Option.is_some (S.deg_class c1l a))
      ~actual:(S.is_polynomial_wrt_class c1l a) ;
    Helpers_bool.check
      ~msg:"test_poly_z"
      ~expected:(Option.is_some (S.deg_z a))
      ~actual:(S.is_polynomial_wrt_z a)

  (* TODO fix: not equality, but inequality *)
  let test_deg_add () =
    let (a, b) = (s (), s ()) in
    let ab = S.add a b in
    let d_a = S.deg_class c1l a in
    let d_b = S.deg_class c1l b in
    let d_ab = S.deg_class c1l ab in
    let dz_a = S.deg_z a in
    let dz_b = S.deg_z b in
    let dz_ab = S.deg_z ab in
    Helpers_deg.check
      ~msg:"test_deg_add:deg"
      ~expected:(Deg.add d_a d_b)
      ~actual:d_ab ;
    Helpers_deg.check
      ~msg:"test_deg_add:deg_z"
      ~expected:(Deg.add dz_a dz_b)
      ~actual:dz_ab

  let test_deg_mul () =
    let (a, b) = (s (), s ()) in
    let ab = S.mul a b in
    let d_a = S.deg_class c1l a in
    let d_b = S.deg_class c1l b in
    let d_ab = S.deg_class c1l ab in
    let dz_a = S.deg_z a in
    let dz_b = S.deg_z b in
    let dz_ab = S.deg_z ab in
    Helpers_deg.check
      ~msg:"test_deg_mul:deg"
      ~expected:(Deg.mul d_a d_b)
      ~actual:d_ab ;
    Helpers_deg.check
      ~msg:"test_deg_mul:deg_z"
      ~expected:(Deg.mul dz_a dz_b)
      ~actual:dz_ab

  let test_deg_seq () =
    let a = s () in
    let sa = S.seq a in
    let d_a = S.deg_class c1l a in
    let d_sa = S.deg_class c1l sa in
    let dz_a = S.deg_z a in
    let dz_sa = S.deg_z sa in
    let expct = function Some x when x <= 0 -> Some 0 | _ -> None in
    Helpers_deg.check ~msg:"test_deg_seq:deg" ~expected:(expct d_a) ~actual:d_sa ;
    Helpers_deg.check
      ~msg:"test_deg_seq:deg_z"
      ~expected:(expct dz_a)
      ~actual:dz_sa

  let test_deg_set () =
    let a = s () in
    let sa = S.set a in
    let d_a = S.deg_class c1l a in
    let d_sa = S.deg_class c1l sa in
    let dz_a = S.deg_z a in
    let dz_sa = S.deg_z sa in
    let expct = function Some x when x <= 0 -> Some 0 | _ -> None in
    Helpers_deg.check ~msg:"test_deg_set:deg" ~expected:(expct d_a) ~actual:d_sa ;
    Helpers_deg.check
      ~msg:"test_deg_set:deg_z"
      ~expected:(expct dz_a)
      ~actual:dz_sa

  let test_deg_cycle () =
    let a = s () in
    let sa = S.cycle a in
    let d_a = S.deg_class c1l a in
    let d_sa = S.deg_class c1l sa in
    let dz_a = S.deg_z a in
    let dz_sa = S.deg_z sa in
    let expct = function Some x when x <= 0 -> Some x | _ -> None in
    Helpers_deg.check
      ~msg:"test_deg_cycle:deg"
      ~expected:(expct d_a)
      ~actual:d_sa ;
    Helpers_deg.check
      ~msg:"test_deg_cycle:deg_z"
      ~expected:(expct dz_a)
      ~actual:dz_sa

  let test_deg_seq_at_most () =
    let a = s () in
    let r = Random.int 10 + 1 in
    Format.printf "n = %i\n" r ;
    let sa = S.seq_at_most_n r a in
    let d_a = S.deg_class c1l a in
    let d_sa = S.deg_class c1l sa in
    let dz_a = S.deg_z a in
    let dz_sa = S.deg_z sa in
    let expct = function Some x -> Some (x * r) | None -> None in
    Helpers_deg.check
      ~msg:"test_deg_seq_at_most:deg"
      ~expected:(expct d_a)
      ~actual:d_sa ;
    Helpers_deg.check
      ~msg:"test_deg_seq_at_most:deg_z"
      ~expected:(expct dz_a)
      ~actual:dz_sa

  let tests =
    let open Test_helpers in
    [
      (Rand, "Test map identity", test_fresh);
      (Rand, "∀ a. a[x->x] = a", test_substitution_id);
      (Rand, "∀ a. x[x->r] = r and y[x->r] = y", test_substitution_literal);
      (Rand, "∀ a b c. (a+b)[x->c] = a[x->c] + b[x->c]", test_substitution_add);
      (Rand, "∀ a b c. (a×b)[x->c] = a[x->c] × b[x->c]", test_substitution_mul);
      ( Rand,
        "∀ a b c. (a[x->b])[x->c] = a[x->(b[x->c])]",
        test_substitution_comp );
      (Rand, "∀ a b. ∂(a+b) = ∂a + ∂b", test_deriv_add);
      (Rand, "∀ a b. ∂(a×b) = ∂a×b + a×∂b", test_deriv_mul);
      (Rand, "∀ a. ∂(Seq(a)) = ∂a × Seq²(a)", test_deriv_seq);
      ( Rand,
        "∀ a. ∂(Seq[≥n](a)) = ∂a × (n × Seq[≥n-1](a) + Seq(a) × Seq[≥n](a))",
        test_deriv_seq_at_least );
      (Rand, "∀ a. ∂(Set(a)) = ∂a × Set(a)", test_deriv_set);
      (Rand, "∀ a. ∂(Cycle(a)) = ∂a × Seq(a)", test_deriv_cycle);
      (Rand, "Test is_polynomial", test_poly);
      (Rand, "Test degree (add)", test_deg_add);
      (Rand, "Test degree (mul)", test_deg_mul);
      (Rand, "Test degree (seq)", test_deg_seq);
      (Rand, "Test degree (bounded seq)", test_deg_seq_at_most);
      (Rand, "Test degree (set)", test_deg_set);
      (Rand, "Test degree (cycle)", test_deg_cycle);
    ]
end

let tests =
  [(name_tests, tests_algebra @ Test_helpers.get_tests ampli Base.tests)]
