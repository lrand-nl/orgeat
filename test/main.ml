let () =
  Random.self_init () ;
  Alcotest.run
    "tezos-gen"
    (Test_species.tests @ Test_boltzmann.tests @ Test_solver.tests)
