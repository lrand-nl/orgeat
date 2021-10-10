(lang dune 2.8)
(name orgeat)
(version 0.0.1)
(generate_opam_files true)
(source (uri git+https://github.com/lrand-nl/orgeat))
(bug_reports http://github.com/lrand-nl/orgeat)
(homepage http://github.com/lrand-nl/orgeat)
(authors "Lucas Randazzo")
(maintainers "lucas.randazzo@nomadic-labs.com")

(package
 (name orgeat)
 (synopsis "Ocaml Random Generation of Arbitrary Types")
 (description "Ocaml Random Generation of Arbitrary Types")
 (license MIT)
 (depends (dune (>= 2.8))
 	  (ocaml (>= 4.08.0))
	  zarith
	  data-encoding
	  smol
	  (smol.helpers :with-test)
    	  (alcotest :with-test))
)
