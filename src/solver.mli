module Make (K : Scalar.S) : sig
  type species_system =
    K.t Smol.Polynomial.Make(Literal.Variable).p Species.s
    Map.Make(Literal.Class).t

  type solution_kind =
    | Poly of species_system
    | Seq of K.t
    | Tree of (K.t * K.t Map.Make(Literal.Class).t)

  (** Translate a [class_tree] into a system of equations *)
  val translate :
    Literal.Class.t -> 'a Combi.Make(K).class_tree -> species_system

  val translate_class : 'a Combi.Make(K).combi_class -> species_system

  (** Note for both translations: variables in [h] are prefixed with "T_", while
    in [sampler_mapping] they are prefixed with "s_" *)

  (** Algorithm isWellFounded
    Characterization of well-founded systems
    See Definition 5.3 and Theorem 5.5. This condition is sufficient to use Newton's
    iteration to evaluate the generating function of the combinatorial system.

    @param s the mapping of known samplers appearing in the system
    @param h a vector of species
    @param j the Jacobian of h. Note that it is also the Jacobian of the companion 
           system [k], so it does not need to be computed multiple times.
    @return true iff the system Y = H(Z,Y) is well founded
*)
  val is_well_founded :
    species_system ->
    K.t Smol.Polynomial.Make(Literal.Variable).p Species.s
    Smol.Matrix.Make(Literal.Class).m ->
    bool

  (** Newton iteration
   
    @param s the mapping of known samplers appearing in the system
    @param h a vector of species such that Y = h(Z,Y) is well founded
    @param j the Jacobian of h
    @param epsilon the precision of the evaluation
    @param z the point of evaluation
    @return some value approximating the solution at [z] with precision (at least) [epsilon], 
            or None if the iteration does not converges with the given parameters.
 *)
  val newton_iteration :
    species_system ->
    K.t Smol.Polynomial.Make(Literal.Variable).p Species.s
    Smol.Matrix.Make(Literal.Class).m ->
    K.t ->
    K.t ->
    K.t Map.Make(Literal.Class).t option

  (** Estimation of the convergence radius. Since the system is well founded, it exists and is
    between 0 and 1. Uses a bisection method: the newtown iteration method converges for a
    certain value iff it is inside the convergence disk (TODO: citation needed).
   
    @param s the mapping of known samplers appearing in the system
    @param h a vector of species such that Y = h(Z,Y) is well founded
    @param j the Jacobian of h
    @param epsilon the precision of the bisection method
    @return approximation of the convergence radius of the system with precision [epsilon].
 *)
  val eval_convergence_radius :
    species_system ->
    K.t Smol.Polynomial.Make(Literal.Variable).p Species.s
    Smol.Matrix.Make(Literal.Class).m ->
    K.t ->
    K.t * K.t Map.Make(Literal.Class).t option

  val classify :
    species_system ->
    K.t Smol.Polynomial.Make(Literal.Variable).p Species.s
    Smol.Matrix.Make(Literal.Class).m ->
    K.t ->
    solution_kind

  val solve :
    species_system ->
    Literal.Class.t ->
    K.t ->
    int ->
    K.t * K.t Map.Make(Literal.Class).t option

  val solve_class :
    'a Combi.Make(K).combi_class ->
    K.t ->
    int ->
    K.t * K.t Map.Make(Literal.Class).t option
end
