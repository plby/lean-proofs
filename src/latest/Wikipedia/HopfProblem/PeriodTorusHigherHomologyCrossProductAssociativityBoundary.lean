import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductAssociativityRealization

/-!
# The actual associator boundary identity

The explicit trilinear homotopy satisfies `d Q + Q d = D` on Mathlib's actual
singular chains. In particular, when the third factor is a cycle, the two
parenthesizations differ by the boundary of the displayed actual chain.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz SingularMayerVietoris

attribute [local instance] integerLinearMapModule integerTensorModule

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The actual associator homotopy identity in third degree zero. -/
theorem crossProductAssociatorHomotopy_boundary_zero
    (a : Chains X 1) (b : Chains Y 1) (c : Chains Z 0) :
    ((singularComplex (X × (Y × Z))).d 3 2).hom
        (crossProductAssociatorHomotopy X Y Z 0 a b c) =
      crossProductAssociatorDefect X Y Z 0 a b c := by
  have heq : integerTrilinearPostcompose (crossProductAssociatorHomotopy X Y Z 0)
        ((singularComplex (X × (Y × Z))).d 3 2).hom =
      crossProductAssociatorDefect X Y Z 0 := by
    apply chainTrilinearMap_ext X Y Z 1 1 0
    intro σ τ υ
    have hstd := crossProductAssociatorHomotopy_boundary_zero_affine 1 1 0
      (formalSimplex (stdVertices 1)) (formalSimplex (stdVertices 1))
      (formalSimplex (stdVertices 0))
    have hστυ := congrArg (inducedChain (σ.prodMap (τ.prodMap υ)) 2) hstd
    simpa only [integerTrilinearPostcompose_apply, inducedChain_boundary,
      crossProductAssociatorHomotopy_natural, crossProductAssociatorDefect_natural,
      affineChainMap_stdVertices, inducedChain_simplex, ContinuousMap.comp_id] using hστυ
  exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun heq a) b) c

/-- Associativity is strict if the third factor is a zero-chain. -/
@[simp] theorem crossProductAssociatorDefect_zero
    (a : Chains X 1) (b : Chains Y 1) (c : Chains Z 0) :
    crossProductAssociatorDefect X Y Z 0 a b c = 0 := by
  have h := crossProductAssociatorHomotopy_boundary_zero a b c
  simpa only [crossProductAssociatorHomotopy_zero, map_zero] using h.symm

/-- The two actual parenthesizations agree on a third factor of degree zero. -/
theorem crossProduct_associativity_zero
    (a : Chains X 1) (b : Chains Y 1) (c : Chains Z 0) :
    inducedChain (Homeomorph.prodAssoc X Y Z : C(_, _)) 2
        (crossProductTriangle (X × Y) Z 0 (crossProductEdge X Y 1 a b) c) =
      crossProductEdge X (Y × Z) 1 a (crossProductEdge Y Z 0 b c) :=
  sub_eq_zero.mp (crossProductAssociatorDefect_zero a b c)

/-- The chain identity `d Q + Q d = D`, with no cycle hypotheses on any input. -/
theorem crossProductAssociatorHomotopy_boundary (n : ℕ)
    (a : Chains X 1) (b : Chains Y 1) (c : Chains Z (n + 1)) :
    ((singularComplex (X × (Y × Z))).d (n + 4) (n + 3)).hom
        (crossProductAssociatorHomotopy X Y Z (n + 1) a b c) +
      crossProductAssociatorHomotopy X Y Z n a b
        (((singularComplex Z).d (n + 1) n).hom c) =
      crossProductAssociatorDefect X Y Z (n + 1) a b c := by
  have heq : integerTrilinearPostcompose (crossProductAssociatorHomotopy X Y Z (n + 1))
        ((singularComplex (X × (Y × Z))).d (n + 4) (n + 3)).hom +
      integerTrilinearPrecompose (crossProductAssociatorHomotopy X Y Z n)
        LinearMap.id LinearMap.id ((singularComplex Z).d (n + 1) n).hom =
      crossProductAssociatorDefect X Y Z (n + 1) := by
    apply chainTrilinearMap_ext X Y Z 1 1 (n + 1)
    intro σ τ υ
    have hstd := crossProductAssociatorHomotopy_boundary_affine 1 1 (n + 1) n
      (formalSimplex (stdVertices 1)) (formalSimplex (stdVertices 1))
      (formalSimplex (stdVertices (n + 1)))
    have hστυ := congrArg (inducedChain (σ.prodMap (τ.prodMap υ)) (n + 3)) hstd
    simpa only [integerTrilinearPostcompose_apply, integerTrilinearPrecompose_apply,
      LinearMap.add_apply, LinearMap.id_apply, map_add, inducedChain_boundary,
      crossProductAssociatorHomotopy_natural, crossProductAssociatorDefect_natural,
      affineChainMap_stdVertices, inducedChain_simplex, ContinuousMap.comp_id] using hστυ
  exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun heq a) b) c

/-- A cycle in the third factor makes the associator defect an explicit actual boundary. -/
theorem crossProductAssociatorHomotopy_boundary_of_cycle (n : ℕ)
    (a : Chains X 1) (b : Chains Y 1) (c : Chains Z n)
    (hc : ((singularComplex Z).d n (n - 1)).hom c = 0) :
    ((singularComplex (X × (Y × Z))).d (n + 3) (n + 2)).hom
        (crossProductAssociatorHomotopy X Y Z n a b c) =
      crossProductAssociatorDefect X Y Z n a b c := by
  cases n with
  | zero => exact crossProductAssociatorHomotopy_boundary_zero a b c
  | succ n =>
      have hc' : ((singularComplex Z).d (n + 1) n).hom c = 0 := by
        simpa only [Nat.succ_sub_one] using hc
      simpa only [hc', map_zero, add_zero] using
        crossProductAssociatorHomotopy_boundary n a b c

/-- The explicit actual chain witnessing associativity modulo boundaries. -/
theorem crossProduct_associativity_boundary (n : ℕ)
    (a : Chains X 1) (b : Chains Y 1) (c : Chains Z n)
    (hc : ((singularComplex Z).d n (n - 1)).hom c = 0) :
    inducedChain (Homeomorph.prodAssoc X Y Z : C(_, _)) (n + 2)
          (crossProductTriangle (X × Y) Z n (crossProductEdge X Y 1 a b) c) -
        crossProductEdge X (Y × Z) (n + 1) a (crossProductEdge Y Z n b c) =
      ((singularComplex (X × (Y × Z))).d (n + 3) (n + 2)).hom
        (crossProductAssociatorHomotopy X Y Z n a b c) :=
  (crossProductAssociatorHomotopy_boundary_of_cycle n a b c hc).symm

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
