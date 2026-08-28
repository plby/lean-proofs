import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryRefinedWangCover
import Wikipedia.HopfProblem.MappingTorusHomology
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleMayerVietorisNaturality

/-!
# Actual Wang coordinates for the refined mapping-torus cover

The genuine smaller interval cover has an actual two-component intersection
homotopy equivalence. Its retraction commutes with the literal inclusion in
the original intersection. Naturality of the actual singular connecting map
under this identity refinement therefore identifies its coordinates with
the original signed Wang pair, in every degree. The quarter-time maps give
the two actual homology summands.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.RefinedWang

open SingularMayerVietoris PeriodTorusHigherHomology

variable {X : Type} [TopologicalSpace X] (φ : X ≃ₜ X)

/-- The actual homology marking of the refined two-component intersection. -/
def intersectionHomologyEquiv (n : ℕ) :
    SingularHomology (U φ ∩ V φ : Set (MappingTorus.Torus φ)) n ≃ₗ[ℤ]
      (SingularHomology X n × SingularHomology X n) :=
  (homotopyEquivHomologyEquiv (intersectionHomotopyEquiv φ) n).trans
    (sumHomologyEquiv X X n)

@[simp] theorem intersectionHomologyEquiv_apply (n : ℕ)
    (a : SingularHomology (U φ ∩ V φ : Set (MappingTorus.Torus φ)) n) :
    intersectionHomologyEquiv φ n a = sumHomologyEquiv X X n
      (singularHomologyMap (intersectionHomotopyEquiv φ).toFun n a) := rfl

/-- The literal intersection inclusion preserves both actual fibre coordinates. -/
theorem intersectionHomologyEquiv_inclusion (n : ℕ)
    (a : SingularHomology (U φ ∩ V φ : Set (MappingTorus.Torus φ)) n) :
    MappingTorusHomology.intersectionHomologyEquiv φ n
        (singularHomologyMap (intersectionInclusion φ) n a) =
      intersectionHomologyEquiv φ n a := by
  rw [MappingTorusHomology.intersectionHomologyEquiv_apply, intersectionHomologyEquiv_apply]
  have h := congrArg (fun f => singularHomologyMap f n)
    (intersectionHomotopyEquiv_inclusion φ)
  rw [singularHomologyMap_comp] at h
  exact congrArg (sumHomologyEquiv X X n) (LinearMap.congr_fun h a)

/-- The refinement map is exactly the restriction of the ambient identity map. -/
theorem intersectionInclusion_eq_intersectionRestriction :
    intersectionInclusion φ = intersectionRestriction (ContinuousMap.id (MappingTorus.Torus φ))
      (U φ) (V φ) (MappingTorus.HomologyCover.U φ) (MappingTorus.HomologyCover.V φ)
      (U_subset φ) (V_subset φ) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  rfl

/-- The genuine connecting map for the proved refined open cover. -/
abbrev mayerVietorisConnecting (n : ℕ) :
    SingularHomology (MappingTorus.Torus φ) (n + 1) →ₗ[ℤ]
      SingularHomology (U φ ∩ V φ : Set (MappingTorus.Torus φ)) n :=
  connectingHomomorphism (U φ) (V φ) (U_open φ) (V_open φ) (cover φ) n

/-- Actual connecting naturality for the ambient identity and literal cover refinement. -/
theorem mayerVietorisConnecting_refinement (n : ℕ)
    (a : SingularHomology (MappingTorus.Torus φ) (n + 1)) :
    singularHomologyMap (intersectionInclusion φ) n (mayerVietorisConnecting φ n a) =
      MappingTorusHomology.mayerVietorisConnecting φ n a := by
  have h := connectingHomomorphism_naturality_apply
    (ContinuousMap.id (MappingTorus.Torus φ)) (U φ) (V φ)
    (MappingTorus.HomologyCover.U φ) (MappingTorus.HomologyCover.V φ)
    (U_subset φ) (V_subset φ) (U_open φ) (V_open φ) (cover φ)
    (MappingTorus.HomologyCover.U_open φ) (MappingTorus.HomologyCover.V_open φ)
    (MappingTorus.HomologyCover.cover φ) n a
  rw [← intersectionInclusion_eq_intersectionRestriction,
    singularHomologyMap_id, LinearMap.id_apply] at h
  exact h

/-- The two actual component coordinates of the refined connecting map. -/
def boundaryCoordinates (n : ℕ) :
    SingularHomology (MappingTorus.Torus φ) (n + 1) →ₗ[ℤ]
      (SingularHomology X n × SingularHomology X n) :=
  (intersectionHomologyEquiv φ n).toLinearMap.comp (mayerVietorisConnecting φ n)

@[simp] theorem boundaryCoordinates_apply (n : ℕ)
    (a : SingularHomology (MappingTorus.Torus φ) (n + 1)) :
    boundaryCoordinates φ n a = intersectionHomologyEquiv φ n
      (mayerVietorisConnecting φ n a) := rfl

/-- Refinement keeps the original connecting coordinates exactly, including their order. -/
theorem boundaryCoordinates_refinement (n : ℕ)
    (a : SingularHomology (MappingTorus.Torus φ) (n + 1)) :
    boundaryCoordinates φ n a = MappingTorusHomology.boundaryCoordinates φ n a := by
  rw [boundaryCoordinates_apply, ← intersectionHomologyEquiv_inclusion,
    mayerVietorisConnecting_refinement]
  rfl

/-- The refined connecting coordinates are the original signed Wang antidiagonal. -/
theorem boundaryCoordinates_eq_antidiagonal (n : ℕ)
    (a : SingularHomology (MappingTorus.Torus φ) (n + 1)) :
    boundaryCoordinates φ n a =
      (-MappingTorusHomology.wangBoundary φ n a, MappingTorusHomology.wangBoundary φ n a) :=
  (boundaryCoordinates_refinement φ n a).trans
    (MappingTorusHomology.boundaryCoordinates_eq_antidiagonal φ n a)

/-- The actual refined connecting value is recovered from its genuine signed Wang pair. -/
theorem mappingTorusConnecting_eq_marked_boundary (n : ℕ)
    (a : SingularHomology (MappingTorus.Torus φ) (n + 1)) :
    mayerVietorisConnecting φ n a = (intersectionHomologyEquiv φ n).symm
      (-MappingTorusHomology.wangBoundary φ n a, MappingTorusHomology.wangBoundary φ n a) := by
  apply (intersectionHomologyEquiv φ n).injective
  rw [LinearEquiv.apply_symm_apply]
  exact boundaryCoordinates_eq_antidiagonal φ n a

/-- The literal quarter-time fibre is the first actual homology summand. -/
@[simp] theorem lowerComponentFibre_homology (n : ℕ) (a : SingularHomology X n) :
    intersectionHomologyEquiv φ n (singularHomologyMap (lowerComponentFibre φ) n a) =
      (a, 0) := by
  rw [intersectionHomologyEquiv_apply, ← LinearMap.comp_apply,
    ← singularHomologyMap_comp, lowerComponentFibre_retraction, sumHomologyEquiv_inl]

/-- The literal three-quarter-time fibre is the second actual homology summand. -/
@[simp] theorem upperComponentFibre_homology (n : ℕ) (a : SingularHomology X n) :
    intersectionHomologyEquiv φ n (singularHomologyMap (upperComponentFibre φ) n a) =
      (0, a) := by
  rw [intersectionHomologyEquiv_apply, ← LinearMap.comp_apply,
    ← singularHomologyMap_comp, upperComponentFibre_retraction, sumHomologyEquiv_inr]

@[simp] theorem intersectionHomologyEquiv_symm_lower (n : ℕ) (a : SingularHomology X n) :
    (intersectionHomologyEquiv φ n).symm (a, 0) =
      singularHomologyMap (lowerComponentFibre φ) n a := by
  apply (intersectionHomologyEquiv φ n).injective
  rw [LinearEquiv.apply_symm_apply, lowerComponentFibre_homology]

@[simp] theorem intersectionHomologyEquiv_symm_upper (n : ℕ) (a : SingularHomology X n) :
    (intersectionHomologyEquiv φ n).symm (0, a) =
      singularHomologyMap (upperComponentFibre φ) n a := by
  apply (intersectionHomologyEquiv φ n).injective
  rw [LinearEquiv.apply_symm_apply, upperComponentFibre_homology]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.RefinedWang
