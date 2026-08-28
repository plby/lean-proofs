import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologyDual
import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluationSingular
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Native cohomology coordinates from proved homology coordinates

Finite free coordinates on actual singular homology supply projectivity
in every degree.  The proved evaluation isomorphism of the actual
singular cochain complex then gives its cohomology coordinates.  The
construction does not define cohomology to be a homology dual.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open SingularMayerVietoris SingularCohomologyFree

variable (X : Type) [TopologicalSpace X] (r : ℕ → ℕ)
  (e : ∀ n : ℕ, SingularHomology X n ≃ₗ[ℤ] (Fin (r n) → ℤ))

/-- The projectivity needed by native evaluation follows from the given
actual homology coordinates, rather than being an extra hypothesis. -/
def cohomologyCoordinatesOfHomology (n : ℕ) :
    SingularCohomology X n ≃ₗ[ℤ] (Fin (r n) → ℤ) := by
  letI (k : ℕ) : Module.Projective ℤ (SingularHomology X k) :=
    Module.Projective.of_basis ((Pi.basisFun ℤ (Fin (r k))).map (e k).symm)
  exact (singularEvaluationEquiv X n).trans (intDualCoordinatesOfEquiv (e n))

@[simp] theorem cohomologyCoordinatesOfHomology_apply (n : ℕ)
    (a : SingularCohomology X n) :
    cohomologyCoordinatesOfHomology X r e n a =
      intDualCoordinatesOfEquiv (e n) (singularEvaluation X n a) := rfl

theorem cohomologyCoordinatesOfHomology_apply_coordinate (n : ℕ)
    (a : SingularCohomology X n) (i : Fin (r n)) :
    cohomologyCoordinatesOfHomology X r e n a i =
      singularEvaluation X n a ((e n).symm (Pi.single i 1)) := by
  rw [cohomologyCoordinatesOfHomology_apply, intDualCoordinatesOfEquiv_apply]

/-- The actual evaluation pairing is the dot product in the displayed coordinates. -/
theorem cohomologyCoordinatesOfHomology_evaluate (n : ℕ)
    (a : SingularCohomology X n) (b : SingularHomology X n) :
    singularEvaluation X n a b =
      ∑ i, cohomologyCoordinatesOfHomology X r e n a i * e n b i := by
  simp only [cohomologyCoordinatesOfHomology_apply]
  exact intDualCoordinatesOfEquiv_evaluate (e n) (singularEvaluation X n a) b

section Consequences

include e

theorem cohomology_free_of_homology_coordinates (n : ℕ) :
    Module.Free ℤ (SingularCohomology X n) :=
  Module.Free.of_equiv (cohomologyCoordinatesOfHomology X r e n).symm

theorem cohomology_finite_of_homology_coordinates (n : ℕ) :
    Module.Finite ℤ (SingularCohomology X n) :=
  Module.Finite.of_surjective (cohomologyCoordinatesOfHomology X r e n).symm.toLinearMap
    (cohomologyCoordinatesOfHomology X r e n).symm.surjective

theorem cohomology_torsionFree_of_homology_coordinates (n : ℕ) :
    Module.IsTorsionFree ℤ (SingularCohomology X n) := by
  let := cohomology_free_of_homology_coordinates X r e n
  infer_instance

theorem cohomology_finrank_of_homology_coordinates (n : ℕ) :
    Module.finrank ℤ (SingularCohomology X n) = r n := by
  rw [(cohomologyCoordinatesOfHomology X r e n).finrank_eq]
  exact Module.finrank_fin_fun ℤ

theorem cohomology_subsingleton_of_homology_coordinates (n : ℕ) (hr : r n = 0) :
    Subsingleton (SingularCohomology X n) := by
  refine ⟨fun a b => ?_⟩
  apply (cohomologyCoordinatesOfHomology X r e n).injective
  ext i
  exact Fin.elim0 (Fin.cast hr i)

end Consequences

section Naturality

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  (r : ℕ → ℕ)
  (eX : ∀ n : ℕ, SingularHomology X n ≃ₗ[ℤ] (Fin (r n) → ℤ))
  (eY : ∀ n : ℕ, SingularHomology Y n ≃ₗ[ℤ] (Fin (r n) → ℤ))

/-- If the actual homology map preserves coordinates, its actual
cohomological pullback preserves the dual coordinates. -/
theorem cohomologyCoordinatesOfHomology_naturality (f : C(X, Y)) (n : ℕ)
    (hf : ∀ b : SingularHomology X n, eY n (singularHomologyMap f n b) = eX n b)
    (a : SingularCohomology Y n) :
    cohomologyCoordinatesOfHomology X r eX n (singularCohomologyPullback f n a) =
      cohomologyCoordinatesOfHomology Y r eY n a := by
  ext i
  have hb : singularHomologyMap f n ((eX n).symm (Pi.single i 1)) =
      (eY n).symm (Pi.single i 1) := by
    apply (eY n).injective
    rw [hf, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  simp only [cohomologyCoordinatesOfHomology_apply_coordinate,
    singularEvaluation_naturality, hb]

end Naturality

end Wikipedia.HopfProblem.Elliptic.HigherHomology
