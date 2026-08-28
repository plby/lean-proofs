import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryCriticalGenerator
import Wikipedia.HomotopyGroupsOfSpheres.UnitaryCompactLogarithm
import Wikipedia.NoExoticSixSphere.OrthogonalExponentialPolygon

/-! # Small exponential increments realize the original constrained exponential polygon -/

noncomputable section

open scoped Matrix.Norms.Frobenius
open Set

namespace Wikipedia.HomotopyGroupsOfSpheres

namespace ComplexSkewMatrices

variable {N : Type*} [Fintype N] [DecidableEq N]

def imaginaryDirection : RealSymmetricMixing.DirectionSpace N →ₗ[ℝ] Space N :=
  (ImaginarySymmetricMatrices.directionMap (N := N)).codRestrict
    (skewAdjoint.submodule ℝ (Matrix N N ℂ))
    (fun A ↦ (ImaginarySymmetricMatrices.imaginary_relations A).2.1)

theorem imaginaryDirection_toOrthogonal (A : RealSymmetricMixing.DirectionSpace N) :
    toOrthogonalSkew (imaginaryDirection A) = ComplexMatrixRealRepresentation.skewMap A := rfl

end ComplexSkewMatrices

namespace QuaternionicSymmetricMatrices

open RealSymmetricMixing ComplexSkewMatrices ComplexMatrixRealRepresentation

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem exponentialCurve_unitary (A : DirectionSpace N) (t : ℝ) :
    (exponentialCurve A t).val.val =
      ComplexSkewMatrices.exponential (t • imaginaryDirection A) := by
  apply Subtype.ext
  exact congrArg NormedSpace.exp (ImaginarySymmetricMatrices.imaginary.map_smul t A.val)

theorem relative_exponentialCurve (A : DirectionSpace N) (s t : ℝ) :
    ShortLog.relative (exponentialCurve A s) (exponentialCurve A t) =
      ComplexSkewMatrices.exponential ((t - s) • imaginaryDirection A) := by
  apply mul_left_cancel (a := (exponentialCurve A s).val.val)
  rw [ShortLog.relative, mul_inv_cancel_left, exponentialCurve_unitary,
    exponentialCurve_unitary, ← ComplexSkewMatrices.exponential_add_smul]
  congr 2
  ring

namespace Polygon

open VertexSpace

variable {m : ℕ}

def exponentialVertices (τ : Fin (m + 2) → ℝ) (A : DirectionSpace N) : VertexSpace.Space N m :=
  fun j ↦ exponentialCurve A (τ j.castSucc.succ)

theorem vertices_exponentialVertices (b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (A : DirectionSpace N) (hend : QuaternionicSymmetricMatrices.exponential A = b)
    (j : Fin (m + 2)) :
    vertices specialIdentity b (exponentialVertices τ A) j = exponentialCurve A (τ j) := by
  induction j using Fin.cases with
  | zero => rw [vertices_zero, hzero, exponentialCurve_zero]
  | succ j =>
    induction j using Fin.lastCases with
    | last =>
      change vertices specialIdentity b (exponentialVertices τ A) (Fin.last (m + 1)) =
        exponentialCurve A (τ (Fin.last (m + 1)))
      rw [vertices_last, hone, exponentialCurve, one_smul, hend]
    | cast j => rw [vertices_interior]; rfl

theorem forget_exponentialVertices (τ : Fin (m + 2) → ℝ) (A : DirectionSpace N) :
    forget (exponentialVertices τ A) =
      NoExoticSixSphere.OrthogonalPolygon.exponentialVertices 1 τ (skewMap A) := by
  funext j
  change specialOrthogonal (exponentialCurve A (τ j.castSucc.succ)) =
    1 * NoExoticSixSphere.OrthogonalExponential.exp (τ j.castSucc.succ • skewMap A)
  rw [one_mul, specialOrthogonal_curve]

variable (b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (A : DirectionSpace N) (hend : QuaternionicSymmetricMatrices.exponential A = b)
    (hsmall : ∀ i : Fin (m + 1),
      ‖(τ i.succ - τ i.castSucc) • imaginaryDirection A‖ < CompatibleLog.radius N)

include hzero hone hend hsmall

theorem exponentialVertices_admissible :
    exponentialVertices τ A ∈ admissible specialIdentity b m := by
  intro i
  change ShortLog.relative (vertices specialIdentity b (exponentialVertices τ A) i.castSucc)
    (vertices specialIdentity b (exponentialVertices τ A) i.succ) ∈ CompatibleLog.domain N
  rw [vertices_exponentialVertices b τ hzero hone A hend,
    vertices_exponentialVertices b τ hzero hone A hend, relative_exponentialCurve]
  exact CompatibleLog.exponential_mem_domain _ (hsmall i)

theorem generator_exponentialVertices (i : Fin (m + 1)) :
    generator specialIdentity b (exponentialVertices τ A) i =
      (τ i.succ - τ i.castSucc) • imaginaryDirection A := by
  change logarithm (ShortLog.relative
    (vertices specialIdentity b (exponentialVertices τ A) i.castSucc)
    (vertices specialIdentity b (exponentialVertices τ A) i.succ)) = _
  rw [vertices_exponentialVertices b τ hzero hone A hend,
    vertices_exponentialVertices b τ hzero hone A hend, relative_exponentialCurve]
  exact logarithm_exponential _
    (ComplexMatrixLocalLogarithm.mem_safeSource_of_norm_lt _
      ((hsmall i).trans CompatibleLog.radius_lt)).1

theorem path_exponentialVertices (hτ : StrictMono τ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    path specialIdentity b τ hτ (exponentialVertices τ A)
      (exponentialVertices_admissible b τ hzero hone A hend hsmall) t = exponentialCurve A t := by
  have hendO : (1 : NoExoticSixSphere.GLOrthonormalization.OrthogonalOperators
      (2 * Fintype.card N)) * NoExoticSixSphere.OrthogonalExponential.exp (skewMap A) =
        specialOrthogonal b := by rw [one_mul, ← specialOrthogonal_exponential, hend]
  have htarget (i : Fin (m + 1)) : (τ i.succ - τ i.castSucc) • skewMap A ∈
      (NoExoticSixSphere.OrthogonalExponential.logarithmChart (2 * Fintype.card N)).target := by
    have h := CompatibleLog.radius_closedBall (N := N)
      (show (τ i.succ - τ i.castSucc) • imaginaryDirection A ∈
        Metric.closedBall 0 (CompatibleLog.radius N) by
          simpa only [Metric.mem_closedBall, dist_zero_right] using (hsmall i).le)
    simpa only [map_smul, imaginaryDirection_toOrthogonal] using h.2.1
  apply Subtype.ext
  apply Subtype.ext
  apply orthogonal_injective
  change specialOrthogonal (path specialIdentity b τ hτ _ _ t) =
    specialOrthogonal (exponentialCurve A t)
  rw [path_orthogonal, forget_exponentialVertices, specialOrthogonal_curve]
  have h := NoExoticSixSphere.OrthogonalPolygon.path_exponentialVertices
    1 (specialOrthogonal b) τ hτ hzero hone (skewMap A) hendO htarget ht
  have hId : specialOrthogonal (specialIdentity (N := N)) = 1 := orthogonal.map_one
  simpa only [hId, one_mul] using h

theorem energy_exponentialVertices (hτ : StrictMono τ) :
    energy specialIdentity b τ (exponentialVertices τ A) =
      2 * RealMatrixSquareNorm.squareNorm A.val :=
  energy_eq_squareNorm_of_exponential b τ hτ hzero hone (exponentialVertices τ A)
    (exponentialVertices_admissible b τ hzero hone A hend hsmall) A
    (fun _ ht ↦ path_exponentialVertices b τ hzero hone A hend hsmall hτ ht)

end Polygon
end QuaternionicSymmetricMatrices
end Wikipedia.HomotopyGroupsOfSpheres
