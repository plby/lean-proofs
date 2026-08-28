import Wikipedia.SmoothSixDPoincare.LinearSphereEquiv
import Wikipedia.SmoothSixDPoincare.SphereOutwardClass
import Wikipedia.SmoothSixDPoincare.OnePointCollapseHomology
import Wikipedia.HopfProblem.SphereHomologyTop

/-!
# Integer markings compatible with the constructed signed-count formula

The source marking uses the global outward class. The target marking uses
the actual compactification connecting map and the same normalized linear
model. A signed-count formula therefore becomes literal multiplication on
integer top homology. Surjectivity then forces the count to be a unit.
-/

noncomputable section

open Set Metric ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.SpherePoint

open Wikipedia.HopfProblem.SphereHomology
  Wikipedia.HopfProblem.SingularMayerVietoris

variable (n : ℕ) {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N]
  [FiniteDimensional ℝ N]
  (j : (ℝ × N) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
  (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] N)

def sourceCountMark : SingularHomology (UnitSphere (n + 2)) (n + 2) ≃ₗ[ℤ] ℤ :=
  (outwardClassEquiv n j B n).trans (unitSphereHomologyTopEquiv n)

def overlapCountMark : SingularHomology (sphere (0 : N) 1) (n + 1) ≃ₗ[ℤ] ℤ :=
  (LinearSphereAction.homologyEquiv B (n + 1)).symm.trans (unitSphereHomologyTopEquiv n)

def targetCountMark : SingularHomology (OnePoint N) (n + 2) ≃ₗ[ℤ] ℤ :=
  (OnePointCover.sphereHomologyEquiv 1 zero_lt_one n).trans (overlapCountMark n B)

omit [FiniteDimensional ℝ N] in
theorem overlapCountMark_linear (a : SingularHomology (UnitSphere (n + 1)) (n + 1)) :
    overlapCountMark n B
      (singularHomologyMap (LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective)
        (n + 1) a) = unitSphereHomologyTopEquiv n a := by
  rw [← LinearSphereAction.homologyEquiv_apply]
  change unitSphereHomologyTopEquiv n
    ((LinearSphereAction.homologyEquiv B (n + 1)).symm
      (LinearSphereAction.homologyEquiv B (n + 1) a)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem countMark_of_connecting
    (u : SingularHomology (OnePoint N) (n + 2))
    (a : SingularHomology (UnitSphere (n + 2)) (n + 2)) (c : ℤ)
    (h : OnePointCover.sphereConnecting 1 zero_lt_one (n + 1) u =
      c • singularHomologyMap
        (LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective)
          (n + 1) (outwardClass n j B n a)) :
    targetCountMark n B u = c * sourceCountMark n j B a := by
  have h' := congrArg (overlapCountMark n B) h
  rw [map_zsmul, overlapCountMark_linear] at h'
  exact h'

theorem count_natAbs_one_of_surjective
    (f : SingularHomology (UnitSphere (n + 2)) (n + 2) →ₗ[ℤ]
      SingularHomology (OnePoint N) (n + 2)) (c : ℤ)
    (hc : ∀ a, targetCountMark n B (f a) = c * sourceCountMark n j B a)
    (hs : Function.Surjective f) : c.natAbs = 1 := by
  obtain ⟨a, ha⟩ := hs ((targetCountMark n B).symm 1)
  have h := hc a
  rw [ha, LinearEquiv.apply_symm_apply] at h
  exact Int.isUnit_iff_natAbs_eq.mp (IsUnit.of_mul_eq_one _ h.symm)

end Wikipedia.SmoothSixDPoincare.SpherePoint
