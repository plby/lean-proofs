import Wikipedia.HopfProblem.SpecialPeriodsThreefoldFiniteActionFixedLocus
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFixedSphere
import Mathlib.Topology.Compactification.OnePoint.Sphere

/-!
# The literal finite-subgroup fixed set is a two-sphere

The equality of fixed subsets identifies the native fixed set with the
already constructed double curve, with its actual subspace topology.
Its original Riemann-sphere parametrization then gives a homeomorphism
to the usual unit two-sphere in real Euclidean three-space. No recognition
theorem for the ambient threefold or Smith fixed-point theorem is used.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.FiniteActionFixed

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold
  Threefold.space_t2Space

/-- The original Riemann sphere parametrizes the literal subgroup fixed
set, using only the proved equality of the two actual subsets. -/
def rootsOfUnityFixedHomeomorph (n : ℕ) (hn : 2 ≤ n) :
    letI := VerticalAction.action
    RiemannSphere ≃ₜ MulAction.fixedPoints (rootsOfUnity n ℂ) Space := by
  let := VerticalAction.action
  let := VerticalAction.D₀_chartedSpace
  exact VerticalAction.D₀_biholomorph.toHomeomorph.trans
    (Homeomorph.setCongr (rootsOfUnity_fixedPoints_eq_D₀ n hn).symm)

/-- The homeomorphism retains the actual ambient cusp-curve
parametrization, rather than introducing a replacement sphere. -/
theorem rootsOfUnityFixedHomeomorph_apply (n : ℕ) (hn : 2 ≤ n) (z : RiemannSphere) :
    letI := VerticalAction.action
    (rootsOfUnityFixedHomeomorph n hn z : Space) =
      CuspGeometry.doubleCurveParametrization 1 z := by
  let := VerticalAction.action
  let := VerticalAction.D₀_chartedSpace
  exact VerticalAction.D₀_biholomorph_val z

/-- Remark 9.25's `S²` is the literal standard Euclidean unit sphere. -/
def rootsOfUnityFixedSphereHomeomorph (n : ℕ) (hn : 2 ≤ n) :
    letI := VerticalAction.action
    MulAction.fixedPoints (rootsOfUnity n ℂ) Space ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  let := VerticalAction.action
  exact (rootsOfUnityFixedHomeomorph n hn).symm.trans
    (onePointEquivSphereOfFinrankEq (V := ℂ) (ι := Fin 3) (by simp))

theorem rootsOfUnity_fixedPoints_isClosed (n : ℕ) (hn : 2 ≤ n) :
    letI := VerticalAction.action
    IsClosed (MulAction.fixedPoints (rootsOfUnity n ℂ) Space) := by
  let := VerticalAction.action
  rw [rootsOfUnity_fixedPoints_eq_D₀ n hn]
  exact VerticalAction.D₀_isClosed

theorem rootsOfUnity_fixedPoints_isCompact (n : ℕ) (hn : 2 ≤ n) :
    letI := VerticalAction.action
    IsCompact (MulAction.fixedPoints (rootsOfUnity n ℂ) Space) := by
  let := VerticalAction.action
  rw [rootsOfUnity_fixedPoints_eq_D₀ n hn]
  exact VerticalAction.D₀_isCompact

/-- Both original triple points belong to every finite subgroup fixed set. -/
theorem tripleStratum_subset_rootsOfUnity_fixedPoints (n : ℕ) (hn : 2 ≤ n) :
    letI := VerticalAction.action
    CuspGeometry.tripleStratum ⊆ MulAction.fixedPoints (rootsOfUnity n ℂ) Space := by
  let := VerticalAction.action
  rw [rootsOfUnity_fixedPoints_eq_D₀ n hn]
  exact VerticalAction.tripleStratum_subset_D₀

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.FiniteActionFixed
