import Wikipedia.SmoothSixDPoincare.DiskTubularNeighborhood
import Wikipedia.SmoothSixDPoincare.MorseCompactStability
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# An inner-product ball surrounding the entire embedded disk

An open tubular neighborhood of the closed unit disk contains a slightly
longer, sufficiently thin ellipsoid. Linear normal rescaling identifies it
with an inner-product ball of radius strictly greater than one, without
changing any point of the disk's coordinate plane.
-/

noncomputable section

open Set Metric Function
open scoped Topology ContDiff Manifold
open Wikipedia.SmoothSixDPoincare.MorsePerturbation

namespace Wikipedia.HopfProblem.DegreeCollapse.DiskShrinking

variable {D Z : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]
  [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
  [FiniteDimensional ℝ Z]

theorem exists_larger_closedBall_subset {U : Set D} (hU : IsOpen U)
    (hunit : closedBall (0 : D) 1 ⊆ U) :
    ∃ R : ℝ, 1 < R ∧ closedBall (0 : D) R ⊆ U := by
  let T : Set ℝ := {r | ∀ x ∈ closedBall (0 : D) 1, r • x ∈ U}
  have hT : IsOpen T := isOpen_forall_mem_compact (isCompact_closedBall (0 : D) 1)
    (hU.preimage (continuous_fst.smul continuous_snd))
  have h1 : (1 : ℝ) ∈ T := by
    intro x hx
    simpa only [one_smul] using hunit hx
  obtain ⟨δ, hδ, hδT⟩ := Metric.mem_nhds_iff.mp (hT.mem_nhds h1)
  let R : ℝ := 1 + δ / 2
  have hR : 1 < R := by dsimp [R]; linarith
  have hRpos : 0 < R := zero_lt_one.trans hR
  have hRT : R ∈ T := hδT (by
    rw [mem_ball, Real.dist_eq, abs_of_nonneg (by dsimp [R]; linarith)]
    dsimp [R]
    linarith)
  refine ⟨R, hR, ?_⟩
  intro x hx
  have hnorm : ‖R⁻¹ • x‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hRpos)]
    exact (inv_mul_le_iff₀ hRpos).mpr (by
      simpa only [mul_one] using mem_closedBall_zero_iff.mp hx)
  have hh := hRT (R⁻¹ • x) (mem_closedBall_zero_iff.mpr hnorm)
  simpa only [smul_inv_smul₀ hRpos.ne'] using hh

theorem exists_disk_ellipsoid_in_open {U : Set (D × Z)} (hU : IsOpen U)
    (hzero : closedBall (0 : D) 1 ×ˢ {(0 : Z)} ⊆ U) :
    ∃ R : ℝ, 1 < R ∧ ∃ L : WithLp 2 (D × Z) ≃L[ℝ] D × Z,
      (∀ x : D, L (WithLp.toLp 2 (x, (0 : Z))) = (x, 0)) ∧
      MapsTo L (closedBall 0 R) U := by
  obtain ⟨A, B, hA, hB, hKA, h0B, hAB⟩ :=
    generalized_tube_lemma (isCompact_closedBall (0 : D) 1)
      (isCompact_singleton (x := (0 : Z))) hU hzero
  obtain ⟨R, hR, hRA⟩ := exists_larger_closedBall_subset hA hKA
  obtain ⟨ε, hε, hεB⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (hB.mem_nhds (h0B (mem_singleton (0 : Z))))
  have hRpos : 0 < R := zero_lt_one.trans hR
  let δ : ℝ := ε / R
  have hδ : 0 < δ := div_pos hε hRpos
  let T : Z ≃L[ℝ] Z := (LinearEquiv.smulOfNeZero ℝ Z δ hδ.ne').toContinuousLinearEquiv
  let L : WithLp 2 (D × Z) ≃L[ℝ] D × Z :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ D Z).trans
      ((ContinuousLinearEquiv.refl ℝ D).prodCongr T)
  have hL (p : WithLp 2 (D × Z)) : L p = (p.fst, δ • p.snd) := rfl
  refine ⟨R, hR, L, ?_, ?_⟩
  · intro x
    rw [hL]
    change (x, δ • (0 : Z)) = (x, 0)
    rw [smul_zero]
  · intro p hp
    rw [hL]
    apply hAB
    refine ⟨hRA (mem_closedBall_zero_iff.mpr
      ((WithLp.norm_fst_le D p).trans (mem_closedBall_zero_iff.mp hp))), hεB ?_⟩
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
    calc
      δ * ‖p.snd‖ ≤ δ * R := mul_le_mul_of_nonneg_left
        ((WithLp.norm_snd_le D p).trans (mem_closedBall_zero_iff.mp hp)) hδ.le
      _ = ε := div_mul_cancel₀ ε hRpos.ne'

end Wikipedia.HopfProblem.DegreeCollapse.DiskShrinking
