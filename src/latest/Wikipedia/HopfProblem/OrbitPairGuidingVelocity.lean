import Wikipedia.HopfProblem.OrbitPairTrackCrossingDifferential
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Small source velocities transverse to the other projected branch

A synchronized regular collision forces the two projected tangent images
to span the target. Since the full source has smaller dimension than the
target, the first tangent image cannot lie in the second one. Arbitrarily
small spatial changes of the first time direction therefore move it outside
the second tangent image. This uses source velocities, without changing
either projected tangent image.
-/

noncomputable section

open Set Function

namespace Wikipedia.HopfProblem.OrbitPair.GuidingVelocity

variable {E G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem exists_small_velocity_outside (A : ℝ × E →L[ℝ] G) (W : Submodule ℝ G)
    (hout : ∃ u : ℝ × E, A u ∉ W) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : E, ‖a‖ < ε ∧ A (1, a) ∉ W := by
  by_cases htime : A (1, 0) ∈ W
  · have hv : ∃ v : E, A (0, v) ∉ W := by
      by_contra! h
      obtain ⟨u, hu⟩ := hout
      apply hu
      have heq : u = u.1 • (1, 0) + (0, u.2) := by ext <;> simp
      rw [heq, map_add, map_smul]
      exact W.add_mem (W.smul_mem u.1 htime) (h u.2)
    obtain ⟨v, hv⟩ := hv
    let c : ℝ := ε / (2 * (‖v‖ + 1))
    have hden : 0 < 2 * (‖v‖ + 1) := by positivity
    have hc : 0 < c := div_pos hε hden
    have hceq : c * (2 * (‖v‖ + 1)) = ε :=
      div_mul_cancel₀ ε (ne_of_gt hden)
    refine ⟨c • v, ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
      nlinarith [norm_nonneg v]
    · intro ha
      have heq : ((1 : ℝ), c • v) = (1, 0) + c • (0, v) := by ext <;> simp
      rw [heq, map_add, map_smul] at ha
      exact hv ((W.smul_mem_iff (ne_of_gt hc)).mp
        ((W.add_mem_iff_right htime).mp ha))
  · exact ⟨0, by simpa using hε, htime⟩

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ G]

theorem exists_small_velocity_transverse (A B : ℝ × E →L[ℝ] G)
    (hregular : Surjective
      (B.comp SynchronizedPairs.secondLinear - A.comp SynchronizedPairs.firstLinear))
    (hdim : Module.finrank ℝ (ℝ × E) < Module.finrank ℝ G)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : E, ‖a‖ < ε ∧ A (1, a) ∉ LinearMap.range B.toLinearMap := by
  apply exists_small_velocity_outside A (LinearMap.range B.toLinearMap) _ hε
  by_contra! h
  have hsurj : Surjective B := by
    intro z
    obtain ⟨u, hu⟩ := hregular z
    change B (u.1, u.2.2) - A (u.1, u.2.1) = z at hu
    obtain ⟨v, hv⟩ := h (u.1, u.2.1)
    change B v = A (u.1, u.2.1) at hv
    refine ⟨(u.1, u.2.2) - v, ?_⟩
    rw [map_sub, hv]
    exact hu
  exact (not_le_of_gt hdim) (LinearMap.finrank_le_finrank_of_surjective hsurj)

theorem injective_curve_branch_difference (B : ℝ × E →L[ℝ] G)
    (hB : Injective B) {w : G} (hw : w ∉ LinearMap.range B.toLinearMap) :
    Injective ((B.comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × E))) -
      (ContinuousLinearMap.fst ℝ ℝ (ℝ × E)).smulRight w) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro q hq
  have heq : B q.2 = q.1 • w := sub_eq_zero.mp hq
  have ht : q.1 = 0 := by
    by_contra ht
    apply hw
    exact ((LinearMap.range B.toLinearMap).smul_mem_iff ht).mp ⟨q.2, heq⟩
  have hv : q.2 = 0 := (injective_iff_map_eq_zero B).mp hB q.2 (by simpa [ht] using heq)
  exact Prod.ext ht hv

end Wikipedia.HopfProblem.OrbitPair.GuidingVelocity
