import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Tactic.FieldSimp

/-!
# A scalar vanishing lemma for holomorphic vector fields on the sphere

An entire coefficient in each affine chart, related by the derivative of
inversion, vanishes if the field vanishes at zero, one, and infinity.  The
proof removes the zero at the origin by divided differences, bounds the
result using both affine charts, and applies Liouville's theorem.
-/

noncomputable section

open Set Metric Bornology
open scoped Topology

namespace Wikipedia.HopfProblem.RiemannSphere.HolomorphicVectorFields

private theorem scalar_differentiable_dslope {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) : Differentiable ℂ (dslope f 0) := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope (by simp)).2 hf.differentiableOn

private theorem scalar_dslope_transition {A B : ℂ → ℂ}
    (htransition : ∀ w : ℂ, w ≠ 0 → B w = -(w ^ 2) * A w⁻¹)
    (hA0 : A 0 = 0) (hB0 : B 0 = 0) {z : ℂ} (hz : z ≠ 0) :
    dslope A 0 z = -dslope B 0 z⁻¹ := by
  rw [dslope_of_ne _ hz, dslope_of_ne _ (inv_ne_zero hz)]
  simp only [slope, vsub_eq_sub, sub_zero, hA0, hB0, smul_eq_mul, inv_inv]
  rw [htransition z⁻¹ (inv_ne_zero hz)]
  simp only [inv_inv]
  field_simp [hz]

/-- An entire two-chart vector-field coefficient that vanishes at zero,
one, and infinity is identically zero in both charts. -/
theorem scalar_field_eq_zero {A B : ℂ → ℂ}
    (hA : Differentiable ℂ A) (hB : Differentiable ℂ B)
    (htransition : ∀ w : ℂ, w ≠ 0 → B w = -(w ^ 2) * A w⁻¹)
    (hA0 : A 0 = 0) (hA1 : A 1 = 0) (hB0 : B 0 = 0) :
    A = 0 ∧ B = 0 := by
  have hQA := scalar_differentiable_dslope hA
  have hQB := scalar_differentiable_dslope hB
  obtain ⟨MA, hMA⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    hQA.continuous.continuousOn
  obtain ⟨MB, hMB⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    hQB.continuous.continuousOn
  have hbound : IsBounded (range (dslope A 0)) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨max MA MB, ?_⟩
    rintro _ ⟨z, rfl⟩
    by_cases hz : ‖z‖ ≤ 1
    · exact (hMA z (by simpa using hz)).trans (le_max_left _ _)
    · have hz0 : z ≠ 0 := by
        intro heq
        simp [heq] at hz
      rw [scalar_dslope_transition htransition hA0 hB0 hz0, norm_neg]
      apply (hMB z⁻¹ ?_).trans (le_max_right _ _)
      rw [mem_closedBall_zero_iff, norm_inv]
      exact inv_le_one_of_one_le₀ (le_of_lt (lt_of_not_ge hz))
  have hQzero (z : ℂ) : dslope A 0 z = 0 := by
    rw [hQA.apply_eq_apply_of_bounded hbound z 1, dslope_of_ne _ one_ne_zero]
    simp [slope, hA0, hA1]
  have hAzero : A = 0 := by
    funext z
    have hfactor := sub_smul_dslope A 0 z
    simpa [hQzero, hA0] using hfactor.symm
  refine ⟨hAzero, ?_⟩
  funext w
  by_cases hw : w = 0
  · simpa [hw] using hB0
  · simp [htransition w hw, hAzero]

end Wikipedia.HopfProblem.RiemannSphere.HolomorphicVectorFields
