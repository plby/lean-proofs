import Wikipedia.SmoothSixDPoincare.WhitneyPairModel
import Wikipedia.SmoothSixDPoincare.BumpTranslationDiffeomorph

/-!
# Actual cancellation of the two intersections in the local Whitney model

The nonnegative cutoff translation sends the first sheet strictly above the
second wherever its height can be nonnegative. For sufficiently small positive
model height, the translation is a genuine compactly supported smooth
diffeomorphism. The original pair has exactly two intersections; the moved pair
has none. This is a model result, not construction of a compatible native chart.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.WhitneyPairModel

/-- The explicit endpoint displacement separates every point of the two model sheets. -/
theorem shifted_firstSheet_ne_secondSheet {h : ℝ} (hh : 0 < h) {d : Space → Space}
    (hd : ∀ z, d z = z + cutoff z • moveVector h) (p q : Sheet) :
    d (firstSheet p) ≠ secondSheet h q := by
  intro heq
  have he : firstSheet p + cutoff (firstSheet p) • moveVector h = secondSheet h q :=
    (hd (firstSheet p)).symm.trans heq
  have hst : p.1 = q.1 := by
    simpa [firstSheet, secondSheet, moveVector] using
      congrArg (fun z : Space => z.1.1) he
  have hu : p.2 = 0 := by
    simpa [firstSheet, secondSheet, moveVector] using
      congrArg (fun z : Space => z.2.1) he
  have ht : cutoff (firstSheet p) * (2 * h) = h * (1 - q.1 ^ 2) := by
    simpa [firstSheet, secondSheet, moveVector, smul_eq_mul] using
      congrArg (fun z : Space => z.1.2) he
  have hheight : 0 ≤ h * (1 - q.1 ^ 2) := by
    rw [← ht]
    exact mul_nonneg (cutoff_nonneg _) (by positivity)
  have hlevel : 0 ≤ 1 - q.1 ^ 2 := nonneg_of_mul_nonneg_right hheight hh
  have habs : |q.1| ≤ 1 := abs_le.mpr
    ⟨by nlinarith [sq_nonneg (q.1 + 1)], by nlinarith [sq_nonneg (q.1 - 1)]⟩
  have hp : p = (q.1, 0) := Prod.ext hst hu
  rw [hp, cutoff_firstSheet_zero habs] at ht
  nlinarith [mul_nonneg hh.le (sq_nonneg q.1)]

/-- The ranges of the actual moved first sheet and the original second sheet are disjoint. -/
theorem disjoint_shifted_ranges {h : ℝ} (hh : 0 < h) {d : Space → Space}
    (hd : ∀ z, d z = z + cutoff z • moveVector h) :
    Disjoint (range (d ∘ firstSheet)) (range (secondSheet h)) := by
  rw [Set.disjoint_left]
  rintro z ⟨p, rfl⟩ ⟨q, hq⟩
  exact shifted_firstSheet_ne_secondSheet hh hd p q hq.symm

/-- An actual compactly supported smooth diffeomorphism removes the model's two intersections. -/
theorem exists_small_model_cancellation :
    ∃ η : ℝ, 0 < η ∧ ∀ h : ℝ, 0 < h → h < η →
      ∃ d : Diffeomorph 𝓘(ℝ, Space) 𝓘(ℝ, Space) Space Space ∞,
        (∀ z, d z = z + cutoff z • moveVector h) ∧
        (∀ z ∉ tsupport cutoff, d z = z) ∧
        Disjoint (range (d ∘ firstSheet)) (range (secondSheet h)) := by
  obtain ⟨ε, hε, hsmall⟩ :=
    SmallPerturbation.exists_radius_bumpTranslation contDiff_cutoff hasCompactSupport_cutoff
  refine ⟨ε / 4, by positivity, ?_⟩
  intro h hh hsmallh
  have hnorm : ‖moveVector h‖ < ε := by
    rw [norm_moveVector hh.le]
    linarith
  obtain ⟨d, hd, hfix⟩ := hsmall (moveVector h) hnorm
  exact ⟨d, hd, hfix, disjoint_shifted_ranges hh hd⟩

end Wikipedia.SmoothSixDPoincare.WhitneyPairModel
