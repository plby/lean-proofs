import Wikipedia.HopfProblem.SpecialPeriodsTriangleShimizuMatrices
import Wikipedia.HopfProblem.SpecialPeriodsTriangleShimizuSequences
import Wikipedia.HopfProblem.SpecialPeriodsTriangleDiscrete

/-!
# The Shimizu--Leutbecher bound for the actual triangle group

For a discrete subgroup containing translation by `w > 0`, a nonzero
lower-left entry has absolute value at least `1 / w`.  The proof constructs
actual conjugates in the subgroup, proves their convergence to the
translation, and contradicts discreteness.  The final specialization uses
the proved inherited discreteness of the triangle matrix group.
-/

noncomputable section

open Matrix Filter Topology
open scoped MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

/-- If its initial scaled lower-left entry is small, the actual conjugation
sequence converges to the translation in the inherited matrix topology. -/
theorem shimizuSequence_tendsto_translation (w : ℝ) (A : SL(2, ℝ))
    (hw : w ≠ 0) (hsmall : |w * A 1 0| < 1) :
    Tendsto (shimizuSequence w A) atTop (𝓝 (shimizuTranslation w)) := by
  obtain ⟨hq, ha⟩ := shimizu_recurrence_tendsto
    (fun n => w * shimizuSequence w A n 1 0)
    (fun n => shimizuSequence w A n 0 0)
    (shimizuSequence_succ_scaled_lower_left w A)
    (shimizuSequence_succ_zero_zero w A) hsmall
  have hc : Tendsto (fun n => shimizuSequence w A n 1 0) atTop (𝓝 (0 : ℝ)) := by
    simpa [hw] using hq.div_const w
  have hp : Tendsto
      (fun n => shimizuSequence w A n 0 0 * (w * shimizuSequence w A n 1 0))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_mul] using ha.mul hq
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  fin_cases i <;> fin_cases j
  · change Tendsto (fun n => shimizuSequence w A n 0 0) atTop (𝓝 (1 : ℝ))
    exact ha
  · change Tendsto (fun n => shimizuSequence w A n 0 1) atTop (𝓝 w)
    apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [shimizuSequence_succ_zero_one, one_pow, mul_one] using (ha.pow 2).const_mul w
  · change Tendsto (fun n => shimizuSequence w A n 1 0) atTop (𝓝 (0 : ℝ))
    exact hc
  · change Tendsto (fun n => shimizuSequence w A n 1 1) atTop (𝓝 (1 : ℝ))
    apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [shimizuSequence_succ_one_one, add_zero] using hp.const_add 1

/-- The scale-invariant Shimizu--Leutbecher inequality for a subgroup with
its inherited discrete topology. -/
theorem shimizu_leutbecher_scaled (Γ : Subgroup (SL(2, ℝ))) [DiscreteTopology Γ]
    (w : ℝ) (hw : w ≠ 0) (hT : shimizuTranslation w ∈ Γ)
    (A : SL(2, ℝ)) (hA : A ∈ Γ) (hc : A 1 0 ≠ 0) :
    1 ≤ |w * A 1 0| := by
  by_contra! hsmall
  let u : ℕ → Γ := fun n => ⟨shimizuSequence w A n, shimizuSequence_mem Γ w A hT hA n⟩
  let t : Γ := ⟨shimizuTranslation w, hT⟩
  have ht : Tendsto u atTop (𝓝 t) :=
    tendsto_subtype_rng.mpr (shimizuSequence_tendsto_translation w A hw hsmall)
  have he : ∀ᶠ n in atTop, u n = t := by
    simpa only [nhds_discrete, tendsto_pure] using ht
  obtain ⟨n, hn⟩ := he.exists
  have hzero : shimizuSequence w A n 1 0 = 0 := by
    have h := congrArg (fun B : Γ => (B : SL(2, ℝ)) 1 0) hn
    simpa [u, t, shimizuTranslation] using h
  exact shimizuSequence_lower_left_ne_zero w A hw hc n hzero

/-- The usual width-normalized form of the Shimizu--Leutbecher inequality. -/
theorem shimizu_leutbecher (Γ : Subgroup (SL(2, ℝ))) [DiscreteTopology Γ]
    (w : ℝ) (hw : 0 < w) (hT : shimizuTranslation w ∈ Γ)
    (A : SL(2, ℝ)) (hA : A ∈ Γ) (hc : A 1 0 ≠ 0) :
    1 / w ≤ |A 1 0| := by
  apply (div_le_iff₀ hw).mpr
  simpa only [abs_mul, abs_of_pos hw, mul_comm] using
    shimizu_leutbecher_scaled Γ w hw.ne' hT A hA hc

/-- An unconditional lower-left-entry bound in the constructed triangle group. -/
theorem matrixGroup_lower_left_bound (A : SL(2, ℝ)) (hA : A ∈ matrixGroup)
    (hc : A 1 0 ≠ 0) : 1 / width ≤ |A 1 0| := by
  apply shimizu_leutbecher matrixGroup width width_pos ?_ A hA hc
  rw [shimizuTranslation_width, ← generatorOneSL_mul_generatorTwoSL]
  exact matrixGroup.mul_mem generatorOneSL_mem_matrixGroup generatorTwoSL_mem_matrixGroup

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
