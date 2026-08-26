/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Root moments control the sign counts of shifted coefficient windows.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.WindowGrid
import ErdosProblems.Erdos521.IntervalMoments
import ErdosProblems.Erdos521.ZeroOne

namespace Erdos521

open MeasureTheory

theorem windowGridSignChanges_pow_integrable (W : Finset ℕ) (g : ℕ → ℝ) (N p : ℕ) :
    Integrable (fun ε ↦ (windowGridSignChanges ε W g N : ℝ) ^ p) sequenceLaw :=
  bounded_nat_pow_integrable sequenceLaw (measurable_windowGridSignChanges W g N).aemeasurable N p
    (fun ε ↦ windowGridSignChanges_le ε W g N)

theorem integral_windowGridSignChanges_pow_le {L U : ℕ} (hLU : L < U)
    (g : ℕ → ℝ) (hg : Monotone g) (hpos : ∀ i, 0 < g i) (N p : ℕ) :
    (∫ ε, (windowGridSignChanges ε (Finset.Ico L U) g N : ℝ) ^ p ∂sequenceLaw) ≤
      ∫ ε, (intervalRootCount ε (U - L - 1) (g 0) (g N) : ℝ) ^ p ∂sequenceLaw := by
  let R := fun ε ↦ (intervalRootCount ε (U - L - 1) (g 0) (g N) : ℝ) ^ p
  have hR : Integrable R sequenceLaw := intervalRootCount_pow_integrable _ _ _ _
  have hshift : MeasurePreserving (shift (α := ℝ) L) sequenceLaw sequenceLaw := measurePreserving_shift signLaw L
  have hRmap : Integrable R (sequenceLaw.map (shift L)) := by rw [hshift.map_eq]; exact hR
  have hcomp : Integrable (R ∘ shift L) sequenceLaw := hRmap.comp_measurable hshift.measurable
  have heq := hshift.hasLaw.integral_comp hR.aestronglyMeasurable
  change (∫ ε, (windowGridSignChanges ε (Finset.Ico L U) g N : ℝ) ^ p ∂sequenceLaw) ≤ ∫ ε, R ε ∂sequenceLaw
  rw [← heq]
  apply integral_mono_ae (windowGridSignChanges_pow_integrable _ _ _ _) hcomp
  filter_upwards [ae_sequence_signs] with ε hε
  rw [windowGridSignChanges_Ico ε hLU g hpos N]
  have hε₀ : (shift L ε) 0 ≠ 0 := by
    rcases hε L with h | h <;> simp [shift, h]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr
    (gridSignChanges_le_intervalRootCount (shift L ε) (U - L - 1) hε₀ g hg N)) p

theorem window_grid_capping_probability {L U : ℕ} (hLU : L < U)
    (g : ℕ → ℝ) (hg : Monotone g) (hpos : ∀ i, 0 < g i) (N p : ℕ) {T : ℝ} (hT : 0 < T) :
    sequenceLaw.real {ε | T ≤ (windowGridSignChanges ε (Finset.Ico L U) g N : ℝ)} ≤
      (∫ ε, (intervalRootCount ε (U - L - 1) (g 0) (g N) : ℝ) ^ p ∂sequenceLaw) / T ^ p := by
  have h := measureReal_le_integral_div_of_ae sequenceLaw
    (windowGridSignChanges_pow_integrable (Finset.Ico L U) g N p)
    (Filter.Eventually.of_forall (fun ε ↦ pow_nonneg (Nat.cast_nonneg _) p)) (pow_pos hT p)
    (Filter.Eventually.of_forall (fun ε hε ↦ pow_le_pow_left₀ hT.le hε p))
  exact h.trans (div_le_div_of_nonneg_right
    (integral_windowGridSignChanges_pow_le hLU g hg hpos N p) (pow_nonneg hT.le p))

end Erdos521
