import BoundedGaps.Maynard.PrimeMertens
import BoundedGaps.Maynard.CoprimeHarmonicGlobalBound
import BoundedGaps.Maynard.WeightedSmoothAbel

/-!
# A bounded prime Mertens error at real endpoints
-/

namespace Erdos964

open BoundedGaps.Maynard

noncomputable def primeLogHarmonicWeight (n : ℕ) : ℝ :=
  if n.Prime then Real.log n / (n : ℝ) else 0

theorem primeLogHarmonicWeight_cumulative (t : ℝ) :
    abelCumulative primeLogHarmonicWeight t = primeLogHarmonicSum ⌊t⌋₊ := by
  classical
  unfold abelCumulative primeLogHarmonicWeight primeLogHarmonicSum
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primesLE, Nat.zero_le, true_and]
  · intro n hn
    rfl

theorem exists_primeLogHarmonicWeight_cumulative_error :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ t : ℝ, 1 ≤ t →
      |abelCumulative primeLogHarmonicWeight t - Real.log t| ≤ E := by
  obtain ⟨C, hC⟩ := exists_uniform_abs_primeLogHarmonicSum_sub_log
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  refine ⟨C + Real.log 2, by positivity, ?_⟩
  intro t ht
  rw [primeLogHarmonicWeight_cumulative]
  exact (abs_sub_le _ (Real.log (⌊t⌋₊ : ℕ)) _).trans
    (add_le_add (hC _) (abs_log_natFloor_sub_log_le_log_two_global ht))

end Erdos964
