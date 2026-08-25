import Util.Bernays.SmoothCounting
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# The exact smooth-part decomposition as a series
-/

open scoped Classical

namespace Bernays

theorem coprimeSliceValues_eq_empty_of_lt (R : ℕ → Prop) {M m N : ℕ} (hNm : N < m) :
    coprimeSliceValues R M m (N / m) = ∅ := by
  simp [coprimeSliceValues, Nat.div_eq_of_lt hNm]

theorem positiveValues_card_eq_tsum (R : ℕ → Prop) {M : ℕ} (hM : M ≠ 0) (N : ℕ) :
    ((positiveValues R N).card : ℝ) = ∑' m : Nat.factoredNumbers M.primeFactors,
      ((coprimeSliceValues R M m.val (N / m.val)).card : ℝ) := by
  let S := (Finset.Icc 1 N).subtype (fun m => m ∈ Nat.factoredNumbers M.primeFactors)
  have hz (m : Nat.factoredNumbers M.primeFactors) (hm : m ∉ S) :
      ((coprimeSliceValues R M m.val (N / m.val)).card : ℝ) = 0 := by
    have hmpos : 0 < m.val := Nat.pos_of_ne_zero m.property.1
    have hNm : N < m.val := by
      have hnot : m.val ∉ Finset.Icc 1 N := by simpa only [S, Finset.mem_subtype] using hm
      simp only [Finset.mem_Icc, not_and] at hnot
      exact Nat.lt_of_not_ge (hnot hmpos)
    rw [coprimeSliceValues_eq_empty_of_lt R hNm, Finset.card_empty, Nat.cast_zero]
  rw [tsum_eq_sum hz]
  dsimp only [S]
  rw [Finset.sum_subtype_eq_sum_filter
    (fun m : ℕ => ((coprimeSliceValues R M m (N / m)).card : ℝ)), ← Nat.cast_sum]
  exact congrArg (fun n : ℕ => (n : ℝ)) (positiveValues_card_smooth_sum R hM N)

end Bernays
