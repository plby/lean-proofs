import ErdosProblems.Erdos520.HarperDyadicEnergyAssembly
import ErdosProblems.Erdos520.HarperEconomicalMomentIteration
import ErdosProblems.Erdos520.HarperParsevalTail

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open MeasureTheory Set

namespace Erdos
namespace Problem520

/-!
# Set geometry for the economical local-moment assembly

These lemmas put the actual unit intervals and signed central bands into the
absolute-value forms consumed by the two positive-log recursion wrappers.
-/

/-- Every noncentral unit interval has height at least its shell index. -/
theorem shell_le_abs_of_mem_harperEulerUnitInterval
    (positive : Bool) (shell : ℕ) {t : ℝ}
    (ht : t ∈ harperEulerUnitInterval positive shell) :
    (shell : ℝ) ≤ |t| := by
  cases positive with
  | false =>
      simp only [harperEulerUnitInterval, Bool.false_eq_true, if_false,
        Set.mem_Ioc] at ht
      have hneg : (shell : ℝ) ≤ -t := by linarith
      exact hneg.trans (neg_le_abs t)
  | true =>
      simp only [harperEulerUnitInterval, if_true, Set.mem_Ico] at ht
      exact ht.1.trans (le_abs_self t)

/-- Every point of a unit interval has height at most the next integer. -/
theorem abs_le_succ_of_mem_harperEulerUnitInterval
    (positive : Bool) (shell : ℕ) {t : ℝ}
    (ht : t ∈ harperEulerUnitInterval positive shell) :
    |t| ≤ (shell + 1 : ℕ) := by
  cases positive with
  | false =>
      simp only [harperEulerUnitInterval, Bool.false_eq_true, if_false,
        Set.mem_Ioc] at ht
      rw [abs_of_nonpos (by linarith : t ≤ 0)]
      push_cast at ht ⊢
      linarith
  | true =>
      simp only [harperEulerUnitInterval, if_true, Set.mem_Ico] at ht
      rw [abs_of_nonneg (by linarith : 0 ≤ t)]
      push_cast at ht ⊢
      linarith

/-- In particular, every shell after the central shell satisfies the lower
height hypothesis of the noncentral wrapper. -/
theorem one_le_abs_of_mem_harperEulerUnitInterval
    (positive : Bool) {shell : ℕ} (hshell : 1 ≤ shell) {t : ℝ}
    (ht : t ∈ harperEulerUnitInterval positive shell) :
    1 ≤ |t| := by
  have hshellR : (1 : ℝ) ≤ (shell : ℝ) := by exact_mod_cast hshell
  exact hshellR.trans
    (shell_le_abs_of_mem_harperEulerUnitInterval positive shell ht)

/-- A signed band at index `depth` is exactly in the central scale consumed
by the wrapper with parameter `depth + 1`. -/
theorem abs_bounds_of_mem_harperSignedDyadicBand
    (positive : Bool) (depth : ℕ) {t : ℝ}
    (ht : t ∈ harperSignedDyadicBand positive depth) :
    (1 / 2 : ℝ) ^ ((depth + 1) + 1) < |t| ∧
      |t| ≤ (1 / 2 : ℝ) ^ (depth + 1) := by
  have hr0 : 0 < harperDyadicRadius (depth + 1) :=
    harperDyadicRadius_pos (depth + 1)
  cases positive with
  | false =>
      simp only [harperSignedDyadicBand, Bool.false_eq_true, if_false,
        Set.mem_Ico] at ht
      have htneg : t < 0 := ht.2.trans (by linarith)
      have hb : harperDyadicRadius (depth + 1) < |t| ∧
          |t| ≤ harperDyadicRadius depth := by
        rw [abs_of_neg htneg]
        exact ⟨by linarith, by linarith⟩
      simpa [harperDyadicRadius, one_div, Nat.add_assoc] using! hb
  | true =>
      simp only [harperSignedDyadicBand, if_true, Set.mem_Ioc] at ht
      have htpos : 0 < t := hr0.trans ht.1
      have hb : harperDyadicRadius (depth + 1) < |t| ∧
          |t| ≤ harperDyadicRadius depth := by
        rwa [abs_of_pos htpos]
      simpa [harperDyadicRadius, one_div, Nat.add_assoc] using! hb

/-- A scheduled endpoint itself is a completely explicit eventual cutoff
for any prescribed available-scale threshold. -/
theorem threshold_le_harperAvailableLogScale_of_endpoint
    (threshold : ℕ) {y : ℕ}
    (hy : harperBlockEndpoint threshold ≤ y) :
    threshold ≤ harperAvailableLogScale y := by
  have h :=
    add_four_le_harperAvailableLogScale_of_blockEndpoint_le hy
  omega

end Problem520
end Erdos

#print axioms Erdos.Problem520.shell_le_abs_of_mem_harperEulerUnitInterval
#print axioms Erdos.Problem520.abs_bounds_of_mem_harperSignedDyadicBand
#print axioms Erdos.Problem520.threshold_le_harperAvailableLogScale_of_endpoint
