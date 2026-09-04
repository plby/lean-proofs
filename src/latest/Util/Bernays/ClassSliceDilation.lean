import Util.Bernays.ClassSlices
import Util.Bernays.DilatedCountBound

/-!
# Fixed-factor class limits and their uniform summable bound
-/

open Filter Topology
open scoped Classical

namespace Bernays

theorem classSliceValues_zero {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (C : ClassGroup (QuadraticAlgebra ℤ d b)) (m : ℕ),
      classSliceValues hD C m 0 = ∅ := by
  let := quadraticOrderIsDomain hD
  intro C m
  simp [classSliceValues]

theorem classSliceValues_card_le_goodLocal {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (C : ClassGroup (QuadraticAlgebra ℤ d b)) (m : ℕ),
      m ∈ Nat.factoredNumbers (discriminantLevel (b ^ 2 + 4 * d)).primeFactors →
      ∀ N : ℕ, (classSliceValues hD C m N).card ≤ (goodLocalValues d b hD.ne N).card := by
  let := quadraticOrderIsDomain hD
  intro C m hm N
  apply Finset.card_le_card
  exact (classSliceValues_subset_genusSliceValues hD C m hm N).trans (Finset.filter_subset _ _)

theorem classSliceValues_card_dilation_limit {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (C : ClassGroup (QuadraticAlgebra ℤ d b)) (m : ℕ),
      m ∈ Nat.factoredNumbers (discriminantLevel (b ^ 2 + 4 * d)).primeFactors →
      Tendsto (fun N : ℕ => ((classSliceValues hD C m (N / m)).card : ℝ) / scale N)
        atTop (𝓝 (goodClassConstant hD * (normGenusSet hD m).card / m)) := by
  let := quadraticOrderIsDomain hD
  intro C m hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm.1
  have h := (count_floor_dilation_limit (classSliceValues_card_limit hD C m hm)
    (one_div_pos.mpr hmR)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [Function.comp_def, one_div_mul_eq_div, Nat.floor_div_natCast, Nat.floor_natCast,
    mul_one_div] using h

theorem exists_classSlice_dilation_bound {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∃ B : ℝ, 0 < B ∧ ∀ (C : ClassGroup (QuadraticAlgebra ℤ d b)) (m : ℕ),
      m ∈ Nat.factoredNumbers (discriminantLevel (b ^ 2 + 4 * d)).primeFactors →
      ∀ N : ℕ, ‖((classSliceValues hD C m (N / m)).card : ℝ) / scale N‖ ≤
        B / Real.sqrt (m : ℝ) := by
  let := quadraticOrderIsDomain hD
  obtain ⟨B, hB, hcount⟩ := exists_logCountBound_of_limit
    (fun N => Nat.cast_nonneg (goodLocalValues d b hD.ne N).card)
    (fun N => (Nat.cast_le (α := ℝ)).mpr (goodLocalValues_card_le hD.ne N))
    (goodLocalConstant_pos hD).le (goodLocalValues_card_limit hD)
  refine ⟨2 * B, mul_pos (by norm_num) hB, fun C m hm N => ?_⟩
  have hs : 0 ≤ scale (N : ℝ) := div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  rw [Real.norm_of_nonneg (div_nonneg (Nat.cast_nonneg _) hs)]
  apply count_dilation_scale_bound (A := fun k => ((classSliceValues hD C m k).card : ℝ))
    (by rw [classSliceValues_zero, Finset.card_empty, Nat.cast_zero])
    hB.le _ (Nat.pos_of_ne_zero hm.1) N
  intro k
  exact ((Nat.cast_le (α := ℝ)).mpr (classSliceValues_card_le_goodLocal hD C m hm k)).trans (hcount k)

end Bernays
