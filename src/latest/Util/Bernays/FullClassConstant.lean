import Util.Bernays.ClassSliceDilation
import Util.Bernays.SmoothSummability
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The convergent, positive common constant, including discriminant-prime factors
-/

open Filter Topology
open scoped Classical

namespace Bernays

noncomputable def fullClassConstant {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) : ℝ :=
  letI := quadraticOrderIsDomain hD
  ∑' m : Nat.factoredNumbers (discriminantLevel (b ^ 2 + 4 * d)).primeFactors,
    goodClassConstant hD * (normGenusSet hD m.val).card / m.val

theorem summable_fullClassCoefficients {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    Summable (fun m : Nat.factoredNumbers (discriminantLevel (b ^ 2 + 4 * d)).primeFactors =>
      goodClassConstant hD * (normGenusSet hD m.val).card / m.val) := by
  letI := quadraticOrderIsDomain hD
  obtain ⟨B, hB, hbound⟩ := exists_classSlice_dilation_bound hD
  have hs : Summable (fun m : Nat.factoredNumbers
      (discriminantLevel (b ^ 2 + 4 * d)).primeFactors => B / Real.sqrt (m.val : ℝ)) := by
    simpa only [mul_one_div] using (summable_factored_inv_sqrt
      (discriminantLevel (b ^ 2 + 4 * d)).primeFactors).mul_left B
  apply hs.of_norm_bounded
  intro m
  exact le_of_tendsto (classSliceValues_card_dilation_limit hD 1 m.val m.property).norm
    (Eventually.of_forall fun N => hbound 1 m.val m.property N)

theorem fullClassConstant_pos {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    0 < fullClassConstant hD := by
  letI := quadraticOrderIsDomain hD
  let m₁ : Nat.factoredNumbers (discriminantLevel (b ^ 2 + 4 * d)).primeFactors :=
    ⟨1, Nat.mem_factoredNumbers'.mpr (fun p hp hp₁ => (hp.not_dvd_one hp₁).elim)⟩
  have hpos : 0 < goodClassConstant hD * (normGenusSet hD m₁.val).card / m₁.val := by
    simpa only [m₁, normGenusSet_one, Finset.card_singleton, Nat.cast_one, mul_one, div_one]
      using goodClassConstant_pos hD
  exact (summable_fullClassCoefficients hD).tsum_pos
    (fun m => div_nonneg (mul_nonneg (goodClassConstant_pos hD).le (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)) m₁ hpos

theorem classSlice_tsum_limit {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ C : ClassGroup (QuadraticAlgebra ℤ d b),
      Tendsto (fun N : ℕ => ∑' m : Nat.factoredNumbers
        (discriminantLevel (b ^ 2 + 4 * d)).primeFactors,
        ((classSliceValues hD C m.val (N / m.val)).card : ℝ) / scale N)
      atTop (𝓝 (fullClassConstant hD)) := by
  letI := quadraticOrderIsDomain hD
  intro C
  obtain ⟨B, hB, hbound⟩ := exists_classSlice_dilation_bound hD
  have hs : Summable (fun m : Nat.factoredNumbers
      (discriminantLevel (b ^ 2 + 4 * d)).primeFactors => B / Real.sqrt (m.val : ℝ)) := by
    simpa only [mul_one_div] using (summable_factored_inv_sqrt
      (discriminantLevel (b ^ 2 + 4 * d)).primeFactors).mul_left B
  exact tendsto_tsum_of_dominated_convergence hs
    (fun m => classSliceValues_card_dilation_limit hD C m.val m.property)
    (Eventually.of_forall fun N m => hbound C m.val m.property N)

end Bernays
