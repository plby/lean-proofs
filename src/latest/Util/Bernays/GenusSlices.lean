import Util.Bernays.NormGenusSets

/-!
# Genus slices at a fixed discriminant-prime part
-/

open Filter Topology
open scoped Classical

namespace Bernays

noncomputable def genusSliceValues {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ClassGroup (QuadraticAlgebra ℤ d b) → ℕ → ℕ → Finset ℕ :=
  letI := quadraticOrderIsDomain hD
  fun C m N => (goodLocalValues d b hD.ne N).filter fun n =>
    genusValue hD n ∈ remainderGenusSet hD C m

theorem genusValues_eq_goodLocal_filter {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (g : GenusGroup (QuadraticAlgebra ℤ d b)) (N : ℕ),
      genusValues hD g N = (goodLocalValues d b hD.ne N).filter (fun n => genusValue hD n = g) := by
  let := quadraticOrderIsDomain hD
  intro g N
  ext n
  simp only [genusValues, goodLocalValues, Finset.mem_filter, and_assoc]

theorem genusSliceValues_card {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (C : ClassGroup (QuadraticAlgebra ℤ d b)) (m N : ℕ),
      (genusSliceValues hD C m N).card =
        ∑ g ∈ remainderGenusSet hD C m, (genusValues hD g N).card := by
  let := quadraticOrderIsDomain hD
  intro C m N
  simp_rw [genusValues_eq_goodLocal_filter]
  exact (Finset.sum_card_fiberwise_eq_card_filter (goodLocalValues d b hD.ne N)
    (remainderGenusSet hD C m) (genusValue hD)).symm

theorem genusSliceValues_card_limit {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (C : ClassGroup (QuadraticAlgebra ℤ d b)) (m : ℕ),
      Tendsto (fun N : ℕ => ((genusSliceValues hD C m N).card : ℝ) / scale N)
        atTop (𝓝 (goodClassConstant hD * (normGenusSet hD m).card)) := by
  let := quadraticOrderIsDomain hD
  intro C m
  have h := tendsto_finsetSum (remainderGenusSet hD C m) (fun g _ => genusValues_card_limit hD g)
  simp only [Finset.sum_const, nsmul_eq_mul, remainderGenusSet_card] at h
  rw [mul_comm] at h
  apply h.congr'
  filter_upwards [] with N
  rw [genusSliceValues_card, Nat.cast_sum, Finset.sum_div]

end Bernays
