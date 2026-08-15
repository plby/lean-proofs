import ErdosProblems.Erdos321.FractionalLogBlock

namespace Erdos321

noncomputable def naturalMassError (B : ℝ) (r : ℕ) : ℝ :=
  1 / (2 : ℝ) ^ (r + 1) + 6 / ((2 : ℝ) ^ r * B)

noncomputable def naturalMassRetention (B : ℝ) (d : ℕ) : ℝ :=
  ∏ r ∈ Finset.range d, (1 - naturalMassError B r)

private theorem naturalMassError_eq {B : ℝ} (hB : B ≠ 0) (r : ℕ) :
    naturalMassError B r = (1 / 2 + 6 / B) / (2 : ℝ) ^ r := by
  dsimp [naturalMassError]
  rw [show r + 1 = r + 1 by rfl, pow_succ]
  field_simp

private theorem shifted_geometric_sum_le_one (k : ℕ) :
    (∑ r ∈ Finset.range k, 1 / (2 : ℝ) ^ (r + 1)) ≤ 1 := by
  have h := blockFraction_sum_le_half k
  have heq : (∑ r ∈ Finset.range k, 1 / (2 : ℝ) ^ (r + 1)) =
      2 * ∑ r ∈ Finset.range k, 1 / (2 : ℝ) ^ (r + 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [show r + 2 = (r + 1) + 1 by omega, pow_succ]
    ring
  rw [heq]
  nlinarith

private theorem naturalMassError_nonneg
    {B : ℝ} (hB : 0 < B) (r : ℕ) : 0 ≤ naturalMassError B r := by
  dsimp [naturalMassError]
  positivity

/-- After isolating the first block, all remaining natural mass errors have
total at most `17/32` at terminal threshold `B≥192`. -/
theorem naturalMassError_tail_sum_le
    {B : ℝ} (hB : 192 ≤ B) (k : ℕ) :
    (∑ r ∈ Finset.range k, naturalMassError B (r + 1)) ≤ 17 / 32 := by
  have hBpos : 0 < B := by linarith
  have hc : 1 / 2 + 6 / B ≤ (17 / 32 : ℝ) := by
    have h6 : 6 / B ≤ (1 / 32 : ℝ) := by
      apply (div_le_iff₀ hBpos).2
      nlinarith
    linarith
  have hg := shifted_geometric_sum_le_one k
  have heq : (∑ r ∈ Finset.range k, naturalMassError B (r + 1)) =
      (1 / 2 + 6 / B) *
        ∑ r ∈ Finset.range k, 1 / (2 : ℝ) ^ (r + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [naturalMassError_eq (ne_of_gt hBpos)]
    ring
  rw [heq]
  have hc0 : 0 ≤ 1 / 2 + 6 / B := by positivity
  calc
    (1 / 2 + 6 / B) *
        (∑ r ∈ Finset.range k, 1 / (2 : ℝ) ^ (r + 1)) ≤
      (1 / 2 + 6 / B) * 1 := mul_le_mul_of_nonneg_left hg hc0
    _ ≤ 17 / 32 := by linarith

/-- The natural block mass product retains an absolute fraction, uniformly in
depth. -/
theorem one_eighth_le_naturalMassRetention
    {B : ℝ} (hB : 192 ≤ B) (d : ℕ) :
    1 / 8 ≤ naturalMassRetention B d := by
  cases d with
  | zero => norm_num [naturalMassRetention]
  | succ k =>
      have hBpos : 0 < B := by linarith
      have htailSum := naturalMassError_tail_sum_le hB k
      have htail0 : ∀ r ∈ Finset.range k,
          0 ≤ naturalMassError B (r + 1) := fun r hr =>
        naturalMassError_nonneg hBpos _
      have htail1 : ∀ r ∈ Finset.range k,
          naturalMassError B (r + 1) ≤ 1 := by
        intro r hr
        have hpoint : naturalMassError B (r + 1) ≤
            ∑ i ∈ Finset.range k, naturalMassError B (i + 1) := by
          apply Finset.single_le_sum htail0
          exact hr
        linarith
      have htailProd := one_sub_sum_le_prod_one_sub htail0 htail1
      have htail : (15 / 32 : ℝ) ≤
          ∏ r ∈ Finset.range k, (1 - naturalMassError B (r + 1)) := by
        linarith
      have hfirst : (15 / 32 : ℝ) ≤ 1 - naturalMassError B 0 := by
        rw [naturalMassError_eq (ne_of_gt hBpos)]
        norm_num
        have hc : 6 / B ≤ (1 / 32 : ℝ) := by
          apply (div_le_iff₀ hBpos).2
          nlinarith
        linarith
      dsimp [naturalMassRetention]
      rw [Finset.prod_range_succ']
      have htailNonneg : 0 ≤
          ∏ r ∈ Finset.range k, (1 - naturalMassError B (r + 1)) :=
        (by norm_num : (0 : ℝ) ≤ 15 / 32).trans htail
      have hm := mul_le_mul htail hfirst (by norm_num) htailNonneg
      nlinarith

end Erdos321
