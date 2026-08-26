import ErdosProblems.Erdos421.RoughInductionContributions
import ErdosProblems.Erdos421.RoughInductionCofactors
import ErdosProblems.Erdos421.RoughBoundaryCorrection

/-! # The complete inductive step for the actual rough-number count -/

namespace Erdos421

theorem roughCountEstimate_step {n : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hcount : RoughCountEstimate n C) :
    RoughCountEstimate (n + 1) (32 * C * ((n : ℝ) + 3) + 24) := by
  intro A ε hA hε
  have hε₄ : 0 < ε / 4 := by positivity
  obtain ⟨B₀, hB₀, hbase⟩ := roughCountEstimate_zero A ε hA hε
  obtain ⟨B₁, hB₁, hprime⟩ := prime_count_long_asymptotic hA hε₄
  obtain ⟨B₂, hB₂, hcof⟩ := roughCountEstimate_cofactor_error hC hcount hA hε₄
  obtain ⟨B₃, hB₃, hbound⟩ := rough_boundary_correction_log_saving hA hε₄
  obtain ⟨B₄, hB₄, hmain⟩ := buchstab_count_main_saving n hA hε₄
  refine ⟨max 16 (max B₀ (max B₁ (max B₂ (max B₃ B₄)))),
    (by norm_num : (1 : ℝ) < 16).trans_le (le_max_left _ _), ?_⟩
  intro b hb a ha hab z hz hzb hbz
  obtain ⟨hb16, hb₀, hb₁, hb₂, hb₃, hb₄⟩ :=
    (by simpa only [max_le_iff] using hb :
      16 ≤ b ∧ B₀ ≤ b ∧ B₁ ≤ b ∧ B₂ ≤ b ∧ B₃ ≤ b ∧ B₄ ≤ b)
  change b ≤ (z : ℝ) ^ (n + 3) at hbz
  by_cases hsq : b ≤ (z : ℝ) ^ 2
  · have h := hbase b hb₀ a ha hab z hz hzb hsq
    rw [roughCountMain_eq_base (n + 1) hz hzb hsq]
    have hprod : 0 ≤ 32 * C * ((n : ℝ) + 3) := by positivity
    have h8 : 8 ≤ 32 * C * ((n : ℝ) + 3) + 24 := by linarith
    exact h.trans (add_le_add le_rfl (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right h8 (sq_nonneg (b - a))) (by positivity)))
  have hzs : (z : ℝ) ≤ Real.sqrt b := Real.le_sqrt_of_sq_le (le_of_not_ge hsq)
  let P : ℝ := (primesInRealInterval a b).card
  let Q : ℝ := ∑ p ∈ sievePrimes z (roughSquareCutoff b),
    ((roughInRealInterval (a / p) (b / p) p).card : ℝ)
  let R : ℝ := ∑ p ∈ sievePrimes z (roughSquareCutoff b), roughCountMain n (a / p) (b / p) p
  let S : ℝ := ∑ p ∈ sievePrimes z (roughSquareCutoff b),
    finiteBuchstab n (logarithmicBuchstabArgument b p) / ((p : ℝ) * Real.log p)
  let M : ℝ := roughCountMain (n + 1) a b z
  have heq : ((roughInRealInterval a b z).card : ℝ) = P + Q := by
    have h := rough_square_cutoff_buchstab hb16 ha hab hzs
    dsimp only [P, Q]
    exact_mod_cast h
  have hp : |P - (b - a) / Real.log b| ≤
      (ε / 4) * b / (Real.log b) ^ A + 8 * (b - a) ^ 2 / (b * (Real.log b) ^ 2) :=
    hprime b hb₁ a ha hab
  have hc : |Q - R| ≤ (ε / 4) * b / (Real.log b) ^ A +
      (32 * C * ((n : ℝ) + 3)) * (b - a) ^ 2 / (b * (Real.log b) ^ 2) :=
    hcof b hb₂ a ha hab z hz hbz
  have hd : |R - (b - a) * S| ≤ (ε / 4) * b / (Real.log b) ^ A +
      16 * (b - a) ^ 2 / (b * (Real.log b) ^ 2) := by
    rw [abs_sub_comm]
    exact hbound b hb₃ a ha hab n z
  have hm : |(b - a) / Real.log b + (b - a) * S - M| ≤
      (ε / 4) * b / (Real.log b) ^ A := hmain b hb₄ a ha hab z hz hzs hbz
  change |((roughInRealInterval a b z).card : ℝ) - M| ≤ _
  rw [heq]
  calc
    _ = |(P - (b - a) / Real.log b) + (Q - R) + (R - (b - a) * S) +
        ((b - a) / Real.log b + (b - a) * S - M)| := by congr 1; ring
    _ ≤ |P - (b - a) / Real.log b| + |Q - R| + |R - (b - a) * S| +
        |(b - a) / Real.log b + (b - a) * S - M| :=
      (abs_add_le _ _).trans (add_le_add
        ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _ ≤ _ := add_le_add (add_le_add (add_le_add hp hc) hd) hm
    _ = _ := by ring

end Erdos421
