import ErdosProblems.Erdos421.IteratedLogSums

/-! # Uniform bounds over all bounded lists of logarithmic shifts -/

namespace Erdos421

theorem differenceCoefficient_zero (hs : List ℝ) :
    differenceCoefficient 0 hs = (hs.length.factorial : ℝ) * hs.prod := by
  simp only [differenceCoefficient, Nat.zero_add, Nat.one_ascFactorial]

noncomputable def logDifferenceLeafBound (M H r : ℕ) (τ δ : ℝ) : ℝ :=
  (τ * r.factorial * (H : ℝ) ^ r / (M : ℝ) ^ (r + 1) + 3) *
    (2 + 12 / δ + 2 * δ * (2 * M + r * H + 1 : ℝ) ^ (r + 2) / τ)

theorem logDifferenceLeafBound_nonneg (M H r : ℕ) {τ δ : ℝ} (hτ : 0 ≤ τ) (hδ : 0 ≤ δ) :
    0 ≤ logDifferenceLeafBound M H r τ δ := by
  unfold logDifferenceLeafBound
  positivity

theorem iteratedLogarithmic_sum_uniform_bound {M N H r : ℕ} (hM : 0 < M) (hN : N ≤ M)
    (hs : List ℝ) (hlen : hs.length = r) (hhs : ∀ h ∈ hs, 1 ≤ h ∧ h ≤ H)
    {τ δ : ℝ} (hτ : 0 < τ) (hδ : 0 < δ) :
    ‖∑ n ∈ Finset.range N, oscillatoryPhase 1 (iteratedLogarithmicPhase M hs τ n)‖ ≤
      logDifferenceLeafBound M H r τ δ := by
  have hhs0 : ∀ h ∈ hs, 0 ≤ h := fun h hh ↦ (by norm_num : (0 : ℝ) ≤ 1).trans (hhs h hh).1
  have hhsp : ∀ h ∈ hs, 0 < h := fun h hh ↦ (by norm_num : (0 : ℝ) < 1).trans_le (hhs h hh).1
  have hsum0 : 0 ≤ hs.sum := List.sum_nonneg hhs0
  have hsum : hs.sum ≤ (r : ℝ) * H := by
    simpa only [hlen, nsmul_eq_mul] using
      List.sum_le_card_nsmul hs (H : ℝ) (fun h hh ↦ (hhs h hh).2)
  have hprod : hs.prod ≤ (H : ℝ) ^ r := by
    have h := List.prod_map_le_prod_map₀ (fun x : ℝ ↦ x) (fun _ ↦ (H : ℝ))
      hhs0 (fun h hh ↦ (hhs h hh).2)
    simpa only [List.map_id', List.map_const', List.prod_replicate, hlen] using h
  have hcoef : differenceCoefficient 0 hs ≤ (r.factorial : ℝ) * (H : ℝ) ^ r := by
    rw [differenceCoefficient_zero, hlen]
    exact mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _)
  have hC : 1 ≤ differenceCoefficient 0 (1 :: hs) := by
    rw [differenceCoefficient_zero]
    have hfac : (1 : ℝ) ≤ ((1 :: hs).length.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos (1 :: hs).length
    have hprod1 : 1 ≤ ((1 : ℝ) :: hs).prod := by
      apply List.one_le_prod
      intro h hh
      rcases List.mem_cons.mp hh with rfl | hh
      · exact le_rfl
      · exact (hhs h hh).1
    exact one_le_mul_of_one_le_of_one_le hfac hprod1
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hN' : (N : ℝ) ≤ M := by exact_mod_cast hN
  have hB : (M + N + hs.sum + 1 : ℝ) ≤ 2 * M + r * H + 1 := by linarith
  have hC0 := differenceCoefficient_nonneg 0 hs hhs0
  have hK : ((⌈τ * differenceCoefficient 0 hs / (M : ℝ) ^ (r + 1)⌉₊ : ℕ) + 2 : ℝ) ≤
      τ * r.factorial * (H : ℝ) ^ r / (M : ℝ) ^ (r + 1) + 3 := by
    have hceil := Nat.ceil_lt_add_one
      (by positivity : 0 ≤ τ * differenceCoefficient 0 hs / (M : ℝ) ^ (r + 1))
    have hc := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef hτ.le)
      (pow_nonneg hMp.le (r + 1))
    simp only [← mul_assoc] at hc
    linarith
  have hpart : 2 * δ * (M + N + hs.sum + 1 : ℝ) ^ (r + 2) /
      (τ * differenceCoefficient 0 (1 :: hs)) ≤
        2 * δ * (2 * M + r * H + 1 : ℝ) ^ (r + 2) / τ := by
    have hτC : τ ≤ τ * differenceCoefficient 0 (1 :: hs) := by nlinarith
    calc
      _ ≤ 2 * δ * (2 * M + r * H + 1 : ℝ) ^ (r + 2) /
          (τ * differenceCoefficient 0 (1 :: hs)) := by
        apply div_le_div_of_nonneg_right _ (by linarith)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hB _) (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hτ hτC
  have hb := iteratedLogarithmic_sum_spacing_bound hM hs hhsp N hτ hδ
  rw [hlen] at hb
  unfold logDifferenceLeafBound
  refine hb.trans (mul_le_mul hK (by linarith [hpart]) (by positivity) (by positivity))

end Erdos421
