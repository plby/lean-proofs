import ErdosProblems.Erdos421.RoughBuchstabMain
import ErdosProblems.Erdos421.SqrtBoundaryPrimeMass

/-! # Bounding the actual clipped cofactor main terms near the square-root boundary -/

namespace Erdos421

theorem rough_cofactor_correction_bounds (n : ℕ) {a b : ℝ} {p : ℕ}
    (hb : 1 < b) (hp : p.Prime) (hps : (p : ℝ) ≤ Real.sqrt b) :
    0 ≤ (b - a) * (finiteBuchstab n (logarithmicBuchstabArgument b p) /
      ((p : ℝ) * Real.log p)) - roughCountMain n (a / p) (b / p) p ∧
    (b - a) * (finiteBuchstab n (logarithmicBuchstabArgument b p) /
      ((p : ℝ) * Real.log p)) - roughCountMain n (a / p) (b / p) p ≤
      if a < (p : ℝ) ^ 2 then (b - a) / ((p : ℝ) * Real.log p) else 0 := by
  have hbp : 0 < b := by linarith
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpp : (0 : ℝ) < p := by linarith
  have hlp := Real.log_pos hp1
  have harg := logarithmicBuchstabArgument_antitone hb hp1 (hp1.trans_le hps) hps
  rw [logarithmicBuchstabArgument_sqrt hb] at harg
  have hf := finiteBuchstab_le_one n harg
  have hf0 := (finiteBuchstab_pos n (logarithmicBuchstabArgument b p)).le
  have hp2 := (Real.le_sqrt hpp.le hbp.le).mp hps
  rw [rough_cofactor_main_correction n hbp hp.two_le]
  refine ⟨by positivity, ?_⟩
  split_ifs with hpa
  · rw [max_eq_left (sub_nonneg.mpr hpa.le)]
    calc
      _ ≤ ((p : ℝ) ^ 2 - a) / ((p : ℝ) * Real.log p) :=
        mul_le_of_le_one_right (by positivity) hf
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (by positivity)
  · rw [max_eq_right (sub_nonpos.mpr (le_of_not_gt hpa)), zero_div, zero_mul]

theorem rough_boundary_correction_le (n z : ℕ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 1 < b) (hab : a ≤ b) :
    |(b - a) * (∑ p ∈ sievePrimes z (roughSquareCutoff b),
      finiteBuchstab n (logarithmicBuchstabArgument b p) / ((p : ℝ) * Real.log p)) -
        ∑ p ∈ sievePrimes z (roughSquareCutoff b), roughCountMain n (a / p) (b / p) p| ≤
      (b - a) * ∑ p ∈ primesInRealInterval (Real.sqrt a) (Real.sqrt b),
        1 / ((p : ℝ) * Real.log p) := by
  classical
  let P := sievePrimes z (roughSquareCutoff b)
  have hpoint : ∀ p ∈ P,
      0 ≤ (b - a) * (finiteBuchstab n (logarithmicBuchstabArgument b p) /
        ((p : ℝ) * Real.log p)) - roughCountMain n (a / p) (b / p) p ∧
      (b - a) * (finiteBuchstab n (logarithmicBuchstabArgument b p) /
        ((p : ℝ) * Real.log p)) - roughCountMain n (a / p) (b / p) p ≤
        if a < (p : ℝ) ^ 2 then (b - a) / ((p : ℝ) * Real.log p) else 0 := by
    intro p hp
    obtain ⟨hpp, _, hps⟩ := (mem_sievePrimes_square_cutoff b z p).mp hp
    exact rough_cofactor_correction_bounds n hb hpp hps
  have hsub : P.filter (fun p : ℕ ↦ a < (p : ℝ) ^ 2) ⊆
      primesInRealInterval (Real.sqrt a) (Real.sqrt b) := by
    intro p hp
    obtain ⟨hpP, hpa⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpp, _, hps⟩ := (mem_sievePrimes_square_cutoff b z p).mp hpP
    apply (mem_primesInRealInterval (Real.sqrt_nonneg a) (Real.sqrt_le_sqrt hab) p).mpr
    exact ⟨hpp, (Real.sqrt_lt ha (Nat.cast_nonneg p)).mpr hpa, hps⟩
  have hsum : (∑ p ∈ P.filter (fun p : ℕ ↦ a < (p : ℝ) ^ 2),
      (b - a) / ((p : ℝ) * Real.log p)) ≤
      ∑ p ∈ primesInRealInterval (Real.sqrt a) (Real.sqrt b),
        (b - a) / ((p : ℝ) * Real.log p) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro p hp hnot
    have hpp := (Finset.mem_filter.mp hp).2
    have hlog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hpp.one_lt)
    exact div_nonneg (sub_nonneg.mpr hab) (by positivity)
  change |(b - a) * (∑ p ∈ P, _) - ∑ p ∈ P, _| ≤ _
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib,
    abs_of_nonneg (Finset.sum_nonneg (fun p hp ↦ (hpoint p hp).1))]
  calc
    _ ≤ ∑ p ∈ P, if a < (p : ℝ) ^ 2 then (b - a) / ((p : ℝ) * Real.log p) else 0 :=
      Finset.sum_le_sum (fun p hp ↦ (hpoint p hp).2)
    _ = ∑ p ∈ P.filter (fun p : ℕ ↦ a < (p : ℝ) ^ 2), (b - a) / ((p : ℝ) * Real.log p) := by
      rw [Finset.sum_filter]
    _ ≤ _ := hsum
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p hp; ring

theorem rough_boundary_correction_log_saving {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ X₀ > 1, ∀ b : ℝ, X₀ ≤ b → ∀ a : ℝ, b / 2 ≤ a → a ≤ b → ∀ n z : ℕ,
      |(b - a) * (∑ p ∈ sievePrimes z (roughSquareCutoff b),
        finiteBuchstab n (logarithmicBuchstabArgument b p) / ((p : ℝ) * Real.log p)) -
          ∑ p ∈ sievePrimes z (roughSquareCutoff b), roughCountMain n (a / p) (b / p) p| ≤
        ε * b / (Real.log b) ^ A + 16 * (b - a) ^ 2 / (b * (Real.log b) ^ 2) := by
  obtain ⟨X₀, hX₀, hbound⟩ := sqrt_boundary_prime_mass hA hε
  refine ⟨X₀, hX₀, ?_⟩
  intro b hb a ha hab n z
  have hb1 := hX₀.trans_le hb
  exact (rough_boundary_correction_le n z (by linarith) hb1 hab).trans
    (hbound b hb a ha hab)

end Erdos421
