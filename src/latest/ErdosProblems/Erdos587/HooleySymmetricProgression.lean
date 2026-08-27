import ErdosProblems.Erdos587.HooleyProgressionGcd

/-! # Delta means on symmetric intervals of signed errors -/

open scoped BigOperators

namespace Erdos587

lemma delta_sum_symmetric_interval (f : ℤ → ℝ) (T : ℕ) :
    (∑ t ∈ Finset.Icc (-(T : ℤ)) T, f t) =
      ∑ j ∈ Finset.Icc 1 (2 * T + 1), f ((j : ℤ) - (T + 1)) := by
  symm
  apply Finset.sum_bij (fun (j : ℕ) _ => (j : ℤ) - (T + 1))
  · intro j hj
    obtain ⟨hj1, hjT⟩ := Finset.mem_Icc.mp hj
    apply Finset.mem_Icc.mpr
    constructor <;> omega
  · intro j hj k hk heq
    omega
  · intro t ht
    obtain ⟨htlo, hthi⟩ := Finset.mem_Icc.mp ht
    have hnonneg : 0 ≤ t + T + 1 := by omega
    have heq := Int.toNat_of_nonneg hnonneg
    refine ⟨(t + T + 1).toNat, ?_, ?_⟩
    · apply Finset.mem_Icc.mpr
      constructor <;> omega
    · omega
  · intro j hj
    rfl

theorem exists_delta_symmetric_progression_mean (r : ℕ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ A B : ℤ, B ≠ 0 → ∀ X T : ℕ,
      2 ≤ X → 8 ≤ T → X ≤ (2 * T + 1) ^ r →
      (∀ t ∈ Finset.Icc (-(T : ℤ)) T, (A + B * t).natAbs ≤ X) →
      (∑ t ∈ Finset.Icc (-(T : ℤ)) T, (hooleyDelta (A + B * t).natAbs : ℝ)) ≤
        C * (Int.gcd A B).divisors.card * (2 * T + 1) *
          (max 1 (Real.log (Real.log (X : ℝ)))) ^ 6 := by
  obtain ⟨C, hC, hmean⟩ := exists_hooleyDelta_progression_mean r hr
  refine ⟨C, hC, ?_⟩
  intro A B hB X T hX hT hsize hvalue
  have hvalues (j : ℕ) (hj : j ∈ Finset.Icc 1 (2 * T + 1)) :
      (A - B * (T + 1) + B * j).natAbs ≤ X := by
    have hmem : (j : ℤ) - (T + 1) ∈ Finset.Icc (-(T : ℤ)) T := by
      obtain ⟨hj1, hjT⟩ := Finset.mem_Icc.mp hj
      apply Finset.mem_Icc.mpr
      constructor <;> omega
    have heq : A - B * (T + 1) + B * j = A + B * ((j : ℤ) - (T + 1)) := by ring
    rw [heq]
    exact hvalue _ hmem
  have h := hmean (A - B * (T + 1)) B hB X (2 * T + 1) hX (by omega) hsize hvalues
  rw [Int.gcd_sub_mul_left_left] at h
  rw [delta_sum_symmetric_interval]
  have hsum : (∑ j ∈ Finset.Icc 1 (2 * T + 1),
      (hooleyDelta (A + B * ((j : ℤ) - (T + 1))).natAbs : ℝ)) =
      ∑ j ∈ Finset.Icc 1 (2 * T + 1), (hooleyDelta (A - B * (T + 1) + B * j).natAbs : ℝ) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [show A + B * ((j : ℤ) - (T + 1)) = A - B * (T + 1) + B * j by ring]
  rw [hsum]
  exact h.trans_eq (by push_cast; ring)

theorem exists_delta_symmetric_error_mean (r : ℕ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ A B : ℤ, B ≠ 0 → ∀ X : ℕ, 2 ≤ X →
      ∀ T : ℝ, 8 ≤ T → X ≤ ⌊T⌋₊ ^ r →
      (∀ t : ℤ, |(t : ℝ)| ≤ T → (A + B * t).natAbs ≤ X) →
      ∀ E : Finset ℤ, (∀ t ∈ E, |(t : ℝ)| ≤ T) →
      (∑ t ∈ E, (hooleyDelta (A + B * t).natAbs : ℝ)) ≤
        C * (Int.gcd A B).divisors.card * T *
          (max 1 (Real.log (Real.log (X : ℝ)))) ^ 6 := by
  obtain ⟨C, hC, hmean⟩ := exists_delta_symmetric_progression_mean r hr
  refine ⟨3 * C, by positivity, ?_⟩
  intro A B hB X hX T hT hsize hvalue E hE
  have hT0 : 0 ≤ T := by linarith
  have hfloor : 8 ≤ ⌊T⌋₊ := Nat.le_floor hT
  have hfloorR := Nat.floor_le hT0
  have hsub : E ⊆ Finset.Icc (-(⌊T⌋₊ : ℤ)) ⌊T⌋₊ := by
    intro t ht
    have habs : (t.natAbs : ℝ) ≤ T := by
      rw [Nat.cast_natAbs, Int.cast_abs]
      exact hE t ht
    have hn := Nat.le_floor habs
    have hz : |t| ≤ (⌊T⌋₊ : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hn
    exact Finset.mem_Icc.mpr (abs_le.mp hz)
  have hvalues (t : ℤ) (ht : t ∈ Finset.Icc (-(⌊T⌋₊ : ℤ)) ⌊T⌋₊) :
      (A + B * t).natAbs ≤ X := by
    apply hvalue t
    have hz := abs_le.mpr (Finset.mem_Icc.mp ht)
    have hR : |(t : ℝ)| ≤ (⌊T⌋₊ : ℝ) := by exact_mod_cast hz
    exact hR.trans hfloorR
  have h := hmean A B hB X ⌊T⌋₊ hX hfloor
    (hsize.trans (Nat.pow_le_pow_left (by omega : ⌊T⌋₊ ≤ 2 * ⌊T⌋₊ + 1) r)) hvalues
  calc
    _ ≤ ∑ t ∈ Finset.Icc (-(⌊T⌋₊ : ℤ)) ⌊T⌋₊, (hooleyDelta (A + B * t).natAbs : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun t ht hnot => by positivity)
    _ ≤ C * (Int.gcd A B).divisors.card * (2 * (⌊T⌋₊ : ℝ) + 1) *
        (max 1 (Real.log (Real.log (X : ℝ)))) ^ 6 := h
    _ ≤ C * (Int.gcd A B).divisors.card * (3 * T) *
        (max 1 (Real.log (Real.log (X : ℝ)))) ^ 6 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    _ = _ := by ring

end Erdos587
