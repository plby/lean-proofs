import ErdosProblems.Erdos587.IteratedCenteredMean
import ErdosProblems.Erdos587.FresnelSeries

/-!
# A power-separated modulus condition for centered means

The explicit small-divisor cutoff can be chosen whenever the modulus is
below the ambient product by the fixed exponent `2/(4^j)`.
-/

open scoped BigOperators

namespace Erdos587

lemma centered_root_cutoff_conditions (j X q : ℕ) (hX : 0 < X)
    (hroot : 3 ≤ (X : ℝ) ^ (1 / (4 ^ j : ℕ) : ℝ))
    (hq : (q : ℝ) ≤ (X : ℝ) ^ (1 - 2 / (4 ^ j : ℕ) : ℝ)) :
    ∃ D : ℕ, 3 ≤ D ∧ q - 1 ≤ X ∧ q * D ≤ X ∧ X ≤ D ^ (4 ^ j) := by
  let k := 4 ^ j
  let y : ℝ := (X : ℝ) ^ (1 / (k : ℝ))
  let D := ⌊y ^ 2⌋₊
  have hk : 0 < k := pow_pos (by norm_num) _
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hy3 : 3 ≤ y := hroot
  have hy0 : 0 ≤ y := by linarith
  have hDlo : y ≤ (D : ℝ) := by
    have hf := Nat.lt_floor_add_one (y ^ 2)
    change y ^ 2 < (D : ℝ) + 1 at hf
    nlinarith
  have hDhi : (D : ℝ) ≤ y ^ 2 := Nat.floor_le (sq_nonneg y)
  have hD3 : 3 ≤ D := by exact_mod_cast hy3.trans hDlo
  have hyk : y ^ k = (X : ℝ) := by
    dsimp only [y]
    rw [← Real.rpow_mul_natCast hXR.le, div_mul_cancel₀ _ hkR.ne', Real.rpow_one]
  have hy2 : y ^ 2 = (X : ℝ) ^ (2 / (k : ℝ)) := by
    dsimp only [y]
    rw [← Real.rpow_mul_natCast hXR.le]
    congr 1
    push_cast
    ring
  have hqDreal : (q : ℝ) * D ≤ X := by
    calc
      _ ≤ (X : ℝ) ^ (1 - 2 / (k : ℝ)) * y ^ 2 :=
        mul_le_mul hq hDhi (Nat.cast_nonneg D) (Real.rpow_nonneg hXR.le _)
      _ = X := by rw [hy2, ← Real.rpow_add hXR]; ring_nf; rw [Real.rpow_one]
  have hqD : q * D ≤ X := by exact_mod_cast hqDreal
  have hqX : q ≤ X := by
    calc
      q = q * 1 := (mul_one q).symm
      _ ≤ q * D := Nat.mul_le_mul_left q (by omega)
      _ ≤ X := hqD
  have hsize : X ≤ D ^ k := by
    have hh := pow_le_pow_left₀ hy0 hDlo k
    rw [hyk] at hh
    exact_mod_cast hh
  exact ⟨D, hD3, (Nat.sub_le q 1).trans hqX, hqD, hsize⟩

theorem exists_centered_quadratic_mean_of_power_margin (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ O : ℕ, 0 < O ∧ ∀ (a q M L : ℕ),
      let X := 2 * M * L
      a.Coprime q → 0 < q → 0 < X →
        3 ≤ (X : ℝ) ^ (1 / (4 ^ j : ℕ) : ℝ) →
        (q : ℝ) ≤ (X : ℝ) ^ (1 - 2 / (4 ^ j : ℕ) : ℝ) →
        ∀ (s : ℕ → ℤ) (l : ℕ → ℕ), (∀ m ∈ Finset.Icc 1 M, l m ≤ L) →
          (∑ m ∈ Finset.Icc 1 M,
            ‖centeredQuadraticInterval q ((a * m : ℕ) : ℤ) (s m) (l m)‖ ^ 2) ≤
              C * M * L * Real.log (X : ℝ) ^ O := by
  obtain ⟨C, hC, O, hO, hmean⟩ := exists_iterated_centered_quadratic_mean_bound j
  refine ⟨C, hC, O, hO, ?_⟩
  intro a q M L
  dsimp only
  intro ha hq hX hroot hmargin s l hl
  obtain ⟨D, hD, hqX, hqD, hsize⟩ := centered_root_cutoff_conditions j (2 * M * L) q hX hroot hmargin
  exact hmean a q M L D ha hq hD hqX hqD hsize s l hl

theorem exists_centered_quadratic_first_mean_of_power_margin (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ O : ℕ, 0 < O ∧ ∀ (a q M L : ℕ),
      let X := 2 * M * L
      a.Coprime q → 0 < q → 0 < X →
        3 ≤ (X : ℝ) ^ (1 / (4 ^ j : ℕ) : ℝ) →
        (q : ℝ) ≤ (X : ℝ) ^ (1 - 2 / (4 ^ j : ℕ) : ℝ) →
        ∀ (s : ℕ → ℤ) (l : ℕ → ℕ), (∀ m ∈ Finset.Icc 1 M, l m ≤ L) →
          (∑ m ∈ Finset.Icc 1 M,
            ‖centeredQuadraticInterval q ((a * m : ℕ) : ℤ) (s m) (l m)‖) ≤
              C * M * Real.sqrt L * Real.log (X : ℝ) ^ O := by
  obtain ⟨C, hC, O, hO, hmean⟩ := exists_centered_quadratic_mean_of_power_margin j
  refine ⟨C + 1, by positivity, O, hO, ?_⟩
  intro a q M L
  dsimp only
  let X := 2 * M * L
  intro ha hq hX hroot hmargin s l hl
  have hsq := hmean a q M L ha hq hX hroot hmargin s l hl
  obtain ⟨D, hD, _, hqD, _⟩ := centered_root_cutoff_conditions j X q hX hroot hmargin
  have hX3 : 3 ≤ X := by
    apply hD.trans
    calc
      D = 1 * D := (one_mul D).symm
      _ ≤ q * D := Nat.mul_le_mul_right D hq
      _ ≤ X := hqD
  have hF : 1 ≤ Real.log (X : ℝ) ^ O := one_le_pow₀ (one_le_log_nat_of_three_le hX3)
  have hcard : (Finset.Icc 1 M).card = M := by simp
  calc
    _ ≤ Real.sqrt (((Finset.Icc 1 M).card : ℝ) *
        ∑ m ∈ Finset.Icc 1 M,
          ‖centeredQuadraticInterval q ((a * m : ℕ) : ℤ) (s m) (l m)‖ ^ 2) :=
      sum_norm_le_sqrt_card_mul_sum_sq _ _
    _ ≤ Real.sqrt (((Finset.Icc 1 M).card : ℝ) *
        (C * M * L * Real.log (X : ℝ) ^ O)) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _))
    _ ≤ (C + 1) * M * Real.sqrt L * Real.log (X : ℝ) ^ O :=
      sqrt_card_reciprocal_mean_le hC.le hF (by rw [hcard]; omega)

end Erdos587
