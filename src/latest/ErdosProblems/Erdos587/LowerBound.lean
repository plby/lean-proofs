import Mathlib

/-! The unconditional cube-root lower bound from the first theorem of `tex/587.tex`. -/

open scoped BigOperators

namespace Erdos587

theorem prime_multiples_square_sum_free {p k : ℕ} (hp : p.Prime) (hk : k ^ 2 < p) :
    let A := (Finset.Icc 1 k).image (fun i => p * i)
    A.card = k ∧ ∀ S ⊆ A, S.Nonempty → ¬ IsSquare (∑ a ∈ S, a) := by
  classical
  let A := (Finset.Icc 1 k).image (fun i => p * i)
  have hcard : A.card = k := by
    rw [Finset.card_image_of_injective _ (fun _ _ heq => Nat.eq_of_mul_eq_mul_left hp.pos heq)]
    simp
  refine ⟨hcard, ?_⟩
  intro S hSA hS hsq
  have hdiv : p ∣ ∑ a ∈ S, a := by
    apply Finset.dvd_sum
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hSA ha)
    exact dvd_mul_right _ _
  have hpos : 0 < ∑ a ∈ S, a := by
    apply Finset.sum_pos
    · intro a ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hSA ha)
      exact Nat.mul_pos hp.pos (Finset.mem_Icc.mp hi).1
    · exact hS
  have hupper : ∑ a ∈ S, a < p ^ 2 := by
    calc
      ∑ a ∈ S, a ≤ ∑ a ∈ A, a := Finset.sum_le_sum_of_subset hSA
      _ ≤ ∑ _a ∈ A, p * k := by
        apply Finset.sum_le_sum
        intro a ha
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
        exact Nat.mul_le_mul_left p (Finset.mem_Icc.mp hi).2
      _ = p * k ^ 2 := by simp [hcard]; ring
      _ < p ^ 2 := by nlinarith [Nat.mul_lt_mul_of_pos_left hk hp.pos]
  obtain ⟨z, hz⟩ := hsq
  have hzpos : 0 < z := by nlinarith
  have hpz : p ∣ z := hp.dvd_of_dvd_pow (n := 2) (by simpa only [pow_two, ← hz] using hdiv)
  have hzge := Nat.le_of_dvd hzpos hpz
  nlinarith

theorem exists_cube_root_square_sum_free (N : ℕ) (hN : 64 ≤ N) :
    ∃ A ⊆ Finset.Icc 1 N,
      (N : ℝ) ^ (1 / 3 : ℝ) / 4 ≤ A.card ∧
      ∀ S ⊆ A, S.Nonempty → ¬ IsSquare (∑ a ∈ S, a) := by
  let r : ℝ := (N : ℝ) ^ (1 / 3 : ℝ)
  have hr0 : 0 ≤ r := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hrpow : r ^ 3 = N := by
    dsimp [r]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg N)]
    norm_num
  have hr4 : 4 ≤ r := by
    by_contra hnot
    have hh : r ^ 3 < (4 : ℝ) ^ 3 :=
      pow_lt_pow_left₀ (lt_of_not_ge hnot) hr0 (by norm_num)
    have hn : (64 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  let k : ℕ := ⌊r / 2⌋₊
  have hkreal : (k : ℝ) ≤ r / 2 := Nat.floor_le (by positivity)
  have hnext : r / 2 < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hk2 : 2 ≤ k := by
    have hh : (2 : ℝ) ≤ k := by
      exact_mod_cast (Nat.le_floor (by linarith : (2 : ℝ) ≤ r / 2))
    exact_mod_cast hh
  have hklower : r / 4 ≤ (k : ℝ) := by
    have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    linarith
  have hkp : 2 * k ^ 3 ≤ N := by
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 * k)
      (show 2 * (k : ℝ) ≤ r by linarith) 3
    have hcast : (2 : ℝ) * (k : ℝ) ^ 3 ≤ N := by nlinarith
    exact_mod_cast hcast
  obtain ⟨p, hp, hpk, hpbound⟩ := Nat.exists_prime_lt_and_le_two_mul (k ^ 2) (by positivity)
  let A := (Finset.Icc 1 k).image (fun i => p * i)
  obtain ⟨hcard, hfree⟩ := prime_multiples_square_sum_free hp hpk
  refine ⟨A, ?_, ?_, hfree⟩
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    refine Finset.mem_Icc.mpr ⟨Nat.mul_pos hp.pos (Finset.mem_Icc.mp hi).1, ?_⟩
    calc
      p * i ≤ p * k := Nat.mul_le_mul_left p (Finset.mem_Icc.mp hi).2
      _ ≤ (2 * k ^ 2) * k := Nat.mul_le_mul_right k hpbound
      _ = 2 * k ^ 3 := by ring
      _ ≤ N := hkp
  · change r / 4 ≤ (A.card : ℝ)
    rw [hcard]
    exact hklower

end Erdos587
