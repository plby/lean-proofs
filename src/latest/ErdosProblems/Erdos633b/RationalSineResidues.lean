import ErdosProblems.Erdos633b.RationalSineNonzero

/-! Exact quotient and remainder formulas for rational-angle sines,
including the two possible residue sums of a triangle's angle weights. -/

namespace Erdos633b

def angleResidueSum (N k : ℕ) (w : Fin 3 → ℕ) : ℕ :=
  (k * w 0) % N + (k * w 1) % N + (k * w 2) % N

def angleQuotientSum (N k : ℕ) (w : Fin 3 → ℕ) : ℕ :=
  (k * w 0) / N + (k * w 1) / N + (k * w 2) / N

theorem weight_remainder_pos (N k m : ℕ) (hk : k.Coprime N)
    (hm : 0 < m) (hmN : m < N) : 0 < (k * m) % N := by
  by_contra hn
  have hz : (k * m) % N = 0 := by omega
  have hd : N ∣ k * m := Nat.dvd_of_mod_eq_zero hz
  have hdm : N ∣ m := hk.symm.dvd_of_dvd_mul_left hd
  exact (Nat.not_dvd_of_pos_of_lt hm hmN) hdm

theorem weight_remainder_sine_pos (N k m : ℕ) (hN : 0 < N) (hk : k.Coprime N)
    (hm : 0 < m) (hmN : m < N) :
    0 < Real.sin (((k * m) % N : ℕ) * (Real.pi / N)) := by
  have hr := weight_remainder_pos N k m hk hm hmN
  have hrN := Nat.mod_lt (k * m) hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hr' : (0 : ℝ) < (((k * m) % N : ℕ) : ℝ) := by exact_mod_cast hr
  have hrN' : (((k * m) % N : ℕ) : ℝ) < N := by exact_mod_cast hrN
  apply Real.sin_pos_of_pos_of_lt_pi (mul_pos hr' (div_pos Real.pi_pos hN'))
  rw [← mul_div_assoc, div_lt_iff₀ hN']
  nlinarith [Real.pi_pos]

theorem sine_weight_quotient_remainder (N k m : ℕ) (hN : 0 < N) :
    Real.sin ((k : ℝ) * (m * (Real.pi / N))) =
      (-1 : ℝ) ^ (k * m / N) * Real.sin (((k * m) % N : ℕ) * (Real.pi / N)) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hdiv : (k : ℝ) * m = (((k * m) % N : ℕ) : ℝ) +
      (N : ℝ) * ((k * m / N : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div (k * m) N).symm
  have he : (k : ℝ) * (m * (Real.pi / N)) =
      (((k * m) % N : ℕ) : ℝ) * (Real.pi / N) +
        ((k * m / N : ℕ) : ℝ) * Real.pi := by
    rw [← mul_assoc, hdiv]
    field_simp
  rw [he, Real.sin_add_nat_mul_pi]

theorem angle_quotient_residue_sum (N k : ℕ) (w : Fin 3 → ℕ)
    (hw : ∑ i, w i = N) : angleResidueSum N k w + N * angleQuotientSum N k w = k * N := by
  have h0 := Nat.mod_add_div (k * w 0) N
  have h1 := Nat.mod_add_div (k * w 1) N
  have h2 := Nat.mod_add_div (k * w 2) N
  have hs : k * w 0 + k * w 1 + k * w 2 = k * N := by
    rw [← Nat.mul_add, ← Nat.mul_add]
    congr 1
    simpa only [Fin.sum_univ_three] using hw
  dsimp only [angleResidueSum, angleQuotientSum]
  nlinarith

theorem angle_residue_sum_cases (N k : ℕ) (hN : 0 < N) (hk : k.Coprime N)
    (w : Fin 3 → ℕ) (hp : ∀ i, 0 < w i ∧ w i < N) (hw : ∑ i, w i = N) :
    angleResidueSum N k w = N ∨ angleResidueSum N k w = 2 * N := by
  have hr0 := weight_remainder_pos N k (w 0) hk (hp 0).1 (hp 0).2
  have hr1 := weight_remainder_pos N k (w 1) hk (hp 1).1 (hp 1).2
  have hr2 := weight_remainder_pos N k (w 2) hk (hp 2).1 (hp 2).2
  have hl0 := Nat.mod_lt (k * w 0) hN
  have hl1 := Nat.mod_lt (k * w 1) hN
  have hl2 := Nat.mod_lt (k * w 2) hN
  have hpos : 0 < angleResidueSum N k w := by dsimp only [angleResidueSum]; omega
  have hlt : angleResidueSum N k w < 3 * N := by dsimp only [angleResidueSum]; omega
  have he := angle_quotient_residue_sum N k w hw
  have hd : N ∣ angleResidueSum N k w := by
    apply (Nat.dvd_add_iff_left (dvd_mul_right N (angleQuotientSum N k w))).mpr
    rw [he]
    exact dvd_mul_left N k
  obtain ⟨r, hr⟩ := hd
  have hrl : 0 < r := by nlinarith
  have hru : r < 3 := by nlinarith
  have hr12 : r = 1 ∨ r = 2 := by omega
  rcases hr12 with rfl | rfl
  · left; simpa using hr
  · right; simpa [Nat.mul_comm] using hr

end Erdos633b
