import ErdosProblems.Erdos633b.CoprimeResidueLift

/-! Every positive rational angle below pi/3 has a negative cosine at
some conjugate multiplier coprime to twice any common denominator. -/

namespace Erdos633b

theorem negative_cosine_conjugate (N m : ℕ) (hm : 0 < m) (hmN : 3 * m < N) :
    ∃ k : ℕ, k.Coprime (2 * N) ∧ Real.cos (k * (m * (Real.pi / N))) < 0 := by
  have hN : 0 < N := by omega
  have hG : 0 < m.gcd (2 * N) := Nat.gcd_pos_of_pos_left _ hm
  obtain ⟨g, j, D, hg, hjD, hmj, hND⟩ := Nat.exists_coprime' hG
  have hj : 0 < j := by
    by_contra h
    have hz : j = 0 := by omega
    rw [hz, zero_mul] at hmj
    omega
  have hmul : (6 * j) * g < D * g := by
    calc
      (6 * j) * g = 2 * (3 * m) := by rw [hmj]; ring
      _ < 2 * N := Nat.mul_lt_mul_of_pos_left hmN (by decide)
      _ = D * g := hND
  have h6j : 6 * j < D := Nat.lt_of_mul_lt_mul_right hmul
  have hD : 6 < D := by omega
  have hDM : D ∣ 2 * N := ⟨g, hND⟩
  obtain ⟨r, hr, hrl, hru⟩ := exists_coprime_middle_residue D hD
  obtain ⟨k, hk, he⟩ := coprime_multiplier_residue (2 * N) D j r (by omega) hDM hjD hr
  have hrD : r < D := by omega
  have hrem : (k * j) % D = r := by
    change (k * j) % D = r % D at he
    rwa [Nat.mod_eq_of_lt hrD] at he
  have hkj : k * j = r + D * (k * j / D) := by
    have hh := Nat.mod_add_div (k * j) D
    rw [hrem] at hh
    exact hh.symm
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
  have hmj' : (m : ℝ) = (j : ℝ) * g := by exact_mod_cast hmj
  have hND' : (2 : ℝ) * N = (D : ℝ) * g := by exact_mod_cast hND
  have hkj' : (k : ℝ) * j = (r : ℝ) + D * ((k * j / D : ℕ) : ℝ) := by exact_mod_cast hkj
  have hangle : (k : ℝ) * (m * (Real.pi / N)) =
      2 * Real.pi * r / D + ((k * j / D : ℕ) : ℝ) * (2 * Real.pi) := by
    apply (mul_right_cancel₀ hN')
    field_simp [hN', hD']
    linear_combination (k : ℝ) * (D : ℝ) * hmj' -
      (k : ℝ) * (j : ℝ) * hND' + 2 * (N : ℝ) * hkj'
  refine ⟨k, hk, ?_⟩
  rw [hangle, Real.cos_add_nat_mul_two_pi]
  exact cosine_middle_residue_neg D r (by omega) hrl hru

end Erdos633b
