import ErdosProblems.Erdos587.NonprimitiveRoots
import ErdosProblems.Erdos587.RootResidueInterval
import ErdosProblems.Erdos587.NonprimitiveRootWindow

/-! The nonprimitive long-side exit, using the reduced quadratic period. -/

namespace Erdos587

lemma exists_progression_coordinate_of_bounded_congruence {q n t H : ℕ} (hq : 0 < q)
    (hcong : n ≡ t [MOD q]) (hlo : t ≤ n) (hhi : n ≤ t + q * H) :
    ∃ x ≤ H, n = t + q * x := by
  have hdiv : q ∣ n - t := (Nat.modEq_iff_dvd' hlo).mp hcong.symm
  obtain ⟨x, hx⟩ := hdiv
  refine ⟨x, ?_, ?_⟩
  · apply Nat.le_of_mul_le_mul_left _ hq
    omega
  · omega

theorem exists_nonprimitive_long_side :
    ∃ A : ℝ, 0 < A ∧ ∀ (g t u v H J T : ℕ),
      0 < g → 0 < u → 0 < H → 0 < T → v.Coprime u →
      g * (t + u * H + v * J) ≤ T →
      A * Real.sqrt ((g.gcd u : ℝ) * u) ≤ J →
      4 * Real.sqrt T ≤ (H : ℝ) * (g.gcd u : ℝ) →
      ∃ x ≤ H, ∃ y ≤ J, ∃ z : ℕ, 0 < z ∧ z ^ 2 = g * (t + u * x + v * y) := by
  obtain ⟨A, hA, hresidue⟩ := exists_nonprimitive_quadratic_residue
  refine ⟨A, hA, ?_⟩
  intro g t u v H J T hg hu hH hT hvu hambient hJ hlong
  obtain ⟨y, hy, r, hr⟩ := hresidue g u v t J hu hvu hJ
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hd : 0 < g.gcd u := Nat.gcd_pos_of_pos_right g hu
  have hq : 0 < u / g.gcd u := Nat.div_pos
    (Nat.le_of_dvd hu (Nat.gcd_dvd_right g u)) hd
  have hambient' : (g : ℝ) * (((t : ℝ) + v * y) + u * H) ≤ T := by
    have hh : g * (t + v * y + u * H) ≤ T := by
      calc
        _ = g * (t + u * H + v * y) := by ring
        _ ≤ g * (t + u * H + v * J) := Nat.mul_le_mul_left g
          (Nat.add_le_add_left (Nat.mul_le_mul_left v hy) (t + u * H))
        _ ≤ T := hambient
    exact_mod_cast hh
  have hrootwidth := nonprimitive_root_window_length hgR
    (by positivity : (0 : ℝ) ≤ (t : ℝ) + v * y) (mul_pos huR hHR) hTR hambient'
  have hperiodwidth := reduced_period_root_window_budget hu hTR hlong
  obtain ⟨z, hzpos, hzlo, hzhi, hzmod⟩ := exists_positive_residue_in_real_interval hq r
    (Real.sqrt_nonneg (((t : ℝ) + v * y) / g)) (hperiodwidth.trans hrootwidth)
  have hcong : g * z ^ 2 ≡ t + v * y [MOD u] :=
    (quadratic_residue_reduced_period hu hzmod).trans hr
  obtain ⟨hlo, hhi⟩ := nonprimitive_root_window_square_bounds hgR
    (by positivity : (0 : ℝ) ≤ (t : ℝ) + v * y)
    (by positivity : (0 : ℝ) ≤ (u : ℝ) * H) (Nat.cast_nonneg z) hzlo hzhi
  have hloN : t + v * y ≤ g * z ^ 2 := by exact_mod_cast hlo
  have hhiN : g * z ^ 2 ≤ t + v * y + u * H := by exact_mod_cast hhi
  obtain ⟨x, hx, heq⟩ := exists_progression_coordinate_of_bounded_congruence hu hcong hloN hhiN
  refine ⟨x, hx, y, hy, g * z, Nat.mul_pos hg hzpos, ?_⟩
  calc
    (g * z) ^ 2 = g * (g * z ^ 2) := by ring
    _ = g * (t + v * y + u * x) := by rw [heq]
    _ = g * (t + u * x + v * y) := by ring

end Erdos587
