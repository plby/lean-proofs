import ErdosProblems.Erdos633b.RationalTilingSineSigns
import ErdosProblems.Erdos633b.TriangleResidueParity

/-! The integer residue condition for actual congruent-triangle tilings,
proved from geometric area and boundaries through cyclotomic conjugacy. -/

namespace Erdos633b.Tiling

theorem coprime_angle_residue_sum_eq {T : Triangle} {n : ℕ} (d : Tiling T n)
    (N : ℕ) (hN : 1 < N) (w a : Fin 3 → ℕ)
    (hw : ∀ i, d.tile.angle i = (w i : ℝ) * (Real.pi / N))
    (ha : ∀ i, T.angle i = (a i : ℝ) * (Real.pi / N))
    (hwp : ∀ i, 0 < w i ∧ w i < N) (hap : ∀ i, 0 < a i ∧ a i < N)
    (hws : ∑ i, w i = N) (has : ∑ i, a i = N)
    (k : ℕ) (hk : k.Coprime (2 * N)) : angleResidueSum N k w = angleResidueSum N k a := by
  apply residue_sums_eq_of_sine_products_pos N k (by omega)
    (Nat.Coprime.of_dvd_right (dvd_mul_left N 2) hk) w a hwp hap hws has
  have hh := d.coprime_sine_product_positive N hN w a hw ha hwp hap k hk
  simpa only [hw, ha, angleWeightSineProduct] using hh

theorem commensurable_angle_residue_condition {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hrat : ∀ i, IsRational (d.tile.angle i / Real.pi)) :
    ∃ N : ℕ, 3 ≤ N ∧ ∃ w a : Fin 3 → ℕ,
      (∀ i, d.tile.angle i = (w i : ℝ) * (Real.pi / N)) ∧
      (∀ i, T.angle i = (a i : ℝ) * (Real.pi / N)) ∧
      (∀ i, 0 < w i ∧ w i < N) ∧ (∀ i, 0 < a i ∧ a i < N) ∧
      ∑ i, w i = N ∧ ∑ i, a i = N ∧
      ∀ k : ℕ, k.Coprime (2 * N) → angleResidueSum N k w = angleResidueSum N k a := by
  obtain ⟨N, hN, w, a, hw, ha, hwp, hap, hws, has⟩ :=
    d.common_positive_integer_angle_weights hrat
  exact ⟨N, hN, w, a, hw, ha, hwp, hap, hws, has,
    d.coprime_angle_residue_sum_eq N (by omega) w a hw ha hwp hap hws has⟩

end Erdos633b.Tiling
