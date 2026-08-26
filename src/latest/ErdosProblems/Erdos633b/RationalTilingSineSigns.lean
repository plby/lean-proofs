import ErdosProblems.Erdos633b.RationalSineNonzero
import ErdosProblems.Erdos633b.RationalAngleWeights
import ErdosProblems.Erdos633b.SinePolynomialCoordinates

/-! The necessary sine-product sign condition for every coprime conjugate
of an actual congruent-triangle tiling with commensurable tile angles.
All common weights, polynomial roots, and nonvanishing facts are proved. -/

namespace Erdos633b
namespace Tiling

theorem coprime_sine_product_positive {T : Triangle} {n : ℕ} (d : Tiling T n)
    (N : ℕ) (hN : 1 < N) (w a : Fin 3 → ℕ)
    (hw : ∀ i, d.tile.angle i = (w i : ℝ) * (Real.pi / N))
    (ha : ∀ i, T.angle i = (a i : ℝ) * (Real.pi / N))
    (hwp : ∀ i, 0 < w i ∧ w i < N) (hap : ∀ i, 0 < a i ∧ a i < N)
    (k : ℕ) (hk : k.Coprime (2 * N)) :
    0 < (Real.sin (k * d.tile.angle 0) * Real.sin (k * d.tile.angle 1) *
      Real.sin (k * d.tile.angle 2)) *
      (Real.sin (k * T.angle 0) * Real.sin (k * T.angle 1) * Real.sin (k * T.angle 2)) := by
  have hkN : k.Coprime N := Nat.Coprime.of_dvd_right (dvd_mul_left N 2) hk
  obtain ⟨f, hf, hm, ht, ht'⟩ := cosine_pi_common_minpoly N k (by omega) hk
  have hpos := d.conjugate_weight_sine_product_positive
    (Real.pi / N) (k * (Real.pi / N)) (sine_pi_div_ne_zero N hN)
    (sine_coprime_pi_div_ne_zero N k hN hkN) w a hw ha f hf hm ht ht'
    (fun i => sine_weight_coprime_ne_zero N k (w i) (by omega) hkN (hwp i).1 (hwp i).2)
    (sine_weight_coprime_ne_zero N k (a 0) (by omega) hkN (hap 0).1 (hap 0).2)
  simpa only [hw, ha, mul_left_comm (k : ℝ)] using hpos

theorem commensurable_sine_product_positive {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hrat : ∀ i, IsRational (d.tile.angle i / Real.pi)) :
    ∃ N : ℕ, 3 ≤ N ∧ ∃ w a : Fin 3 → ℕ,
      (∀ i, d.tile.angle i = (w i : ℝ) * (Real.pi / N)) ∧
      (∀ i, T.angle i = (a i : ℝ) * (Real.pi / N)) ∧
      (∀ i, 0 < w i ∧ w i < N) ∧ (∀ i, 0 < a i ∧ a i < N) ∧
      ∑ i, w i = N ∧ ∑ i, a i = N ∧
      ∀ k : ℕ, k.Coprime (2 * N) →
        0 < (Real.sin (k * d.tile.angle 0) * Real.sin (k * d.tile.angle 1) *
          Real.sin (k * d.tile.angle 2)) *
          (Real.sin (k * T.angle 0) * Real.sin (k * T.angle 1) * Real.sin (k * T.angle 2)) := by
  obtain ⟨N, hN, w, a, hw, ha, hwp, hap, hws, has⟩ :=
    d.common_positive_integer_angle_weights hrat
  exact ⟨N, hN, w, a, hw, ha, hwp, hap, hws, has,
    d.coprime_sine_product_positive N (by omega) w a hw ha hwp hap⟩

end Tiling
end Erdos633b
