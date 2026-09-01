import ErdosProblems.Erdos491.AffineSieve

/-! # Numerical consequences of the finite affine sieve -/

open scoped BigOperators

namespace Erdos491

lemma affine_density_positive (Q : Finset ℕ) {H : ℕ}
    (hQ : Q.Nonempty) (hprime : ∀ q ∈ Q, q.Prime) (hH : 0 < H) :
    0 < ∑ q ∈ Q, (H : ℝ) / q := by
  apply Finset.sum_pos
  · intro q hq
    exact div_pos (Nat.cast_pos.mpr hH) (Nat.cast_pos.mpr (hprime q hq).pos)
  · exact hQ

lemma affine_density_linear_bound (Q : Finset ℕ) (H : ℕ) {R : ℝ}
    (hprime : ∀ q ∈ Q, q.Prime) (hR : ∀ q ∈ Q, (q : ℝ) ≤ R) :
    (H : ℝ) * Q.card ≤ R * ∑ q ∈ Q, (H : ℝ) / q := by
  calc
    _ = ∑ q ∈ Q, (q : ℝ) * ((H : ℝ) / q) := by
      have hterm (q : ℕ) (hq : q ∈ Q) : (q : ℝ) * ((H : ℝ) / q) = H := by
        have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hprime q hq).ne_zero
        field_simp
      rw [Finset.sum_congr rfl hterm]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ ∑ q ∈ Q, R * ((H : ℝ) / q) := by
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_right (hR q hq) (by positivity)
    _ = _ := (Finset.mul_sum _ _ _).symm

lemma sieve_scalar_bound {P T S μ R H : ℝ}
    (hμ : 0 < μ) (hH : 0 < H) (hS : 1 ≤ S)
    (hlinear : S * H ≤ R ^ 2 * μ)
    (hvar : P * μ ^ 2 ≤ T * μ + S + S ^ 2) :
    P ≤ T / μ + 2 * R ^ 4 / H ^ 2 := by
  have hratio : S / μ ≤ R ^ 2 / H := (div_le_div_iff₀ hμ hH).mpr hlinear
  have hratio0 : 0 ≤ S / μ := div_nonneg (by linarith) hμ.le
  have hsq : (S / μ) ^ 2 ≤ (R ^ 2 / H) ^ 2 :=
    pow_le_pow_left₀ hratio0 hratio 2
  have hSsq : S ≤ S ^ 2 := by nlinarith
  have hvar' : P * μ ^ 2 ≤ T * μ + 2 * S ^ 2 := by linarith
  calc
    P ≤ (T * μ + 2 * S ^ 2) / μ ^ 2 := (le_div_iff₀ (sq_pos_of_pos hμ)).mpr hvar'
    _ = T / μ + 2 * (S / μ) ^ 2 := by field_simp
    _ ≤ T / μ + 2 * (R ^ 2 / H) ^ 2 := by linarith
    _ = T / μ + 2 * R ^ 4 / H ^ 2 := by ring

theorem affine_avoidance_card_bound (Q P : Finset ℕ) {H T : ℕ} {R : ℝ}
    (hQ : Q.Nonempty) (hprime : ∀ q ∈ Q, q.Prime)
    (hH : 0 < H) (hHq : ∀ q ∈ Q, H < q) (hR : ∀ q ∈ Q, (q : ℝ) ≤ R)
    (hP : P ⊆ Finset.range T)
    (havoid : ∀ n ∈ P, ∀ q ∈ Q, ∀ u : ℕ, 1 ≤ u → u ≤ H → ¬ q ∣ n * u + 1) :
    (P.card : ℝ) ≤ (T : ℝ) / (∑ q ∈ Q, (H : ℝ) / q) + 2 * R ^ 4 / (H : ℝ) ^ 2 := by
  have hμ := affine_density_positive Q hQ hprime hH
  have hlin := affine_density_linear_bound Q H hprime hR
  have hsum : (∑ q ∈ Q, (q : ℝ)) ≤ R * Q.card := by
    calc
      _ ≤ ∑ _q ∈ Q, R := Finset.sum_le_sum fun q hq ↦ hR q hq
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
  obtain ⟨q₀, hq₀⟩ := hQ
  have hS : (1 : ℝ) ≤ ∑ q ∈ Q, (q : ℝ) := by
    have hsingle : (q₀ : ℝ) ≤ ∑ q ∈ Q, (q : ℝ) :=
      Finset.single_le_sum (fun q _ ↦ Nat.cast_nonneg q) hq₀
    have hq1 : (1 : ℝ) ≤ q₀ := by exact_mod_cast (hprime q₀ hq₀).one_le
    exact hq1.trans hsingle
  have hR0 : 0 ≤ R := (Nat.cast_nonneg q₀).trans (hR q₀ hq₀)
  apply sieve_scalar_bound hμ (Nat.cast_pos.mpr hH) hS
  · calc
      (∑ q ∈ Q, (q : ℝ)) * H ≤ (R * Q.card) * H :=
        mul_le_mul_of_nonneg_right hsum (Nat.cast_nonneg H)
      _ = R * ((H : ℝ) * Q.card) := by ring
      _ ≤ R * (R * ∑ q ∈ Q, (H : ℝ) / q) := mul_le_mul_of_nonneg_left hlin hR0
      _ = _ := by ring
  · exact affine_avoidance_second_moment Q P H T hprime hHq hP havoid

end Erdos491
