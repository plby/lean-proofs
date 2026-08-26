import ErdosProblems.Erdos491.SieveBounds

/-! # Dense sets cannot avoid all small affine cofactors -/

open Filter
open scoped BigOperators Topology

namespace Erdos491

lemma sieve_density_comparison {P Q T μ x X l A L dP dQ : ℝ}
    (hx : 0 < x) (hX : 0 < X) (hl : 0 ≤ l) (hμ : 0 < μ)
    (hA : 0 ≤ A) (hdQ : 0 < dQ)
    (hT : T ≤ A * x ^ 4) (hP : dP * x ^ 4 ≤ P * l) (hQ : dQ * x ≤ Q * l)
    (hlinear : X * Q ≤ L * x * μ)
    (hcard : P ≤ T / μ + 2 * (L * x) ^ 4 / X ^ 2) :
    dP ≤ (A * L / dQ) * (l ^ 2 / X) + 2 * L ^ 4 * (l / X ^ 2) := by
  have hcancel : x * (dQ * X) ≤ x * (L * l * μ) := by
    calc
      _ = X * (dQ * x) := by ring
      _ ≤ X * (Q * l) := mul_le_mul_of_nonneg_left hQ hX.le
      _ = (X * Q) * l := by ring
      _ ≤ (L * x * μ) * l := mul_le_mul_of_nonneg_right hlinear hl
      _ = _ := by ring
  have hinv : 1 / μ ≤ (L * l) / (dQ * X) := by
    apply (div_le_div_iff₀ hμ (mul_pos hdQ hX)).mpr
    simpa only [one_mul] using (mul_le_mul_iff_right₀ hx).mp hcancel
  have hupper : P ≤ (A * x ^ 4) * ((L * l) / (dQ * X)) +
      2 * (L * x) ^ 4 / X ^ 2 := by
    calc
      P ≤ T / μ + 2 * (L * x) ^ 4 / X ^ 2 := hcard
      _ ≤ (A * x ^ 4) / μ + 2 * (L * x) ^ 4 / X ^ 2 := by
        exact add_le_add (div_le_div_of_nonneg_right hT hμ.le) le_rfl
      _ = (A * x ^ 4) * (1 / μ) + 2 * (L * x) ^ 4 / X ^ 2 := by ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hinv
        (mul_nonneg hA (pow_nonneg hx.le _))) le_rfl
  have hfinal : x ^ 4 * dP ≤ x ^ 4 *
      ((A * L / dQ) * (l ^ 2 / X) + 2 * L ^ 4 * (l / X ^ 2)) := by
    calc
      _ = dP * x ^ 4 := by ring
      _ ≤ P * l := hP
      _ ≤ ((A * x ^ 4) * ((L * l) / (dQ * X)) +
          2 * (L * x) ^ 4 / X ^ 2) * l := mul_le_mul_of_nonneg_right hupper hl
      _ = _ := by field_simp
  exact (mul_le_mul_iff_right₀ (pow_pos hx 4)).mp hfinal

lemma tendsto_log_sq_div_nat :
    Tendsto (fun X : ℕ ↦ Real.log (X : ℝ) ^ 2 / (X : ℝ)) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (s := 1) (by norm_num)).tendsto_div_nhds_zero
  have h' : Tendsto (fun x : ℝ ↦ Real.log x ^ 2 / x) atTop (𝓝 0) := by
    simpa only [Real.rpow_two, Real.rpow_one] using h
  exact h'.comp tendsto_natCast_atTop_atTop

lemma tendsto_log_div_nat_sq :
    Tendsto (fun X : ℕ ↦ Real.log (X : ℝ) / (X : ℝ) ^ 2) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (r := 2) (by norm_num)).tendsto_div_nhds_zero
  have h' : Tendsto (fun x : ℝ ↦ Real.log x / x ^ 2) atTop (𝓝 0) := by
    simpa only [Real.rpow_two] using h
  exact h'.comp tendsto_natCast_atTop_atTop

/-- The low set lives at the fourth power of the high-prime scale. Cofactors
run from `1` through `X`; the fixed integer `k` may be arbitrarily large. -/
theorem not_dense_affine_avoidance (k L₁ L₂ : ℕ) {dP dQ : ℝ}
    (hdP : 0 < dP) (hdQ : 0 < dQ) :
    ¬ (∀ᶠ X : ℕ in atTop, ∃ P Q : Finset ℕ,
      (∀ q ∈ Q, q.Prime ∧ X < q ∧ q ≤ L₂ * X ^ k) ∧
      (P ⊆ Finset.range (L₁ * (X ^ k) ^ 4 + 1)) ∧
      (dP * ((X ^ k : ℕ) : ℝ) ^ 4 ≤ (P.card : ℝ) * Real.log (X : ℝ)) ∧
      (dQ * ((X ^ k : ℕ) : ℝ) ≤ (Q.card : ℝ) * Real.log (X : ℝ)) ∧
      (∀ n ∈ P, ∀ q ∈ Q, ∀ u : ℕ, 1 ≤ u → u ≤ X → ¬ q ∣ n * u + 1)) := by
  intro h
  have hineq : ∀ᶠ X : ℕ in atTop,
      dP ≤ (((L₁ : ℝ) + 1) * L₂ / dQ) * (Real.log (X : ℝ) ^ 2 / X) +
        2 * (L₂ : ℝ) ^ 4 * (Real.log (X : ℝ) / (X : ℝ) ^ 2) := by
    filter_upwards [h, eventually_ge_atTop (2 : ℕ)] with X hXdata hX2
    obtain ⟨P, Q, hprime, hP, hPdense, hQdense, havoid⟩ := hXdata
    have hX : 0 < X := by omega
    have hx : (0 : ℝ) < ((X ^ k : ℕ) : ℝ) := by positivity
    have hlog : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX)
    have hQ : Q.Nonempty := by
      by_contra he
      have heq : Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
      rw [heq, Finset.card_empty, Nat.cast_zero, zero_mul] at hQdense
      exact (not_le_of_gt (mul_pos hdQ hx)) hQdense
    have hpr : ∀ q ∈ Q, q.Prime := fun q hq ↦ (hprime q hq).1
    have hR : ∀ q ∈ Q, (q : ℝ) ≤ (L₂ : ℝ) * ((X ^ k : ℕ) : ℝ) := by
      intro q hq
      exact_mod_cast (hprime q hq).2.2
    have hcard := affine_avoidance_card_bound Q P hQ hpr hX
      (fun q hq ↦ (hprime q hq).2.1) hR hP havoid
    have hμ := affine_density_positive Q hQ hpr hX
    have hlinear := affine_density_linear_bound Q X hpr hR
    have hx1 : (1 : ℝ) ≤ ((X ^ k : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_pow k X (by omega : 1 ≤ X)
    have hT : ((L₁ * (X ^ k) ^ 4 + 1 : ℕ) : ℝ) ≤
        ((L₁ : ℝ) + 1) * ((X ^ k : ℕ) : ℝ) ^ 4 := by
      push_cast
      have hx4 : (1 : ℝ) ≤ ((X ^ k : ℕ) : ℝ) ^ 4 := one_le_pow₀ hx1
      push_cast at hx4
      nlinarith
    exact sieve_density_comparison hx (Nat.cast_pos.mpr hX) hlog hμ
      (by positivity) hdQ hT hPdense hQdense hlinear hcard
  have ht : Tendsto (fun X : ℕ ↦
      (((L₁ : ℝ) + 1) * L₂ / dQ) * (Real.log (X : ℝ) ^ 2 / X) +
        2 * (L₂ : ℝ) ^ 4 * (Real.log (X : ℝ) / (X : ℝ) ^ 2)) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_log_sq_div_nat.const_mul (((L₁ : ℝ) + 1) * L₂ / dQ)).add
        (tendsto_log_div_nat_sq.const_mul (2 * (L₂ : ℝ) ^ 4))
  exact (not_le_of_gt hdP) (ge_of_tendsto ht hineq)

end Erdos491
