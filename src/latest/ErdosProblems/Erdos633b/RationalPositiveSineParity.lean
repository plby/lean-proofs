import ErdosProblems.Erdos633b.ConjugateBoundarySigns
import ErdosProblems.Erdos633b.TilingResidueCondition

/-! Exact integer tests for positive conjugate sines. This removes
trigonometric evaluation from the finite candidate filtering stage. -/

namespace Erdos633b

theorem sine_weight_pos_iff_even_quotient (N k m : ℕ) (hN : 0 < N)
    (hk : k.Coprime N) (hm : 0 < m) (hmN : m < N) :
    0 < Real.sin ((k : ℝ) * (m * (Real.pi / N))) ↔ Even (k * m / N) := by
  rw [sine_weight_quotient_remainder N k m hN]
  have hr := weight_remainder_sine_pos N k m hN hk hm hmN
  constructor
  · intro hp
    by_contra hn
    have he := (Nat.not_even_iff_odd.mp hn).neg_one_pow (α := ℝ)
    rw [he, neg_one_mul] at hp
    linarith
  · intro he
    rw [he.neg_one_pow, one_mul]
    exact hr

namespace Tiling

theorem coprime_even_outer_quotients {T : Triangle} {n : ℕ} (d : Tiling T n)
    (N : ℕ) (hN : 1 < N) (w a : Fin 3 → ℕ)
    (hw : ∀ i, d.tile.angle i = (w i : ℝ) * (Real.pi / N))
    (ha : ∀ i, T.angle i = (a i : ℝ) * (Real.pi / N))
    (hwp : ∀ i, 0 < w i ∧ w i < N) (hap : ∀ i, 0 < a i ∧ a i < N)
    (k : ℕ) (hk : k.Coprime (2 * N)) (ht : ∀ i, Even (k * w i / N)) :
    ∀ i, Even (k * a i / N) := by
  have hkN := Nat.Coprime.of_dvd_right (dvd_mul_left N 2) hk
  have htile (i : Fin 3) : 0 < Real.sin (k * d.tile.angle i) := by
    rw [hw i]
    exact (sine_weight_pos_iff_even_quotient N k (w i) (by omega) hkN
      (hwp i).1 (hwp i).2).mpr (ht i)
  have hh := d.coprime_positive_outer_sines N hN w a hw ha hwp hap k hk htile
  intro i
  apply (sine_weight_pos_iff_even_quotient N k (a i) (by omega) hkN
    (hap i).1 (hap i).2).mp
  simpa only [ha] using hh i

theorem coprime_integer_angle_tests {T : Triangle} {n : ℕ} (d : Tiling T n)
    (N : ℕ) (hN : 1 < N) (w a : Fin 3 → ℕ)
    (hw : ∀ i, d.tile.angle i = (w i : ℝ) * (Real.pi / N))
    (ha : ∀ i, T.angle i = (a i : ℝ) * (Real.pi / N))
    (hwp : ∀ i, 0 < w i ∧ w i < N) (hap : ∀ i, 0 < a i ∧ a i < N)
    (hws : ∑ i, w i = N) (has : ∑ i, a i = N)
    (k : ℕ) (hk : k.Coprime (2 * N)) :
    angleResidueSum N k w = angleResidueSum N k a ∧
      ((∀ i, Even (k * w i / N)) → ∀ i, Even (k * a i / N)) :=
  ⟨d.coprime_angle_residue_sum_eq N hN w a hw ha hwp hap hws has k hk,
    d.coprime_even_outer_quotients N hN w a hw ha hwp hap k hk⟩

end Tiling
end Erdos633b
