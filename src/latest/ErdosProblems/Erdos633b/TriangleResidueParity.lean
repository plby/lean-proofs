import ErdosProblems.Erdos633b.RationalSineResidues

/-! A positive product of two triangle sine products forces equality
of their integer residue sums. No bound on the common denominator is used. -/

namespace Erdos633b

noncomputable def angleWeightSineProduct (N k : ℕ) (w : Fin 3 → ℕ) : ℝ :=
  Real.sin (k * (w 0 * (Real.pi / N))) * Real.sin (k * (w 1 * (Real.pi / N))) *
    Real.sin (k * (w 2 * (Real.pi / N)))

noncomputable def angleResidueSineProduct (N k : ℕ) (w : Fin 3 → ℕ) : ℝ :=
  Real.sin (((k * w 0) % N : ℕ) * (Real.pi / N)) *
    Real.sin (((k * w 1) % N : ℕ) * (Real.pi / N)) *
    Real.sin (((k * w 2) % N : ℕ) * (Real.pi / N))

theorem angle_residue_sine_product_pos (N k : ℕ) (hN : 0 < N) (hk : k.Coprime N)
    (w : Fin 3 → ℕ) (hp : ∀ i, 0 < w i ∧ w i < N) :
    0 < angleResidueSineProduct N k w :=
  mul_pos (mul_pos (weight_remainder_sine_pos N k (w 0) hN hk (hp 0).1 (hp 0).2)
    (weight_remainder_sine_pos N k (w 1) hN hk (hp 1).1 (hp 1).2))
    (weight_remainder_sine_pos N k (w 2) hN hk (hp 2).1 (hp 2).2)

theorem angle_sine_product_quotient_factor (N k : ℕ) (hN : 0 < N) (w : Fin 3 → ℕ) :
    angleWeightSineProduct N k w =
      (-1 : ℝ) ^ angleQuotientSum N k w * angleResidueSineProduct N k w := by
  dsimp only [angleWeightSineProduct, angleQuotientSum, angleResidueSineProduct]
  rw [sine_weight_quotient_remainder N k (w 0) hN,
    sine_weight_quotient_remainder N k (w 1) hN,
    sine_weight_quotient_remainder N k (w 2) hN]
  simp only [pow_add]
  ring

theorem even_quotient_sum_of_sine_products_pos (N k : ℕ) (hN : 0 < N) (hk : k.Coprime N)
    (w a : Fin 3 → ℕ) (hw : ∀ i, 0 < w i ∧ w i < N) (ha : ∀ i, 0 < a i ∧ a i < N)
    (hpos : 0 < angleWeightSineProduct N k w * angleWeightSineProduct N k a) :
    Even (angleQuotientSum N k w + angleQuotientSum N k a) := by
  have hred := mul_pos (angle_residue_sine_product_pos N k hN hk w hw)
    (angle_residue_sine_product_pos N k hN hk a ha)
  have he : angleWeightSineProduct N k w * angleWeightSineProduct N k a =
      (-1 : ℝ) ^ (angleQuotientSum N k w + angleQuotientSum N k a) *
        (angleResidueSineProduct N k w * angleResidueSineProduct N k a) := by
    rw [angle_sine_product_quotient_factor N k hN w,
      angle_sine_product_quotient_factor N k hN a, pow_add]
    ring
  rw [he] at hpos
  by_contra hn
  have hodd := Nat.not_even_iff_odd.mp hn
  have hh : (-1 : ℝ) ^ (angleQuotientSum N k w + angleQuotientSum N k a) = -1 :=
    hodd.neg_one_pow
  rw [hh, neg_one_mul] at hpos
  linarith

theorem residue_sums_eq_of_even_quotients (N k : ℕ) (hN : 0 < N) (hk : k.Coprime N)
    (w a : Fin 3 → ℕ) (hw : ∀ i, 0 < w i ∧ w i < N) (ha : ∀ i, 0 < a i ∧ a i < N)
    (hws : ∑ i, w i = N) (has : ∑ i, a i = N)
    (heven : Even (angleQuotientSum N k w + angleQuotientSum N k a)) :
    angleResidueSum N k w = angleResidueSum N k a := by
  have hwq := angle_quotient_residue_sum N k w hws
  have haq := angle_quotient_residue_sum N k a has
  obtain ⟨b, hb⟩ := heven
  rcases angle_residue_sum_cases N k hN hk w hw hws with hw1 | hw2 <;>
    rcases angle_residue_sum_cases N k hN hk a ha has with ha1 | ha2
  · exact hw1.trans ha1.symm
  · rw [hw1] at hwq
    rw [ha2] at haq
    have hqw : angleQuotientSum N k w + 1 = k := by nlinarith
    have hqa : angleQuotientSum N k a + 2 = k := by nlinarith
    omega
  · rw [hw2] at hwq
    rw [ha1] at haq
    have hqw : angleQuotientSum N k w + 2 = k := by nlinarith
    have hqa : angleQuotientSum N k a + 1 = k := by nlinarith
    omega
  · exact hw2.trans ha2.symm

theorem residue_sums_eq_of_sine_products_pos (N k : ℕ) (hN : 0 < N) (hk : k.Coprime N)
    (w a : Fin 3 → ℕ) (hw : ∀ i, 0 < w i ∧ w i < N) (ha : ∀ i, 0 < a i ∧ a i < N)
    (hws : ∑ i, w i = N) (has : ∑ i, a i = N)
    (hpos : 0 < angleWeightSineProduct N k w * angleWeightSineProduct N k a) :
    angleResidueSum N k w = angleResidueSum N k a :=
  residue_sums_eq_of_even_quotients N k hN hk w a hw ha hws has
    (even_quotient_sum_of_sine_products_pos N k hN hk w a hw ha hpos)

end Erdos633b
