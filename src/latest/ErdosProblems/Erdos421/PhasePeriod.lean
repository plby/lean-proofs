import ErdosProblems.Erdos421.PhaseReciprocalPi

/-! # Reciprocal phase variation away from both ends of a period -/

namespace Erdos421

open Complex

theorem oscillatoryPhase_reflection (x : ℝ) :
    oscillatoryPhase 1 (2 * Real.pi - x) = starRingEnd ℂ (oscillatoryPhase 1 x) := by
  have heq : Complex.I * (2 * Real.pi - x : ℝ) =
      2 * Real.pi * Complex.I + starRingEnd ℂ (Complex.I * (x : ℂ)) := by
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat,
      map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  simp only [oscillatoryPhase, Complex.ofReal_one, mul_one]
  rw [heq, Complex.exp_add, Complex.exp_two_pi_mul_I, one_mul, Complex.exp_conj]

theorem phaseReciprocal_reflection (x : ℝ) :
    phaseReciprocal (2 * Real.pi - x) = starRingEnd ℂ (phaseReciprocal x) := by
  simp only [phaseReciprocal, oscillatoryPhase_reflection, map_inv₀, map_sub, map_one]

theorem phaseReciprocal_reflection_norm_sub (a b : ℝ) :
    ‖phaseReciprocal (2 * Real.pi - b) - phaseReciprocal (2 * Real.pi - a)‖ =
      ‖phaseReciprocal b - phaseReciprocal a‖ := by
  rw [phaseReciprocal_reflection, phaseReciprocal_reflection, ← map_sub, Complex.norm_conj]

theorem phaseReciprocal_variation_upper {a b : ℝ}
    (ha : Real.pi ≤ a) (hab : a ≤ b) (hb : b < 2 * Real.pi) :
    ‖phaseReciprocal b - phaseReciprocal a‖ ≤
      4 / (2 * Real.pi - b) - 4 / (2 * Real.pi - a) := by
  have h := phaseReciprocal_variation_pi (a := 2 * Real.pi - b) (b := 2 * Real.pi - a)
    (by linarith) (by linarith) (by linarith)
  rw [norm_sub_rev, phaseReciprocal_reflection_norm_sub] at h
  exact h

noncomputable def phaseVariationWeight (x : ℝ) : ℝ :=
  4 / x - 4 / (2 * Real.pi - x)

/-- The reciprocal-phase variation telescopes over the whole open period. -/
theorem phaseReciprocal_variation_period {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 2 * Real.pi) :
    ‖phaseReciprocal b - phaseReciprocal a‖ ≤
      phaseVariationWeight a - phaseVariationWeight b := by
  have hbpos := ha.trans_le hab
  have hap : 0 < 2 * Real.pi - a := by linarith
  have hbp : 0 < 2 * Real.pi - b := by linarith
  by_cases hbpi : b ≤ Real.pi
  · have h := phaseReciprocal_variation_pi ha hab hbpi
    have hi : 4 / (2 * Real.pi - a) ≤ 4 / (2 * Real.pi - b) :=
      div_le_div_of_nonneg_left (by norm_num) hbp (by linarith)
    unfold phaseVariationWeight
    linarith
  by_cases hapi : Real.pi ≤ a
  · have h := phaseReciprocal_variation_upper hapi hab hb
    have hi : 4 / b ≤ 4 / a := div_le_div_of_nonneg_left (by norm_num) ha hab
    unfold phaseVariationWeight
    linarith
  · have hleft := phaseReciprocal_variation_pi ha (by linarith : a ≤ Real.pi) le_rfl
    have hright := phaseReciprocal_variation_upper (a := Real.pi) le_rfl
      (by linarith : Real.pi ≤ b) hb
    have hsplit := norm_add_le (phaseReciprocal b - phaseReciprocal Real.pi)
      (phaseReciprocal Real.pi - phaseReciprocal a)
    rw [sub_add_sub_cancel] at hsplit
    have hpi : 2 * Real.pi - Real.pi = Real.pi := by ring
    rw [hpi] at hright
    have h1 : 4 / b ≤ 4 / Real.pi :=
      div_le_div_of_nonneg_left (by norm_num) Real.pi_pos (by linarith)
    have h2 : 4 / (2 * Real.pi - a) ≤ 4 / Real.pi :=
      div_le_div_of_nonneg_left (by norm_num) Real.pi_pos (by linarith)
    unfold phaseVariationWeight
    linarith

theorem phase_sub_one_ne_zero_period {x : ℝ} (hx : 0 < x) (hxpi : x < 2 * Real.pi) :
    oscillatoryPhase 1 x - 1 ≠ 0 := by
  by_cases h : x ≤ Real.pi
  · exact phase_sub_one_ne_zero_pi hx h
  · have hz := phase_sub_one_ne_zero_pi (x := 2 * Real.pi - x) (by linarith) (by linarith)
    intro heq
    apply hz
    have hxone := sub_eq_zero.mp heq
    rw [oscillatoryPhase_reflection, hxone, map_one, sub_self]

theorem phaseReciprocal_norm_le_period {x δ : ℝ} (hδ : 0 < δ)
    (hlo : δ ≤ x) (hhi : x ≤ 2 * Real.pi - δ) : ‖phaseReciprocal x‖ ≤ 2 / δ := by
  by_cases h : x ≤ Real.pi
  · exact (phaseReciprocal_norm_le_pi (hδ.trans_le hlo) h).trans
      (div_le_div_of_nonneg_left (by norm_num) hδ hlo)
  · have h' : δ ≤ 2 * Real.pi - x := by linarith
    have hb := phaseReciprocal_norm_le_pi (hδ.trans_le h') (by linarith : 2 * Real.pi - x ≤ Real.pi)
    rw [phaseReciprocal_reflection, Complex.norm_conj] at hb
    exact hb.trans (div_le_div_of_nonneg_left (by norm_num) hδ h')

end Erdos421
