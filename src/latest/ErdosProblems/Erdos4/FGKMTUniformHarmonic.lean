import BoundedGaps.Maynard.CoprimeHarmonicErrorBound
import BoundedGaps.Maynard.ReciprocalTotientCorrectionEndpoint

/-!
# Harmonic estimates with a growing excluded modulus

The endpoint and the squarefree modulus are both unrestricted. The error
depends logarithmically on the modulus, so no fixed-modulus limiting
statement is used in the growing-dimensional sieve.
-/

open scoped BigOperators

namespace Erdos4.FGKMT

open BoundedGaps.Maynard

theorem harmonicDensity_nonneg (W : ℕ) : 0 ≤ coprimeHarmonicDensity W := by
  unfold coprimeHarmonicDensity
  positivity

theorem harmonicDensity_le_one {W : ℕ} (hW : 0 < W) : coprimeHarmonicDensity W ≤ 1 := by
  unfold coprimeHarmonicDensity
  apply (div_le_one (by exact_mod_cast hW)).mpr
  exact_mod_cast Nat.totient_le W

theorem primePredecessorMass_le_log {W : ℕ} (hSq : Squarefree W) :
    primeLogPredecessorDivisorMass W ≤ Real.log (W : ℝ) := by
  unfold primeLogPredecessorDivisorMass
  calc
    _ ≤ ∑ p ∈ W.primeFactors, Real.log (p : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      apply div_le_self (Real.log_natCast_nonneg p)
      exact_mod_cast (by have hh := (Nat.prime_of_mem_primeFactors hp).two_le; omega : 1 ≤ p - 1)
    _ = Real.log (∏ p ∈ W.primeFactors, (p : ℝ)) := by
      symm
      apply Real.log_prod
      intro p hp
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    _ = _ := by rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hSq]

theorem reciprocal_divisors_le_one_add_log (W : ℕ) :
    (∑ d ∈ W.divisors, (1 : ℝ) / d) ≤ 1 + Real.log (W : ℝ) := by
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 W, (1 : ℝ) / d := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
          Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2) (Nat.dvd_of_mem_divisors hd)⟩
      · intro d _ _
        positivity
    _ = (harmonic W : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
    _ ≤ _ := harmonic_le_one_add_log W

theorem coprimeHarmonic_uniform_log_error {W Q : ℕ} (hW : 0 < W) (hSq : Squarefree W) :
    |coprimeHarmonicSum W Q - coprimeHarmonicDensity W * Real.log (Q : ℝ)| ≤
      (4 + |Real.eulerMascheroniConstant|) * (1 + Real.log (W : ℝ)) := by
  have hρ0 := harmonicDensity_nonneg W
  have hρ1 := harmonicDensity_le_one hW
  have hlogW := Real.log_natCast_nonneg W
  have hlogQ := Real.log_natCast_nonneg Q
  have hγ := abs_nonneg Real.eulerMascheroniConstant
  by_cases hWQ : W ≤ Q
  · have hQ : 0 < Q := hW.trans_le hWQ
    have hcard : (W.divisors.card : ℝ) ≤ Q := by
      exact_mod_cast (Nat.card_divisors_le_self W).trans hWQ
    have hdiv : 2 * (W.divisors.card : ℝ) / Q ≤ 2 := by
      apply (div_le_iff₀ (by exact_mod_cast hQ)).mpr
      linarith
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlog2le : Real.log 2 ≤ 1 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at hh
      exact hh
    have hsum := reciprocal_divisors_le_one_add_log W
    have henvelope := abs_coprimeHarmonicError_le_divisor_envelope hW hSq hWQ
    have herror : |coprimeHarmonicError W Q| ≤ 3 + Real.log (W : ℝ) := by
      have hh := mul_le_mul_of_nonneg_left hsum hlog2
      have hh' := mul_le_mul_of_nonneg_right hlog2le (by positivity : 0 ≤ 1 + Real.log (W : ℝ))
      linarith
    have hmass0 : 0 ≤ primeLogPredecessorDivisorMass W := by
      unfold primeLogPredecessorDivisorMass
      positivity
    have hmass := primePredecessorMass_le_log hSq
    have hconstant : |coprimeHarmonicDensity W *
        (Real.eulerMascheroniConstant + primeLogPredecessorDivisorMass W)| ≤
        |Real.eulerMascheroniConstant| + Real.log (W : ℝ) := by
      rw [abs_mul, abs_of_nonneg hρ0]
      calc
        _ ≤ 1 * |Real.eulerMascheroniConstant + primeLogPredecessorDivisorMass W| :=
          mul_le_mul_of_nonneg_right hρ1 (abs_nonneg _)
        _ ≤ _ := by
          simpa only [one_mul, abs_of_nonneg hmass0] using
            (abs_add_le Real.eulerMascheroniConstant (primeLogPredecessorDivisorMass W)).trans
              (add_le_add le_rfl (by simpa only [abs_of_nonneg hmass0] using hmass))
    have hsplit : coprimeHarmonicSum W Q - coprimeHarmonicDensity W * Real.log (Q : ℝ) =
        coprimeHarmonicError W Q + coprimeHarmonicDensity W *
          (Real.eulerMascheroniConstant + primeLogPredecessorDivisorMass W) := by
      unfold coprimeHarmonicError coprimeHarmonicMainTerm
      ring
    rw [hsplit]
    apply (abs_add_le _ _).trans
    exact (add_le_add herror hconstant).trans (by nlinarith [mul_nonneg hγ hlogW])
  · have hsum0 := coprimeHarmonicSum_nonneg W Q
    have hsum : coprimeHarmonicSum W Q ≤ 1 + Real.log (Q : ℝ) :=
      (coprimeHarmonicSum_le_harmonic W Q).trans (harmonic_le_one_add_log Q)
    have hlog : Real.log (Q : ℝ) ≤ Real.log (W : ℝ) := by
      by_cases hQ : Q = 0
      · simpa [hQ] using hlogW
      · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hQ)
          (by exact_mod_cast (by omega : Q ≤ W))
    have hterm0 : 0 ≤ coprimeHarmonicDensity W * Real.log (Q : ℝ) := mul_nonneg hρ0 hlogQ
    have hterm : coprimeHarmonicDensity W * Real.log (Q : ℝ) ≤ Real.log (Q : ℝ) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hρ1 hlogQ
    have habs : |coprimeHarmonicSum W Q - coprimeHarmonicDensity W * Real.log (Q : ℝ)| ≤
        1 + Real.log (W : ℝ) := by
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    exact habs.trans (by nlinarith [mul_nonneg hγ hlogW])

noncomputable def uniformHarmonicConstant : ℝ :=
  4 + |Real.eulerMascheroniConstant| +
    2 * (Real.exp 16 + 4 * reciprocalTotientCorrectionQuarterConstant)

theorem uniformHarmonicConstant_pos : 0 < uniformHarmonicConstant := by
  unfold uniformHarmonicConstant reciprocalTotientCorrectionQuarterConstant
  positivity

theorem squarefreeHarmonic_uniform_log_error {W Q : ℕ} (hW : 0 < W) (hSq : Squarefree W) :
    |squarefreeCoprimeInvTotientMean W Q - coprimeHarmonicDensity W * Real.log (Q : ℝ)| ≤
      uniformHarmonicConstant * (1 + Real.log (W : ℝ)) := by
  have hfirst := abs_squarefreeCoprimeInvTotientMean_sub_coprimeHarmonicSum_le W Q
  have hsecond := coprimeHarmonic_uniform_log_error (Q := Q) hW hSq
  have hcorrection : 0 ≤ 2 * (Real.exp 16 + 4 * reciprocalTotientCorrectionQuarterConstant) := by
    unfold reciprocalTotientCorrectionQuarterConstant
    positivity
  have hlog := Real.log_natCast_nonneg W
  calc
    _ ≤ |squarefreeCoprimeInvTotientMean W Q - coprimeHarmonicSum W Q| +
        |coprimeHarmonicSum W Q - coprimeHarmonicDensity W * Real.log (Q : ℝ)| := abs_sub_le _ _ _
    _ ≤ _ := by
      unfold uniformHarmonicConstant
      nlinarith [mul_nonneg hcorrection hlog]

end Erdos4.FGKMT
