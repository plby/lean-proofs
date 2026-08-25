import ErdosProblems.Erdos67.TwistSeparation
import BoundedGaps.Maynard.PrimeMertens

/-!
# Analytic reductions for polynomial-height twist separation

This file records the exact algebraic reductions used before the high-height
Dirichlet-series estimate.  In particular, it removes the coprimality side
condition from the quotient-character identity: at a prime dividing either
level, both sides vanish.
-/

open scoped BigOperators ComplexConjugate

namespace Erdos67

noncomputable section

/-- The common-level quotient character agrees with the pointwise quotient
at every natural number, including numbers which are not coprime to the
product level. -/
theorem quotientCharacter_apply {q q' n : ℕ}
    (hq : 0 < q) (hq' : 0 < q')
    (χ : DirichletCharacter ℂ q) (χ' : DirichletCharacter ℂ q') :
    quotientCharacter χ χ' n = χ n * conj (χ' n) := by
  by_cases hn : IsCoprime (n : ℤ) (q * q' : ℕ)
  · exact quotientCharacter_apply_of_isCoprime χ χ' hn
  · have hprod : q * q' ≠ 0 := Nat.mul_ne_zero hq.ne' hq'.ne'
    let _ : NeZero (q * q') := ⟨hprod⟩
    have hleft : quotientCharacter χ χ' n = 0 := by
      simpa only [Int.cast_natCast] using
        (DirichletCharacter.apply_eq_zero_iff
          (quotientCharacter χ χ') (n : ℤ)).2 hn
    have hor : ¬ IsCoprime (n : ℤ) (q : ℤ) ∨
        ¬ IsCoprime (n : ℤ) (q' : ℤ) := by
      by_contra hboth
      push Not at hboth
      apply hn
      simpa only [Nat.cast_mul] using hboth.1.mul_right hboth.2
    rw [hleft]
    rcases hor with hnq | hnq'
    · have hχ : χ n = 0 := by
        simpa only [Int.cast_natCast] using
          (DirichletCharacter.apply_eq_zero_iff χ (n : ℤ)).2 hnq
      simp [hχ]
    · have hχ' : χ' n = 0 := by
        simpa only [Int.cast_natCast] using
          (DirichletCharacter.apply_eq_zero_iff χ' (n : ℤ)).2 hnq'
      simp [hχ']

/-- After passage to the common level, the original phase is literally a
single character times an Archimedean phase. -/
theorem characterTwistPhase_eq_quotientCharacter {q q' n : ℕ}
    (hq : 0 < q) (hq' : 0 < q')
    (χ : DirichletCharacter ℂ q) (χ' : DirichletCharacter ℂ q')
    (v : ℝ) :
    characterTwistPhase χ χ' v n =
      quotientCharacter χ χ' n *
        (n : ℂ) ^ (-(Complex.I * (v : ℂ))) := by
  rw [characterTwistPhase, quotientCharacter_apply hq hq' χ χ']

/-- The prime correlation can therefore be written with one character at the
product level. -/
theorem characterTwistPrimeCorrelation_eq_quotientCharacter
    {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (χ : DirichletCharacter ℂ q) (χ' : DirichletCharacter ℂ q')
    (v : ℝ) (Y : ℕ) :
    characterTwistPrimeCorrelation χ χ' v Y =
      ∑ p ∈ primesUpTo Y,
        (quotientCharacter χ χ' p *
          (p : ℂ) ^ (-(Complex.I * (v : ℂ)))).re / (p : ℝ) := by
  unfold characterTwistPrimeCorrelation
  apply Finset.sum_congr rfl
  intro p hp
  rw [characterTwistPhase_eq_quotientCharacter hq hq' χ χ']

/-! ## Finite Euler-logarithm reduction -/

/-- The point just to the right of the line `Re(s)=1` used for the truncated
Euler product. -/
def polynomialHeightEulerPoint (Y : ℕ) (v : ℝ) : ℂ :=
  ((1 + (Real.log (Y : ℝ))⁻¹ : ℝ) : ℂ) + Complex.I * (v : ℂ)

/-- The linear term of the Euler factor at `p`. -/
def polynomialHeightEulerPrimeTerm {N : ℕ}
    (ψ : DirichletCharacter ℂ N) (Y : ℕ) (v : ℝ) (p : ℕ) : ℂ :=
  ψ p * (p : ℂ) ^ (-polynomialHeightEulerPoint Y v)

/-- The finite real part of the logarithm of the Euler product through `Y`. -/
def truncatedPolynomialHeightEulerLog {N : ℕ}
    (ψ : DirichletCharacter ℂ N) (Y : ℕ) (v : ℝ) : ℝ :=
  ∑ p ∈ primesUpTo Y,
    (-Complex.log (1 - polynomialHeightEulerPrimeTerm ψ Y v p)).re

/-- The corresponding finite sum of the linear Euler-factor terms. -/
def truncatedPolynomialHeightEulerLinear {N : ℕ}
    (ψ : DirichletCharacter ℂ N) (Y : ℕ) (v : ℝ) : ℝ :=
  ∑ p ∈ primesUpTo Y,
    (polynomialHeightEulerPrimeTerm ψ Y v p).re

theorem norm_polynomialHeightEulerPrimeTerm_lt_half
    {N Y p : ℕ} (ψ : DirichletCharacter ℂ N) (v : ℝ)
    (hY : 2 ≤ Y) (hp : p.Prime) :
    ‖polynomialHeightEulerPrimeTerm ψ Y v p‖ < 1 / 2 := by
  have hlogY : 0 < Real.log (Y : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hsigma : 1 < 1 + (Real.log (Y : ℝ))⁻¹ := by
    have : 0 < (Real.log (Y : ℝ))⁻¹ := inv_pos.mpr hlogY
    linarith
  have hpOne : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hrpow :
      (p : ℝ) ^ (-(1 + (Real.log (Y : ℝ))⁻¹)) <
        (p : ℝ) ^ (-(1 : ℝ)) :=
    Real.rpow_lt_rpow_of_exponent_lt hpOne (by linarith)
  have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hinv : (p : ℝ) ^ (-(1 : ℝ)) ≤ 1 / 2 := by
    rw [Real.rpow_neg (by positivity), Real.rpow_one]
    simpa only [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hpTwo)
  unfold polynomialHeightEulerPrimeTerm polynomialHeightEulerPoint
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp.pos]
  simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, zero_mul, Complex.I_im,
    Complex.ofReal_im, mul_zero, sub_zero, add_zero]
  calc
    ‖ψ p‖ * (p : ℝ) ^ (-(1 + (Real.log (Y : ℝ))⁻¹)) ≤
        1 * (p : ℝ) ^ (-(1 + (Real.log (Y : ℝ))⁻¹)) := by
      gcongr
      exact ψ.norm_le_one p
    _ < (p : ℝ) ^ (-(1 : ℝ)) := by simpa using hrpow
    _ ≤ 1 / 2 := hinv

/-- Removing all powers of a single Euler factor beyond the linear term costs
at most `p⁻²`, uniformly in the character, height, and endpoint. -/
theorem norm_eulerLog_sub_linear_le_inv_sq
    {N Y p : ℕ} (ψ : DirichletCharacter ℂ N) (v : ℝ)
    (hY : 2 ≤ Y) (hp : p.Prime) :
    ‖-Complex.log (1 - polynomialHeightEulerPrimeTerm ψ Y v p) -
        polynomialHeightEulerPrimeTerm ψ Y v p‖ ≤
      (p : ℝ) ^ (-(2 : ℝ)) := by
  let z := polynomialHeightEulerPrimeTerm ψ Y v p
  have hzHalf : ‖z‖ < 1 / 2 :=
    norm_polynomialHeightEulerPrimeTerm_lt_half ψ v hY hp
  have hzOne : ‖z‖ < 1 := hzHalf.trans (by norm_num)
  have hlog := Complex.norm_log_one_sub_inv_sub_self_le hzOne
  have hslit : 1 - z ∈ Complex.slitPlane :=
    by
      simpa only [sub_eq_add_neg, norm_neg] using
        (Complex.mem_slitPlane_of_norm_lt_one (z := -z) (by simpa using hzOne))
  rw [Complex.log_inv _ (Complex.slitPlane_arg_ne_pi hslit)] at hlog
  have hinv : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀]
    · linarith
    · linarith
  have hzNonneg : 0 ≤ ‖z‖ ^ 2 := sq_nonneg _
  have hrem : ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 ≤ ‖z‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hinv hzNonneg]
  have hpInvNonneg : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  have hzInv : ‖z‖ ≤ (p : ℝ)⁻¹ := by
    have hpOne : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hlogY : 0 < Real.log (Y : ℝ) := by
      exact Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
    have hrpow :
        (p : ℝ) ^ (-(1 + (Real.log (Y : ℝ))⁻¹)) ≤
          (p : ℝ) ^ (-(1 : ℝ)) :=
      (Real.rpow_lt_rpow_of_exponent_lt hpOne
        (by have := inv_pos.mpr hlogY; linarith)).le
    unfold z polynomialHeightEulerPrimeTerm polynomialHeightEulerPoint
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp.pos]
    simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, zero_mul, Complex.I_im,
      Complex.ofReal_im, mul_zero, sub_zero, add_zero]
    calc
      ‖ψ p‖ * (p : ℝ) ^ (-(1 + (Real.log (Y : ℝ))⁻¹)) ≤
          1 * (p : ℝ) ^ (-(1 + (Real.log (Y : ℝ))⁻¹)) := by
        gcongr
        exact ψ.norm_le_one p
      _ ≤ (p : ℝ) ^ (-(1 : ℝ)) := by simpa using hrpow
      _ = (p : ℝ)⁻¹ := by rw [Real.rpow_neg (by positivity), Real.rpow_one]
  calc
    ‖-Complex.log (1 - polynomialHeightEulerPrimeTerm ψ Y v p) -
        polynomialHeightEulerPrimeTerm ψ Y v p‖ =
        ‖-Complex.log (1 - z) - z‖ := rfl
    _ ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 := hlog
    _ ≤ ‖z‖ ^ 2 := hrem
    _ ≤ ((p : ℝ)⁻¹) ^ 2 := by gcongr
    _ = (p : ℝ) ^ (-(2 : ℝ)) := by
      rw [Real.rpow_neg (by positivity), Real.rpow_two, inv_pow]

/-- A fixed finite constant dominating every truncated `p⁻²` sum. -/
def polynomialHeightPrimePowerRemainderBound : ℝ :=
  ∑' n : ℕ, (n : ℝ) ^ (-(2 : ℝ))

theorem polynomialHeightPrimePowerRemainderBound_nonneg :
    0 ≤ polynomialHeightPrimePowerRemainderBound := by
  exact tsum_nonneg fun n ↦ Real.rpow_nonneg (Nat.cast_nonneg n) _

theorem truncatedEulerLinear_le_log_add_remainder
    {N Y : ℕ} (ψ : DirichletCharacter ℂ N) (v : ℝ) (hY : 2 ≤ Y) :
    truncatedPolynomialHeightEulerLinear ψ Y v ≤
      truncatedPolynomialHeightEulerLog ψ Y v +
        polynomialHeightPrimePowerRemainderBound := by
  have hsummable : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-(2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hfinite :
      ∑ p ∈ primesUpTo Y, (p : ℝ) ^ (-(2 : ℝ)) ≤
        polynomialHeightPrimePowerRemainderBound := by
    exact hsummable.sum_le_tsum (primesUpTo Y)
      (fun n hn ↦ Real.rpow_nonneg (Nat.cast_nonneg n) _)
  unfold truncatedPolynomialHeightEulerLinear
    truncatedPolynomialHeightEulerLog
  calc
    ∑ p ∈ primesUpTo Y,
        (polynomialHeightEulerPrimeTerm ψ Y v p).re ≤
      ∑ p ∈ primesUpTo Y,
        ((-Complex.log (1 - polynomialHeightEulerPrimeTerm ψ Y v p)).re +
          (p : ℝ) ^ (-(2 : ℝ))) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpPrime := (mem_primesUpTo.mp hp).1
      have hnorm := norm_eulerLog_sub_linear_le_inv_sq ψ v hY hpPrime
      have hre := Complex.abs_re_le_norm
        (-Complex.log (1 - polynomialHeightEulerPrimeTerm ψ Y v p) -
          polynomialHeightEulerPrimeTerm ψ Y v p)
      have habs := hre.trans hnorm
      rw [abs_le] at habs
      simp only [Complex.sub_re, Complex.neg_re] at habs
      rw [Complex.neg_re]
      linarith
    _ = (∑ p ∈ primesUpTo Y,
          (-Complex.log (1 - polynomialHeightEulerPrimeTerm ψ Y v p)).re) +
        ∑ p ∈ primesUpTo Y, (p : ℝ) ^ (-(2 : ℝ)) := by
      rw [Finset.sum_add_distrib]
    _ ≤ (∑ p ∈ primesUpTo Y,
          (-Complex.log (1 - polynomialHeightEulerPrimeTerm ψ Y v p)).re) +
        polynomialHeightPrimePowerRemainderBound := by gcongr

/-! ## Removing the small real shift -/

/-- A nonnegative uniform constant in the logarithmically weighted prime
Mertens estimate. -/
def polynomialHeightPrimeLogMertensBound : ℝ :=
  max 0 (Classical.choose
    BoundedGaps.Maynard.exists_uniform_abs_primeLogHarmonicSum_sub_log)

theorem polynomialHeightPrimeLogMertensBound_nonneg :
    0 ≤ polynomialHeightPrimeLogMertensBound :=
  le_max_left _ _

theorem primeLogHarmonicSum_le_log_add_bound (Y : ℕ) :
    BoundedGaps.Maynard.primeLogHarmonicSum Y ≤
      Real.log (Y : ℝ) + polynomialHeightPrimeLogMertensBound := by
  have hspec := (Classical.choose_spec
    BoundedGaps.Maynard.exists_uniform_abs_primeLogHarmonicSum_sub_log) Y
  have hupper := (abs_le.mp hspec).2
  unfold polynomialHeightPrimeLogMertensBound
  linarith [le_max_right (0 : ℝ) (Classical.choose
    BoundedGaps.Maynard.exists_uniform_abs_primeLogHarmonicSum_sub_log)]

/-- The fixed cost of replacing `p⁻¹⁻¹/log Y` by `p⁻¹` on primes
through `Y`. -/
def polynomialHeightWeightRemovalBound : ℝ :=
  1 + polynomialHeightPrimeLogMertensBound / Real.log 2

theorem polynomialHeightWeightRemovalBound_nonneg :
    0 ≤ polynomialHeightWeightRemovalBound := by
  unfold polynomialHeightWeightRemovalBound
  have hlogTwo : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hquot : 0 ≤ polynomialHeightPrimeLogMertensBound / Real.log 2 :=
    div_nonneg polynomialHeightPrimeLogMertensBound_nonneg hlogTwo.le
  linarith

private theorem one_sub_rpow_neg_inv_log_le
    {Y p : ℕ} (hY : 2 ≤ Y) (hp : p.Prime) :
    1 - (p : ℝ) ^ (-(Real.log (Y : ℝ))⁻¹) ≤
      Real.log (p : ℝ) / Real.log (Y : ℝ) := by
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlogY : 0 < Real.log (Y : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  rw [Real.rpow_def_of_pos hpPos]
  have hexp := Real.add_one_le_exp
    (-(Real.log (p : ℝ) / Real.log (Y : ℝ)))
  have hexponent :
      Real.log (p : ℝ) * (-(Real.log (Y : ℝ))⁻¹) =
        -(Real.log (p : ℝ) / Real.log (Y : ℝ)) := by
    field_simp
  rw [hexponent]
  linarith

private theorem inv_sub_rpow_shift_le_log_div
    {Y p : ℕ} (hY : 2 ≤ Y) (hp : p.Prime) :
    (p : ℝ)⁻¹ - (p : ℝ) ^ (-(1 + (Real.log (Y : ℝ))⁻¹)) ≤
      Real.log (p : ℝ) / (p : ℝ) / Real.log (Y : ℝ) := by
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hphase := one_sub_rpow_neg_inv_log_le hY hp
  have hinvNonneg : 0 ≤ (p : ℝ)⁻¹ := by positivity
  have hmul := mul_le_mul_of_nonneg_left hphase hinvNonneg
  rw [show -(1 + (Real.log (Y : ℝ))⁻¹) =
      (-(1 : ℝ)) + (-(Real.log (Y : ℝ))⁻¹) by ring,
    Real.rpow_add hpPos, Real.rpow_neg (by positivity), Real.rpow_one]
  calc
    (p : ℝ)⁻¹ - (p : ℝ)⁻¹ *
        (p : ℝ) ^ (-(Real.log (Y : ℝ))⁻¹) =
        (p : ℝ)⁻¹ *
          (1 - (p : ℝ) ^ (-(Real.log (Y : ℝ))⁻¹)) := by ring
    _ ≤ (p : ℝ)⁻¹ *
        (Real.log (p : ℝ) / Real.log (Y : ℝ)) := hmul
    _ = Real.log (p : ℝ) / (p : ℝ) / Real.log (Y : ℝ) := by
      field_simp

theorem polynomialHeightEulerPrimeTerm_eq_shifted_phase
    {N Y p : ℕ} (ψ : DirichletCharacter ℂ N) (v : ℝ)
    (hp : p.Prime) :
    polynomialHeightEulerPrimeTerm ψ Y v p =
      (ψ p * (p : ℂ) ^ (-(Complex.I * (v : ℂ)))) *
        ((p : ℝ) ^ (-(1 + (Real.log (Y : ℝ))⁻¹)) : ℝ) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  unfold polynomialHeightEulerPrimeTerm polynomialHeightEulerPoint
  rw [show -(((1 + (Real.log (Y : ℝ))⁻¹ : ℝ) : ℂ) +
        Complex.I * (v : ℂ)) =
      -(Complex.I * (v : ℂ)) +
        (-((1 + (Real.log (Y : ℝ))⁻¹ : ℝ) : ℂ)) by ring,
    Complex.cpow_add _ _ hp0]
  have hreal :
      (p : ℂ) ^ (-((1 + (Real.log (Y : ℝ))⁻¹ : ℝ) : ℂ)) =
        ((p : ℝ) ^ (-(1 + (Real.log (Y : ℝ))⁻¹)) : ℝ) := by
    rw [← Complex.ofReal_neg]
    change ((p : ℝ) : ℂ) ^
      ((-(1 + (Real.log (Y : ℝ))⁻¹) : ℝ) : ℂ) = _
    exact (Complex.ofReal_cpow (Nat.cast_nonneg p)
      (-(1 + (Real.log (Y : ℝ))⁻¹))).symm
  rw [hreal]
  ring

theorem quotientCorrelation_le_eulerLinear_add_weightBound
    {q q' Y : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (χ : DirichletCharacter ℂ q) (χ' : DirichletCharacter ℂ q')
    (v : ℝ) (hY : 2 ≤ Y) :
    characterTwistPrimeCorrelation χ χ' v Y ≤
      truncatedPolynomialHeightEulerLinear (quotientCharacter χ χ') Y v +
        polynomialHeightWeightRemovalBound := by
  rw [characterTwistPrimeCorrelation_eq_quotientCharacter hq hq' χ χ']
  have hlogY : 0 < Real.log (Y : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hsumLog :
      ∑ p ∈ primesUpTo Y, Real.log (p : ℝ) / (p : ℝ) =
        BoundedGaps.Maynard.primeLogHarmonicSum Y := by
    unfold BoundedGaps.Maynard.primeLogHarmonicSum primesUpTo
    rw [Nat.primesLE_eq_filter_range]
  have hlogBound := primeLogHarmonicSum_le_log_add_bound Y
  have herror :
      (∑ p ∈ primesUpTo Y, Real.log (p : ℝ) / (p : ℝ)) /
          Real.log (Y : ℝ) ≤ polynomialHeightWeightRemovalBound := by
    rw [hsumLog]
    calc
      BoundedGaps.Maynard.primeLogHarmonicSum Y / Real.log (Y : ℝ) ≤
          (Real.log (Y : ℝ) + polynomialHeightPrimeLogMertensBound) /
            Real.log (Y : ℝ) := div_le_div_of_nonneg_right hlogBound hlogY.le
      _ = 1 + polynomialHeightPrimeLogMertensBound /
            Real.log (Y : ℝ) := by field_simp
      _ ≤ 1 + polynomialHeightPrimeLogMertensBound / Real.log 2 := by
        have hcast : (2 : ℝ) ≤ Y := by exact_mod_cast hY
        have hlogle : Real.log 2 ≤ Real.log (Y : ℝ) :=
          Real.log_le_log (by norm_num) hcast
        simpa only [add_comm] using add_le_add_left
          (div_le_div_of_nonneg_left
            polynomialHeightPrimeLogMertensBound_nonneg
            (Real.log_pos one_lt_two) hlogle) 1
      _ = polynomialHeightWeightRemovalBound := rfl
  unfold truncatedPolynomialHeightEulerLinear
  calc
    ∑ p ∈ primesUpTo Y,
        (quotientCharacter χ χ' p *
          (p : ℂ) ^ (-(Complex.I * (v : ℂ)))).re / (p : ℝ) ≤
      ∑ p ∈ primesUpTo Y,
        ((polynomialHeightEulerPrimeTerm (quotientCharacter χ χ') Y v p).re +
          Real.log (p : ℝ) / (p : ℝ) / Real.log (Y : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hpMem
      have hp := (mem_primesUpTo.mp hpMem).1
      let phase := quotientCharacter χ χ' p *
        (p : ℂ) ^ (-(Complex.I * (v : ℂ)))
      have hphaseEq : phase = characterTwistPhase χ χ' v p := by
        exact (characterTwistPhase_eq_quotientCharacter hq hq' χ χ' v).symm
      have hphase : phase.re ≤ 1 := by
        calc
          phase.re = (characterTwistPhase χ χ' v p).re :=
            congrArg Complex.re hphaseEq
          _ ≤ ‖characterTwistPhase χ χ' v p‖ := Complex.re_le_norm _
          _ ≤ 1 := norm_characterTwistPhase_le_one χ χ' v hp.pos
      have hshiftNonneg :
          0 ≤ (p : ℝ)⁻¹ -
            (p : ℝ) ^ (-(1 + (Real.log (Y : ℝ))⁻¹)) := by
        have hpOne : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
        have hdelta : 0 < (Real.log (Y : ℝ))⁻¹ := inv_pos.mpr hlogY
        have hpow := Real.rpow_lt_rpow_of_exponent_lt hpOne
          (show -(1 + (Real.log (Y : ℝ))⁻¹) < -(1 : ℝ) by linarith)
        have hone : (p : ℝ) ^ (-(1 : ℝ)) = (p : ℝ)⁻¹ := by
          rw [Real.rpow_neg (by positivity), Real.rpow_one]
        linarith
      have hscaled := mul_le_mul_of_nonneg_right hphase hshiftNonneg
      have hdiff := inv_sub_rpow_shift_le_log_div hY hp
      rw [polynomialHeightEulerPrimeTerm_eq_shifted_phase
        (quotientCharacter χ χ') v hp]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero]
      change phase.re / (p : ℝ) ≤
        phase.re * (p : ℝ) ^ (-(1 + (Real.log (Y : ℝ))⁻¹)) +
          Real.log (p : ℝ) / (p : ℝ) / Real.log (Y : ℝ)
      rw [div_eq_mul_inv]
      nlinarith
    _ = (∑ p ∈ primesUpTo Y,
          (polynomialHeightEulerPrimeTerm
            (quotientCharacter χ χ') Y v p).re) +
        (∑ p ∈ primesUpTo Y, Real.log (p : ℝ) / (p : ℝ)) /
          Real.log (Y : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.sum_div]
    _ ≤ (∑ p ∈ primesUpTo Y,
          (polynomialHeightEulerPrimeTerm
            (quotientCharacter χ χ') Y v p).re) +
        polynomialHeightWeightRemovalBound := by gcongr

/-! ## The exact remaining high-height estimate -/

/-- A bounded-conductor Vinogradov--Korobov estimate in the precise finite
Euler-product form consumed by the reduction above.  The strict coefficient
margin between `5/6` here and `11/12` in
`PolynomialHeightPrimeCorrelationBound` absorbs the two uniform finite
comparison costs. -/
def PolynomialHeightTruncatedEulerLogBound (Q D : ℕ) (T : ℝ) : Prop :=
  ∃ Y₀ : ℕ, 2 ≤ Y₀ ∧
    ∀ (Y N : ℕ), Y₀ ≤ Y → 0 < N → N ≤ Q * Q →
      ∀ (ψ : DirichletCharacter ℂ N) (v : ℝ),
        (Y : ℝ) ≤ |v| → |v| ≤ T * (Y : ℝ) ^ D →
          truncatedPolynomialHeightEulerLog ψ Y v ≤
            (5 / 6 : ℝ) * Real.log (Real.log (Y : ℝ))

/-- The finite Euler-log estimate implies the original prime-correlation
estimate.  This theorem includes passage to the common product level,
removal of prime powers, removal of the real shift, and absorption of both
uniform errors. -/
theorem polynomialHeightPrimeCorrelationBound_of_truncatedEulerLogBound
    {Q D : ℕ} {T : ℝ}
    (hEuler : PolynomialHeightTruncatedEulerLogBound Q D T) :
    PolynomialHeightPrimeCorrelationBound Q D T := by
  rcases hEuler with ⟨YE, hYE, hEuler⟩
  let K : ℝ := polynomialHeightWeightRemovalBound +
    polynomialHeightPrimePowerRemainderBound
  have hK : 0 ≤ K := add_nonneg
    polynomialHeightWeightRemovalBound_nonneg
    polynomialHeightPrimePowerRemainderBound_nonneg
  have hloglog : Filter.Tendsto
      (fun Y : ℕ ↦ Real.log (Real.log (Y : ℝ)))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hevent : ∀ᶠ Y : ℕ in Filter.atTop,
      12 * K ≤ Real.log (Real.log (Y : ℝ)) :=
    (Filter.tendsto_atTop.1 hloglog (12 * K))
  obtain ⟨NK, hNK⟩ := Filter.eventually_atTop.1 hevent
  let Y₀ := max YE (max 2 NK)
  refine ⟨Y₀, (le_max_left 2 NK).trans (le_max_right YE (max 2 NK)), ?_⟩
  intro Y q q' hY hq hqQ hq' hq'Q χ χ' v hvLower hvUpper
  have hYEY : YE ≤ Y := (le_max_left YE (max 2 NK)).trans hY
  have hN : NK ≤ Y :=
    (le_max_right 2 NK).trans ((le_max_right YE (max 2 NK)).trans hY)
  have hYY : 2 ≤ Y :=
    (le_max_left 2 NK).trans ((le_max_right YE (max 2 NK)).trans hY)
  have hlevelPos : 0 < q * q' := Nat.mul_pos hq hq'
  have hlevel : q * q' ≤ Q * Q := Nat.mul_le_mul hqQ hq'Q
  have hlog := hEuler Y (q * q') hYEY hlevelPos hlevel
    (quotientCharacter χ χ') v hvLower hvUpper
  have hlinear := truncatedEulerLinear_le_log_add_remainder
    (quotientCharacter χ χ') v hYY
  have hcorr := quotientCorrelation_le_eulerLinear_add_weightBound
    hq hq' χ χ' v hYY
  have habsorb :
      K ≤ (1 / 12 : ℝ) * Real.log (Real.log (Y : ℝ)) +
        PrimeEstimates.mertensBound := by
    have hlarge := hNK Y hN
    have hM := PrimeEstimates.mertensBound_nonneg
    nlinarith
  dsimp only [K] at habsorb
  linarith

end

end Erdos67
