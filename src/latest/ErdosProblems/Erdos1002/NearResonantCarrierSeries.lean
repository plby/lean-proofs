import ErdosProblems.Erdos1002.NearResonantCarrierGlobal
import ErdosProblems.Erdos1002.WindowCarrierSummation
import Mathlib.NumberTheory.ZetaValues

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Pointwise Bernoulli-carrier reconstruction of the smooth near tail

The shifted-carrier estimates are useful for the literal shot only after
the carrier series has been identified pointwise.  The Bernoulli mark is
continuous and has quadratically decaying Fourier coefficients, so this
identification is an absolutely convergent `HasSum`, not merely an `L²`
identity.  We then exchange that series with the finite denominator sum.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators ComplexConjugate ENNReal Real

namespace Erdos1002

noncomputable section

private theorem paperExp_int_period
    (ell m : ℤ) (x : ℝ) :
    paperExp ((ell : ℝ) * (x + (m : ℝ))) =
      paperExp ((ell : ℝ) * x) := by
  unfold paperExp
  rw [show
      2 * (Real.pi : ℂ) * Complex.I *
          (((ell : ℝ) * (x + (m : ℝ)) : ℝ) : ℂ) =
        2 * (Real.pi : ℂ) * Complex.I *
            ((((ell : ℝ) * x : ℝ) : ℂ)) +
          ((ell * m : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
      push_cast
      ring]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- An integer Fourier character may be evaluated at the fractional part.
This is the exact periodicity step needed below. -/
theorem paperExp_int_mul_eq_fourier_fract (ell : ℤ) (x : ℝ) :
    paperExp ((ell : ℝ) * x) =
      fourier ell ((Int.fract x : ℝ) : AddCircle (1 : ℝ)) := by
  have hx : x = Int.fract x + (Int.floor x : ℝ) :=
    (Int.fract_add_floor x).symm
  rw [hx, paperExp_int_period]
  rw [fourier_coe_apply]
  norm_num
  unfold paperExp
  congr 1
  push_cast
  ring

/-- The exact pointwise Fourier series of the paper's Bernoulli mark.  In
particular the series is summable at every real argument, including
integers. -/
theorem hasSum_bernoulliMark_pointwiseFourier (x : ℝ) :
    HasSum
      (fun ell : ℤ ↦ bernoulliMarkFourierCoefficient ell *
        paperExp ((ell : ℝ) * x))
      (bernoulliMark x : ℂ) := by
  let y : ℝ := Int.fract x
  have hy : y ∈ Set.Icc (0 : ℝ) 1 := by
    exact ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  have hbase := hasSum_one_div_pow_mul_fourier_mul_bernoulliFun
    (k := 2) (by omega) hy
  let c : ℂ := -(1 / (4 * (Real.pi : ℂ) ^ 2))
  have hscaled := hbase.mul_left c
  have hzero : HasSum
      (fun ell : ℤ ↦ if ell = 0 then (1 / 12 : ℂ) else 0)
      (1 / 12 : ℂ) := hasSum_ite_eq 0 (1 / 12 : ℂ)
  have hadd := hzero.add hscaled
  convert! hadd using 1
  · funext ell
    rw [paperExp_int_mul_eq_fourier_fract]
    dsimp [y]
    by_cases hell : ell = 0
    · subst ell
      simp [bernoulliMarkFourierCoefficient]
    · rw [bernoulliMarkFourierCoefficient, if_neg hell, if_neg hell]
      dsimp [c]
      ring
  · dsimp [c, y]
    rw [bernoulliFun_two]
    unfold bernoulliMark
    push_cast
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp [hpi]
    rw [Complex.I_sq]
    ring

theorem summable_bernoulliMark_pointwiseFourier (x : ℝ) :
    Summable
      (fun ell : ℤ ↦ bernoulliMarkFourierCoefficient ell *
        paperExp ((ell : ℝ) * x)) :=
  (hasSum_bernoulliMark_pointwiseFourier x).summable

/-- The cell phase may be written either with `Npα` or with the nearest
resonance displacement `Nδ_p`; the difference is an integer. -/
theorem bernoulliMark_nat_mul_eq_resonanceDelta
    (N p : ℕ) (alpha : ℝ) :
    bernoulliMark ((N * p : ℕ) * alpha) =
      bernoulliMark ((N : ℝ) * resonanceDelta p alpha) := by
  have harg : ((N * p : ℕ) : ℝ) * alpha =
      (N : ℝ) * resonanceDelta p alpha +
        (((N : ℤ) * resonanceNumerator p alpha : ℤ) : ℝ) := by
    unfold resonanceDelta
    push_cast
    ring
  rw [harg, bernoulliMark_add_intCast]

/-- The finite smooth denominator tail with its Bernoulli mark still in
physical space. -/
def smoothNearBernoulliShotTail
    (N : ℕ) (a ε : ℝ) (Q U : ℕ) (alpha : ℝ) : ℂ :=
  ∑ p ∈ Finset.Ioc Q U,
    (bernoulliMark ((N * p : ℕ) * alpha) : ℂ) *
      smoothNearPrimitivePoleSum a ε p alpha

/-- The same smooth shot written with the literal primitive-resonance pole.
This form is the direct bridge to `primitiveShot`. -/
def smoothNearLiteralShotTerm
    (N p : ℕ) (a ε : ℝ) (alpha : ℝ) : ℂ :=
  (bernoulliMark ((N : ℝ) * resonanceDelta p alpha) : ℂ) *
    nearPrimitivePole a ε p alpha

def smoothNearLiteralShotTail
    (N : ℕ) (a ε : ℝ) (Q U : ℕ) (alpha : ℝ) : ℂ :=
  ∑ p ∈ Finset.Ioc Q U, smoothNearLiteralShotTerm N p a ε alpha

/-- The smooth term is the exact primitive shot multiplied by the explicit
two-scale cutoff.  Division at an exact rational is totalized on both sides,
so no exceptional case is suppressed. -/
theorem smoothNearLiteralShotTerm_eq_rho_mul_primitiveShot
    (N p : ℕ) (a ε : ℝ) (alpha : ℝ) :
    smoothNearLiteralShotTerm N p a ε alpha =
      nearRho a ε ((p : ℝ) * resonanceDelta p alpha) *
        (primitiveShot N p alpha : ℂ) := by
  by_cases hprim : IsPrimitiveResonance p alpha
  · rw [primitiveShot_of_primitive N p alpha hprim]
    unfold smoothNearLiteralShotTerm nearPrimitivePole
    rw [if_pos hprim]
    unfold nearW
    push_cast
    ring
  · rw [primitiveShot_of_not_primitive N p alpha hprim]
    simp [smoothNearLiteralShotTerm, nearPrimitivePole, hprim]

/-- On the central plateau `2a ≤ |x| ≤ ε/4`, the cutoff is exactly
one.  The two transition layers are therefore explicit, rather than hidden
inside a smoothing-removal phrase. -/
theorem nearRho_eq_one_of_two_mul_le_abs_of_abs_le_quarter
    (a ε x : ℝ) (ha : 0 < a) (hε : 0 < ε)
    (htwo : 2 * a ≤ |x|) (hquarter : |x| ≤ ε / 4) :
    nearRho a ε x = 1 := by
  have houter : scaledNearProfile (ε / 2) x = 1 := by
    apply scaledNearProfile_eq_one (ε / 2) x (by positivity)
    linarith
  have hinner : scaledNearProfile a x = 0 := by
    exact scaledNearProfile_eq_zero_of_two_mul_le_abs a x ha htwo
  unfold nearRho
  rw [houter, hinner]
  norm_num

theorem smoothNearLiteralShotTerm_eq_primitiveShot_of_plateau
    (N p : ℕ) (a ε : ℝ) (alpha : ℝ)
    (ha : 0 < a) (hε : 0 < ε)
    (htwo : 2 * a ≤ |(p : ℝ) * resonanceDelta p alpha|)
    (hquarter : |(p : ℝ) * resonanceDelta p alpha| ≤ ε / 4) :
    smoothNearLiteralShotTerm N p a ε alpha =
      (primitiveShot N p alpha : ℂ) := by
  rw [smoothNearLiteralShotTerm_eq_rho_mul_primitiveShot,
    nearRho_eq_one_of_two_mul_le_abs_of_abs_le_quarter
      a ε _ ha hε htwo hquarter, one_mul]

/-- On the open unit interval, and once the exceptional denominators `1,2`
have been removed, the globally smooth cell representative is exactly the
literal primitive-resonance expression. -/
theorem smoothNearBernoulliShotTail_eq_literal
    (N : ℕ) (a ε : ℝ) (Q U : ℕ) (alpha : ℝ)
    (hQ : 1 ≤ Q) (ha : 0 < a) (hε : 0 < ε)
    (haε : a ≤ ε / 4) (hεhalf : ε ≤ 1 / 2)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1) :
    smoothNearBernoulliShotTail N a ε Q U alpha =
      smoothNearLiteralShotTail N a ε Q U alpha := by
  unfold smoothNearBernoulliShotTail smoothNearLiteralShotTail
    smoothNearLiteralShotTerm
  apply Finset.sum_congr rfl
  intro p hp
  have hpTwo : 2 ≤ p := by
    have := (Finset.mem_Ioc.mp hp).1
    omega
  rw [bernoulliMark_nat_mul_eq_resonanceDelta,
    nearPrimitivePole_eq_smoothNearPrimitivePoleSum
      a ε p hpTwo ha hε haε hεhalf halpha]

private theorem hasSum_smoothNearCarrierTerm_oneDenominator
    (N p : ℕ) (a ε alpha : ℝ) :
    HasSum
      (fun ell : ℤ ↦
        smoothNearPrimitivePoleCarrierTerm N ell a ε p alpha)
      ((bernoulliMark ((N * p : ℕ) * alpha) : ℂ) *
        smoothNearPrimitivePoleSum a ε p alpha) := by
  have h := (hasSum_bernoulliMark_pointwiseFourier
    (((N * p : ℕ) : ℝ) * alpha)).mul_right
      (smoothNearPrimitivePoleSum a ε p alpha)
  convert! h using 1
  funext ell
  unfold smoothNearPrimitivePoleCarrierTerm unitModulate
    nearBernoulliCarrierFrequency
  push_cast
  ring_nf

/-- The complete Bernoulli-carrier series reconstructs the literal smooth
physical tail pointwise.  The exchange with denominators is harmless because
that sum is finite. -/
theorem hasSum_smoothNearPrimitivePoleCarrierTail
    (N : ℕ) (a ε : ℝ) (Q U : ℕ) (alpha : ℝ) :
    HasSum
      (fun ell : ℤ ↦
        smoothNearPrimitivePoleCarrierTail N ell a ε Q U alpha)
      (smoothNearBernoulliShotTail N a ε Q U alpha) := by
  classical
  have hfinite : ∀ S : Finset ℕ,
      HasSum
        (fun ell : ℤ ↦ ∑ p ∈ S,
          smoothNearPrimitivePoleCarrierTerm N ell a ε p alpha)
        (∑ p ∈ S,
          (bernoulliMark ((N * p : ℕ) * alpha) : ℂ) *
            smoothNearPrimitivePoleSum a ε p alpha) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        simpa using! (hasSum_zero : HasSum (fun _ell : ℤ ↦ (0 : ℂ)) 0)
    | @insert p S hp ih =>
        have hpTail := hasSum_smoothNearCarrierTerm_oneDenominator
          N p a ε alpha
        simpa only [Finset.sum_insert hp] using! hpTail.add ih
  simpa only [smoothNearPrimitivePoleCarrierTail,
    smoothNearBernoulliShotTail] using! hfinite (Finset.Ioc Q U)

theorem summable_smoothNearPrimitivePoleCarrierTail
    (N : ℕ) (a ε : ℝ) (Q U : ℕ) (alpha : ℝ) :
    Summable
      (fun ell : ℤ ↦
        smoothNearPrimitivePoleCarrierTail N ell a ε Q U alpha) :=
  (hasSum_smoothNearPrimitivePoleCarrierTail N a ε Q U alpha).summable

theorem tsum_smoothNearPrimitivePoleCarrierTail
    (N : ℕ) (a ε : ℝ) (Q U : ℕ) (alpha : ℝ) :
    (∑' ell : ℤ,
        smoothNearPrimitivePoleCarrierTail N ell a ε Q U alpha) =
      smoothNearBernoulliShotTail N a ε Q U alpha :=
  (hasSum_smoothNearPrimitivePoleCarrierTail N a ε Q U alpha).tsum_eq

/-! ## Uniform aggregation of the nonzero carriers -/

theorem norm_bernoulliMarkFourierCoefficient_pos (ell : ℤ) :
    0 < ‖bernoulliMarkFourierCoefficient ell‖ := by
  by_cases hell : ell = 0
  · subst ell
    norm_num [bernoulliMarkFourierCoefficient]
  · rw [norm_bernoulliMarkFourierCoefficient_eq hell]
    positivity

def finiteNonzeroCarrierSet (J : ℕ) : Finset ℤ :=
  (Finset.Icc (-(J : ℤ)) (J : ℤ)).erase 0

def finiteNonzeroLowCarrierCoefficients
    (N M J : ℕ) (a ε : ℝ) (n : ℤ) : ℂ :=
  ∑ ell ∈ finiteNonzeroCarrierSet J,
    nearCarrierDyadicTotalCoefficients N M ell a ε n

/-- Every symmetric finite nonzero carrier block has one energy bound that
is independent of the carrier cutoff `J`. -/
theorem eventually_coefficientEnergy_finiteNonzeroLowCarrier_le
    (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∀ᶠ L : ℝ in atTop, ∀ (N M J : ℕ),
      0 < N → Real.exp L = (N : ℝ) →
      (∀ s ∈ nearCarrierDyadicExponents M,
        (2 ^ s : ℕ) / (N : ℝ) ≤
          Real.exp (-L ^ (1 / 3 : ℝ))) →
      coefficientEnergy
          (finiteNonzeroLowCarrierCoefficients N M J (A / L) ε) ≤
        ENNReal.ofReal (windowCarrierMassConstant ^ 2) *
          nearCarrierLowCommonEnergyBound A L M := by
  have hmodeEventually :=
    eventually_coefficientEnergy_nearCarrierDyadicTotal_le_coeff_sq_mul
      A ε hA hε hεhalf
  filter_upwards [hmodeEventually] with L hmode
  intro N M J hN hNL hcut
  let S := finiteNonzeroCarrierSet J
  let w : ℤ → ℝ := fun ell ↦ ‖bernoulliMarkFourierCoefficient ell‖
  let B := nearCarrierLowCommonEnergyBound A L M
  have hell (ell : ℤ) (hellS : ell ∈ S) : ell ≠ 0 := by
    exact Finset.ne_of_mem_erase (by simpa only [S] using! hellS)
  have hcommon := coefficientEnergy_finset_sum_le_weighted_common
    S (fun ell ↦ nearCarrierDyadicTotalCoefficients
      N M ell (A / L) ε) w B
    (fun ell _hellS ↦ norm_bernoulliMarkFourierCoefficient_pos ell)
    (fun ell hellS ↦ hmode N M ell hN (hell ell hellS) hNL hcut)
  have hweight : (∑ ell ∈ S, w ell) ≤ windowCarrierMassConstant := by
    calc
      (∑ ell ∈ S, w ell) ≤
          ∑ ell ∈ S, bernoulliCarrierMajorant ell := by
        apply Finset.sum_le_sum
        intro ell _hellS
        exact norm_bernoulliMarkFourierCoefficient_le_majorant ell
      _ ≤ windowCarrierMassConstant := sum_bernoulliCarrierMajorant_le S
  have hsumNonneg : 0 ≤ ∑ ell ∈ S, w ell :=
    Finset.sum_nonneg fun ell _hell ↦ (norm_nonneg _)
  have hmassNonneg : 0 ≤ windowCarrierMassConstant :=
    windowCarrierMassConstant_nonneg
  calc
    coefficientEnergy
        (finiteNonzeroLowCarrierCoefficients N M J (A / L) ε) ≤
      ENNReal.ofReal ((∑ ell ∈ S, w ell) ^ 2) * B := by
        simpa only [finiteNonzeroLowCarrierCoefficients, S, w, B] using! hcommon
    _ ≤ ENNReal.ofReal (windowCarrierMassConstant ^ 2) * B := by
      gcongr

def finiteNonzeroHighCarrierCoefficients
    (N S H J : ℕ) (a ε : ℝ) (n : ℤ) : ℂ :=
  ∑ ell ∈ finiteNonzeroCarrierSet J,
    nearCarrierDyadicRangeTotalCoefficients N S H ell a ε n

theorem coefficientEnergy_finiteNonzeroHighCarrier_le
    (N S H J : ℕ) (a ε : ℝ)
    (hS : 2 ≤ S) (ha : 0 < a) (hε : 0 < ε)
    (haε : a ≤ ε / 4) (hεhalf : ε < 1 / 2) :
    coefficientEnergy
        (finiteNonzeroHighCarrierCoefficients N S H J a ε) ≤
      ENNReal.ofReal (windowCarrierMassConstant ^ 2) *
        nearCarrierHighCommonEnergyBound a H := by
  let T := finiteNonzeroCarrierSet J
  let w : ℤ → ℝ := fun ell ↦ ‖bernoulliMarkFourierCoefficient ell‖
  let B := nearCarrierHighCommonEnergyBound a H
  have hcommon := coefficientEnergy_finset_sum_le_weighted_common
    T (fun ell ↦ nearCarrierDyadicRangeTotalCoefficients
      N S H ell a ε) w B
    (fun ell _hell ↦ norm_bernoulliMarkFourierCoefficient_pos ell)
    (fun ell _hell ↦
      coefficientEnergy_nearCarrierDyadicRangeTotalCoefficients_le_coeff_sq_mul
        N S H ell a ε hS ha hε haε hεhalf)
  have hweight : (∑ ell ∈ T, w ell) ≤ windowCarrierMassConstant := by
    calc
      (∑ ell ∈ T, w ell) ≤
          ∑ ell ∈ T, bernoulliCarrierMajorant ell := by
        apply Finset.sum_le_sum
        intro ell _hell
        exact norm_bernoulliMarkFourierCoefficient_le_majorant ell
      _ ≤ windowCarrierMassConstant := sum_bernoulliCarrierMajorant_le T
  have hsumNonneg : 0 ≤ ∑ ell ∈ T, w ell :=
    Finset.sum_nonneg fun ell _hell ↦ norm_nonneg _
  calc
    coefficientEnergy
        (finiteNonzeroHighCarrierCoefficients N S H J a ε) ≤
      ENNReal.ofReal ((∑ ell ∈ T, w ell) ^ 2) * B := by
        simpa only [finiteNonzeroHighCarrierCoefficients, T, w, B] using! hcommon
    _ ≤ ENNReal.ofReal (windowCarrierMassConstant ^ 2) * B := by
      gcongr

end

end Erdos1002
