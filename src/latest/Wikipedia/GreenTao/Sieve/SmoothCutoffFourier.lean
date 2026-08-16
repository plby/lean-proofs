import Wikipedia.GreenTao.Sieve.SmoothCutoff
import Wikipedia.GreenTao.Sieve.TruncatedDivisorSum
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Tactic

/-!
# Fourier inversion for the smooth sieve cutoff

This file supplies the analytic transform used in the Goldston--Yıldırım
calculation.  For a smooth sieve cutoff `χ`, put

`g(x) = exp(x) χ(x)`.

We regard `g` as complex-valued and use Mathlib's analyst normalization

`𝓕 g(t) = ∫ x, exp(-2 π i x t) g(x)`.

The function `g` is smooth and compactly supported, hence is a Schwartz
function.  Its Fourier transform is therefore again Schwartz and in
particular integrable.  Fourier inversion gives

`χ(x) = ∫ t, 𝓕 g(t) exp(-x + 2 π i t x)`.

At `x = log d / log R`, the last exponential is multiplicative in `d`.
The final results interchange this integral with the finite divisor sums
that occur in the truncated divisor sum.
-/

namespace Wikipedia.SzemeredisTheorem

open Function MeasureTheory
open scoped ArithmeticFunction.Moebius BigOperators FourierTransform
  ContDiff SchwartzMap

namespace SmoothSieveCutoff

/-- The compactly supported function to which Fourier inversion is applied:
`g(x) = exp(x) χ(x)`, regarded as complex-valued. -/
noncomputable def fourierInput (χ : SmoothSieveCutoff) (x : ℝ) : ℂ :=
  ((Real.exp x * χ x : ℝ) : ℂ)

/-- The Fourier input is infinitely differentiable. -/
theorem fourierInput_contDiff (χ : SmoothSieveCutoff) :
    ContDiff ℝ ∞ χ.fourierInput := by
  have hspace :
      (NormedField.toNormedSpace : NormedSpace ℝ ℝ) =
        RCLike.toInnerProductSpaceReal.toNormedSpace :=
    NormedSpace.ext rfl
  rw [← hspace]
  change
    ContDiff ℝ ∞
      (Complex.ofRealCLM ∘ fun x : ℝ ↦ Real.exp x * χ.toFun x)
  exact
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.mul χ.smooth)

/-- The exponential factor does not enlarge the support of the cutoff. -/
theorem fourierInput_hasCompactSupport (χ : SmoothSieveCutoff) :
    HasCompactSupport χ.fourierInput := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro x hx
  apply χ.support_subset
  intro hχ
  apply hx
  simp [fourierInput, hχ]

/-- The Fourier input packaged as a Schwartz function. -/
noncomputable def fourierInputSchwartz
    (χ : SmoothSieveCutoff) : 𝓢(ℝ, ℂ) :=
  χ.fourierInput_hasCompactSupport.toSchwartzMap χ.fourierInput_contDiff

@[simp]
theorem fourierInputSchwartz_apply
    (χ : SmoothSieveCutoff) (x : ℝ) :
    χ.fourierInputSchwartz x = χ.fourierInput x :=
  rfl

/-- The Fourier transform of `x ↦ exp(x) χ(x)`, with Mathlib's analyst
normalization. -/
noncomputable def cutoffFourierTransform
    (χ : SmoothSieveCutoff) (t : ℝ) : ℂ :=
  𝓕 χ.fourierInput t

/-- The same transform, retaining its Schwartz-space structure. -/
noncomputable def cutoffFourierSchwartz
    (χ : SmoothSieveCutoff) : 𝓢(ℝ, ℂ) :=
  𝓕 χ.fourierInputSchwartz

@[simp]
theorem cutoffFourierSchwartz_apply
    (χ : SmoothSieveCutoff) (t : ℝ) :
    χ.cutoffFourierSchwartz t = χ.cutoffFourierTransform t :=
  rfl

/-- Explicit record of Mathlib's Fourier normalization. -/
theorem cutoffFourierTransform_eq_integral
    (χ : SmoothSieveCutoff) (t : ℝ) :
    χ.cutoffFourierTransform t =
      ∫ x : ℝ,
        Complex.exp
            (((-2 * Real.pi * inner ℝ x t : ℝ) : ℂ) * Complex.I) •
          χ.fourierInput x := by
  exact Real.fourier_eq' χ.fourierInput t

/-- The Fourier input is integrable. -/
theorem fourierInput_integrable (χ : SmoothSieveCutoff) :
    Integrable χ.fourierInput := by
  change Integrable (χ.fourierInputSchwartz : ℝ → ℂ)
  exact χ.fourierInputSchwartz.integrable

/-- The cutoff transform is integrable, as needed for pointwise Fourier
inversion. -/
theorem cutoffFourierTransform_integrable (χ : SmoothSieveCutoff) :
    Integrable χ.cutoffFourierTransform := by
  change Integrable (χ.cutoffFourierSchwartz : ℝ → ℂ)
  exact χ.cutoffFourierSchwartz.integrable

/-- The cutoff transform is continuous. -/
theorem cutoffFourierTransform_continuous (χ : SmoothSieveCutoff) :
    Continuous χ.cutoffFourierTransform := by
  change Continuous (χ.cutoffFourierSchwartz : ℝ → ℂ)
  exact χ.cutoffFourierSchwartz.continuous

/-- The full rapid-decay package for the Fourier transform.  In particular,
this controls every derivative after multiplication by every polynomial
weight. -/
theorem cutoffFourierSchwartz_decay
    (χ : SmoothSieveCutoff) (k n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ t : ℝ,
        ‖t‖ ^ k *
            ‖iteratedFDeriv ℝ n χ.cutoffFourierSchwartz t‖ ≤ C :=
  χ.cutoffFourierSchwartz.decay k n

/-- The zeroth-derivative specialization of rapid decay, stated directly
for the ordinary Fourier transform. -/
theorem cutoffFourierTransform_rapidDecay
    (χ : SmoothSieveCutoff) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ t : ℝ, ‖t‖ ^ k * ‖χ.cutoffFourierTransform t‖ ≤ C := by
  simpa only [norm_iteratedFDeriv_zero, cutoffFourierSchwartz_apply] using
    χ.cutoffFourierSchwartz.decay k 0

/-- The positive-sign character in the inverse Fourier transform. -/
noncomputable def inverseFourierCharacter (x t : ℝ) : ℂ :=
  Complex.exp
    (((2 * Real.pi * (t * x) : ℝ) : ℂ) * Complex.I)

@[simp]
theorem norm_inverseFourierCharacter (x t : ℝ) :
    ‖inverseFourierCharacter x t‖ = 1 := by
  rw [inverseFourierCharacter, Complex.norm_exp]
  simp

theorem continuous_inverseFourierCharacter (x : ℝ) :
    Continuous (inverseFourierCharacter x) := by
  unfold inverseFourierCharacter
  fun_prop

/-- Multiplying the integrable Fourier transform by an inverse Fourier
character preserves integrability. -/
theorem integrable_cutoffFourierTransform_mul_inverseFourierCharacter
    (χ : SmoothSieveCutoff) (x : ℝ) :
    Integrable
      (fun t : ℝ ↦
        χ.cutoffFourierTransform t * inverseFourierCharacter x t) := by
  refine χ.cutoffFourierTransform_integrable.mul_bdd
    (c := 1) ?_ ?_
  · exact (continuous_inverseFourierCharacter x).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t ↦ by
      rw [norm_inverseFourierCharacter]

/-- Pointwise Fourier inversion for the exponentially weighted cutoff. -/
theorem fourierInput_eq_integral
    (χ : SmoothSieveCutoff) (x : ℝ) :
    χ.fourierInput x =
      ∫ t : ℝ,
        χ.cutoffFourierTransform t *
          inverseFourierCharacter x t := by
  have hinversion :
      𝓕⁻ (𝓕 χ.fourierInput) x = χ.fourierInput x :=
    χ.fourierInput_integrable.fourierInv_fourier_eq
      χ.cutoffFourierTransform_integrable
      χ.fourierInput_contDiff.continuous.continuousAt
  rw [Real.fourierInv_eq'] at hinversion
  symm
  simpa only [cutoffFourierTransform, inverseFourierCharacter,
    RCLike.inner_apply, conj_trivial, Complex.real_smul, smul_eq_mul,
    mul_comm] using hinversion

/-- The phase appearing after removing the factor `exp(x)` from the Fourier
input. -/
noncomputable def cutoffMultiplicativePhase (x t : ℝ) : ℂ :=
  Complex.exp
    (-(x : ℂ) +
      ((2 * Real.pi * (t * x) : ℝ) : ℂ) * Complex.I)

/-- The cutoff phase is the inverse Fourier character times the real
exponential `exp(-x)`. -/
theorem cutoffMultiplicativePhase_eq
    (x t : ℝ) :
    cutoffMultiplicativePhase x t =
      (Real.exp (-x) : ℂ) * inverseFourierCharacter x t := by
  simp only [cutoffMultiplicativePhase, inverseFourierCharacter,
    Complex.exp_add, Complex.ofReal_neg, Complex.ofReal_exp]

/-- The cutoff phase is additive-to-multiplicative in its logarithmic
variable. -/
theorem cutoffMultiplicativePhase_add
    (x y t : ℝ) :
    cutoffMultiplicativePhase (x + y) t =
      cutoffMultiplicativePhase x t *
        cutoffMultiplicativePhase y t := by
  rw [cutoffMultiplicativePhase, cutoffMultiplicativePhase,
    cutoffMultiplicativePhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The integrand in the cutoff inversion formula is integrable. -/
theorem integrable_cutoffFourierTransform_mul_cutoffMultiplicativePhase
    (χ : SmoothSieveCutoff) (x : ℝ) :
    Integrable
      (fun t : ℝ ↦
        χ.cutoffFourierTransform t *
          cutoffMultiplicativePhase x t) := by
  have h :=
    (χ.integrable_cutoffFourierTransform_mul_inverseFourierCharacter x).mul_const
      (Real.exp (-x) : ℂ)
  convert h using 1
  funext t
  rw [cutoffMultiplicativePhase_eq]
  ring

/-- Pointwise Fourier inversion in the form used by the
Goldston--Yıldırım divisor sum. -/
theorem cutoff_eq_integral
    (χ : SmoothSieveCutoff) (x : ℝ) :
    (χ x : ℂ) =
      ∫ t : ℝ,
        χ.cutoffFourierTransform t *
          cutoffMultiplicativePhase x t := by
  calc
    (χ x : ℂ) =
        (Real.exp (-x) : ℂ) * χ.fourierInput x := by
          rw [fourierInput]
          push_cast
          rw [← mul_assoc, ← Complex.exp_add]
          simp
    _ = (Real.exp (-x) : ℂ) *
          ∫ t : ℝ,
            χ.cutoffFourierTransform t *
              inverseFourierCharacter x t := by
          rw [χ.fourierInput_eq_integral x]
    _ = ∫ t : ℝ,
          (Real.exp (-x) : ℂ) *
            (χ.cutoffFourierTransform t *
              inverseFourierCharacter x t) := by
          rw [integral_const_mul]
    _ = ∫ t : ℝ,
          χ.cutoffFourierTransform t *
            cutoffMultiplicativePhase x t := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun t ↦ by
            dsimp only
            rw [cutoffMultiplicativePhase_eq]
            ring

/-- The phase specialized to the logarithmic divisor variable. -/
noncomputable def divisorMultiplicativePhase
    (R d : ℕ) (t : ℝ) : ℂ :=
  cutoffMultiplicativePhase
    (Real.log d / Real.log R) t

/-- The name `divisorMultiplicativePhase` is justified literally: it is
multiplicative in positive natural-number arguments. -/
theorem divisorMultiplicativePhase_mul
    (R : ℕ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (t : ℝ) :
    divisorMultiplicativePhase R (d * e) t =
      divisorMultiplicativePhase R d t *
        divisorMultiplicativePhase R e t := by
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have he0 : (e : ℝ) ≠ 0 := by positivity
  rw [divisorMultiplicativePhase, divisorMultiplicativePhase,
    divisorMultiplicativePhase, Nat.cast_mul, Real.log_mul hd0 he0,
    add_div]
  exact cutoffMultiplicativePhase_add _ _ _

/-- Fourier inversion evaluated at the logarithmic divisor variable. -/
theorem cutoff_log_div_log_eq_integral
    (χ : SmoothSieveCutoff) (R d : ℕ) :
    (χ (Real.log d / Real.log R) : ℂ) =
      ∫ t : ℝ,
        χ.cutoffFourierTransform t *
          divisorMultiplicativePhase R d t := by
  exact χ.cutoff_eq_integral (Real.log d / Real.log R)

/-- The integral occurring in a transformed divisor summand is integrable. -/
theorem integrable_transformedSmoothDivisorSummand
    (χ : SmoothSieveCutoff) (R d : ℕ) :
    Integrable
      (fun t : ℝ ↦
        (ArithmeticFunction.moebius d : ℂ) *
          χ.cutoffFourierTransform t *
            divisorMultiplicativePhase R d t) := by
  have h :=
    (χ.integrable_cutoffFourierTransform_mul_cutoffMultiplicativePhase
      (Real.log d / Real.log R)).const_mul
      (ArithmeticFunction.moebius d : ℂ)
  simpa only [divisorMultiplicativePhase, mul_assoc] using h

/-- A single smooth Möbius-divisor summand as a Fourier integral. -/
theorem smoothDivisorSummand_eq_integral
    (χ : SmoothSieveCutoff) (R d : ℕ) :
    (smoothDivisorSummand χ.toFun R d : ℂ) =
      ∫ t : ℝ,
        (ArithmeticFunction.moebius d : ℂ) *
          χ.cutoffFourierTransform t *
            divisorMultiplicativePhase R d t := by
  rw [smoothDivisorSummand]
  push_cast
  rw [χ.cutoff_log_div_log_eq_integral R d, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t ↦ by
    ring

/-- Fourier inversion commutes with any finite sum of smooth divisor
summands.  This is the finite sum/integral interchange used before the
Euler-product calculation. -/
theorem sum_smoothDivisorSummand_eq_integral
    (χ : SmoothSieveCutoff) (R : ℕ) (s : Finset ℕ) :
    (∑ d ∈ s, smoothDivisorSummand χ.toFun R d : ℝ) =
      ∫ t : ℝ,
        ∑ d ∈ s,
          (ArithmeticFunction.moebius d : ℂ) *
            χ.cutoffFourierTransform t *
              divisorMultiplicativePhase R d t := by
  rw [MeasureTheory.integral_finsetSum s]
  · push_cast
    apply Finset.sum_congr rfl
    intro d hd
    exact χ.smoothDivisorSummand_eq_integral R d
  · intro d hd
    exact χ.integrable_transformedSmoothDivisorSummand R d

end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem
