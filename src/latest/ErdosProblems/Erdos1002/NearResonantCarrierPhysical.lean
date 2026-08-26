import ErdosProblems.Erdos1002.NearResonantPhysicalParseval
import ErdosProblems.Erdos1002.FourierSeries

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Physical Bernoulli carriers for the near-resonant pole

The zero-carrier near pole is connected to the reciprocal-Ramanujan vector
in `NearResonantPhysicalParseval`.  This file records the corresponding
identity for every nonzero Fourier carrier of the Bernoulli mark.  The key
point is that on the reduced cell indexed by `(p,q)` one has

`e(ell * N * (p * alpha - q)) = e(ell * N * p * alpha)`.

Consequently multiplication by the `ell`-th Bernoulli carrier translates
the Fourier coefficients by the *integer* frequency `ell * N * p`.  The
statements below are exact identities for the actual smooth physical
function; no formal coefficient sequence is substituted for it.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators ComplexConjugate ENNReal

namespace Erdos1002

noncomputable section

private theorem paperExp_add_carrier (u v : ℝ) :
    paperExp u * paperExp v = paperExp (u + v) := by
  unfold paperExp
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem paperExp_int_carrier (z : ℤ) :
    paperExp (z : ℝ) = 1 := by
  unfold paperExp
  convert! Complex.exp_int_mul_two_pi_mul_I z using 2
  push_cast
  ring

/-- Integer frequency carried by the `ell`-th Bernoulli mode on the
denominator-`p` primitive pole. -/
def nearBernoulliCarrierFrequency (N p : ℕ) (ell : ℤ) : ℤ :=
  ell * ((N * p : ℕ) : ℤ)

/-- The cell phase `e(ell N (p alpha-q))` loses its integral `q`-part
exactly, not merely almost everywhere. -/
theorem paperExp_nearCell_carrier_eq
    (N p q : ℕ) (ell : ℤ) (alpha : ℝ) :
    paperExp
        ((ell : ℝ) * (N : ℝ) *
          ((p : ℝ) * alpha - (q : ℝ))) =
      paperExp ((nearBernoulliCarrierFrequency N p ell : ℤ) * alpha) := by
  have harg :
      (ell : ℝ) * (N : ℝ) * ((p : ℝ) * alpha - (q : ℝ)) =
        (nearBernoulliCarrierFrequency N p ell : ℝ) * alpha +
          ((-(ell * (N : ℤ) * (q : ℤ)) : ℤ) : ℝ) := by
    unfold nearBernoulliCarrierFrequency
    push_cast
    ring
  rw [harg, ← paperExp_add_carrier, paperExp_int_carrier, mul_one]

/-- Multiplication by a unit-period integer character. -/
def unitModulate (m : ℤ) (f : ℝ → ℂ) (alpha : ℝ) : ℂ :=
  paperExp ((m : ℝ) * alpha) * f alpha

/-- Exact Fourier translation under an integer modulation. -/
theorem unitFourierCoefficientInt_unitModulate
    (m n : ℤ) (f : ℝ → ℂ) :
    unitFourierCoefficientInt (unitModulate m f) n =
      unitFourierCoefficientInt f (n - m) := by
  unfold unitFourierCoefficientInt unitModulate
  apply intervalIntegral.integral_congr
  intro alpha _halpha
  calc
    (paperExp ((m : ℝ) * alpha) * f alpha) *
        paperExp (-(n : ℝ) * alpha) =
      f alpha *
        (paperExp ((m : ℝ) * alpha) *
          paperExp (-(n : ℝ) * alpha)) := by ring
    _ = f alpha *
        paperExp ((m : ℝ) * alpha + -(n : ℝ) * alpha) := by
      rw [paperExp_add_carrier]
    _ = f alpha * paperExp (-((n - m : ℤ) : ℝ) * alpha) := by
      congr 2
      push_cast
      ring

theorem unitFourierCoefficientInt_const_mul
    (c : ℂ) (f : ℝ → ℂ) (n : ℤ) :
    unitFourierCoefficientInt (fun alpha ↦ c * f alpha) n =
      c * unitFourierCoefficientInt f n := by
  unfold unitFourierCoefficientInt
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro alpha _halpha
  ring

/-- The actual physical `ell`-carrier of one denominator. -/
def smoothNearPrimitivePoleCarrierTerm
    (N : ℕ) (ell : ℤ) (a ε : ℝ) (p : ℕ) (alpha : ℝ) : ℂ :=
  bernoulliMarkFourierCoefficient ell *
    unitModulate (nearBernoulliCarrierFrequency N p ell)
      (smoothNearPrimitivePoleSum a ε p) alpha

/-- At every integer frequency, the actual carrier term has exactly the
coefficient sequence `modulateCoefficients` used by the abstract leakage
lemmas. -/
theorem unitFourierCoefficientInt_smoothNearPrimitivePoleCarrierTerm
    (N p : ℕ) (ell n : ℤ) (a ε : ℝ) :
    unitFourierCoefficientInt
        (smoothNearPrimitivePoleCarrierTerm N ell a ε p) n =
      bernoulliMarkFourierCoefficient ell *
        modulateCoefficients (nearBernoulliCarrierFrequency N p ell)
          (unitFourierCoefficientInt
            (smoothNearPrimitivePoleSum a ε p)) n := by
  unfold smoothNearPrimitivePoleCarrierTerm
  rw [unitFourierCoefficientInt_const_mul,
    unitFourierCoefficientInt_unitModulate]
  rfl

/-- Exact leakage identity for an actual physical carrier.  The unshifted
sequence on the right is the Fourier sequence of the smooth primitive pole,
scaled by the corresponding Bernoulli coefficient. -/
theorem coefficientEnergy_physicalNearCarrier_sub_projection
    (N p : ℕ) (ell : ℤ) (a ε : ℝ) (A : Set ℤ) :
    coefficientEnergy (fun n ↦
      unitFourierCoefficientInt
          (smoothNearPrimitivePoleCarrierTerm N ell a ε p) n -
        projectCoefficients A
          (unitFourierCoefficientInt
            (smoothNearPrimitivePoleCarrierTerm N ell a ε p)) n) =
      fourierLeakageEnergy A (nearBernoulliCarrierFrequency N p ell)
        (fun k ↦ bernoulliMarkFourierCoefficient ell *
          unitFourierCoefficientInt
            (smoothNearPrimitivePoleSum a ε p) k) := by
  let c : ℤ → ℂ := fun k ↦ bernoulliMarkFourierCoefficient ell *
    unitFourierCoefficientInt (smoothNearPrimitivePoleSum a ε p) k
  have hcoeff :
      unitFourierCoefficientInt
          (smoothNearPrimitivePoleCarrierTerm N ell a ε p) =
        modulateCoefficients (nearBernoulliCarrierFrequency N p ell) c := by
    funext n
    rw [unitFourierCoefficientInt_smoothNearPrimitivePoleCarrierTerm]
    rfl
  rw [hcoeff]
  exact coefficientEnergy_modulate_sub_projection
    A (nearBernoulliCarrierFrequency N p ell) c

/-- Derivative-energy control of the leakage of an actual physical carrier,
with every `j`-dependent factor explicit. -/
theorem coefficientEnergy_physicalNearCarrier_le_derivativeEnergy
    (N p : ℕ) (ell : ℤ) (a ε : ℝ) (A : Set ℤ)
    (D : ℝ) (j : ℕ) (hD : 0 ≤ D)
    (hsep : ∀ k : ℤ,
      nearBernoulliCarrierFrequency N p ell + k ∉ A →
        D ≤ |(k : ℝ)|) :
    ENNReal.ofReal ((2 * Real.pi * D) ^ (2 * j)) *
        coefficientEnergy (fun n ↦
          unitFourierCoefficientInt
              (smoothNearPrimitivePoleCarrierTerm N ell a ε p) n -
            projectCoefficients A
              (unitFourierCoefficientInt
                (smoothNearPrimitivePoleCarrierTerm N ell a ε p)) n) ≤
      fourierDerivativeEnergy j
        (fun k ↦ bernoulliMarkFourierCoefficient ell *
          unitFourierCoefficientInt
            (smoothNearPrimitivePoleSum a ε p) k) := by
  rw [coefficientEnergy_physicalNearCarrier_sub_projection]
  exact fourierLeakageEnergy_scaled_le
    A (nearBernoulliCarrierFrequency N p ell)
      (fun k ↦ bernoulliMarkFourierCoefficient ell *
        unitFourierCoefficientInt
          (smoothNearPrimitivePoleSum a ε p) k)
      D j hD hsep

/-- The coefficient of the physical carrier on its translated dyadic
coordinate is exactly the unmodulated reciprocal-Ramanujan coefficient,
including the Bernoulli Fourier coefficient. -/
theorem unitFourierCoefficientInt_smoothNearPrimitivePoleCarrierTerm_eq
    (N p k : ℕ) (ell : ℤ) (a ε : ℝ)
    (hp : 2 ≤ p) (ha : 0 < a) (hε : 0 < ε)
    (haε : a ≤ ε / 4) (hεhalf : ε ≤ 1 / 2) :
    unitFourierCoefficientInt
        (smoothNearPrimitivePoleCarrierTerm N ell a ε p)
        (nearBernoulliCarrierFrequency N p ell + (k : ℤ)) =
      bernoulliMarkFourierCoefficient ell *
        (((1 / (p : ℝ) ^ 2 : ℝ) : ℂ) *
          ramanujanSum p (k : ℤ) *
            nearJ a ε ((k : ℝ) / (p : ℝ) ^ 2)) := by
  unfold smoothNearPrimitivePoleCarrierTerm
  rw [unitFourierCoefficientInt_const_mul,
    unitFourierCoefficientInt_unitModulate]
  have hsub : nearBernoulliCarrierFrequency N p ell + (k : ℤ) -
      nearBernoulliCarrierFrequency N p ell = (k : ℤ) := by omega
  rw [hsub, unitFourierCoefficientInt_natCast,
    unitFourierCoefficient_smoothNearPrimitivePoleSum_eq
      a ε k p hp ha hε haε hεhalf]

/-- A finite sum of the actual `ell`-carrier over a denominator interval.
The carrier frequency is allowed to depend on `p`, as it must in the
physical near-resonant sum. -/
def smoothNearPrimitivePoleCarrierTail
    (N : ℕ) (ell : ℤ) (a ε : ℝ) (Q U : ℕ) (alpha : ℝ) : ℂ :=
  ∑ p ∈ Finset.Ioc Q U,
    smoothNearPrimitivePoleCarrierTerm N ell a ε p alpha

theorem smoothNearPrimitivePoleCarrierTerm_continuous
    (N p : ℕ) (ell : ℤ) (a ε : ℝ)
    (ha : 0 < a) (haε : a ≤ ε / 4) :
    Continuous (smoothNearPrimitivePoleCarrierTerm N ell a ε p) := by
  unfold smoothNearPrimitivePoleCarrierTerm unitModulate
  have hphase : Continuous (fun alpha : ℝ ↦
      paperExp ((nearBernoulliCarrierFrequency N p ell : ℝ) * alpha)) := by
    unfold paperExp
    fun_prop
  exact continuous_const.mul
    (hphase.mul
      (smoothNearPrimitivePoleSum_contDiff a ε p ha haε).continuous)

theorem smoothNearPrimitivePoleCarrierTail_continuous
    (N Q U : ℕ) (ell : ℤ) (a ε : ℝ)
    (ha : 0 < a) (haε : a ≤ ε / 4) :
    Continuous (smoothNearPrimitivePoleCarrierTail N ell a ε Q U) := by
  unfold smoothNearPrimitivePoleCarrierTail
  apply continuous_finset_sum
  intro p _hp
  exact smoothNearPrimitivePoleCarrierTerm_continuous
    N p ell a ε ha haε

/-- Exact coefficient-level recombination over a finite denominator tail.
In particular, the abstract modulation sequence in
`NearResonantMultipliers` is now identified with the Fourier coefficients
of the physical carrier sum. -/
theorem unitFourierCoefficientInt_smoothNearPrimitivePoleCarrierTail
    (N Q U : ℕ) (ell n : ℤ) (a ε : ℝ)
    (ha : 0 < a) (haε : a ≤ ε / 4) :
    unitFourierCoefficientInt
        (smoothNearPrimitivePoleCarrierTail N ell a ε Q U) n =
      ∑ p ∈ Finset.Ioc Q U,
        bernoulliMarkFourierCoefficient ell *
          modulateCoefficients (nearBernoulliCarrierFrequency N p ell)
            (unitFourierCoefficientInt
              (smoothNearPrimitivePoleSum a ε p)) n := by
  unfold unitFourierCoefficientInt smoothNearPrimitivePoleCarrierTail
  rw [show (fun alpha ↦
      (∑ p ∈ Finset.Ioc Q U,
          smoothNearPrimitivePoleCarrierTerm N ell a ε p alpha) *
        paperExp (-(n : ℝ) * alpha)) =
      (fun alpha ↦ ∑ p ∈ Finset.Ioc Q U,
        smoothNearPrimitivePoleCarrierTerm N ell a ε p alpha *
          paperExp (-(n : ℝ) * alpha)) by
    funext alpha
    rw [Finset.sum_mul]]
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro p _hp
    simpa only [unitFourierCoefficientInt] using!
      unitFourierCoefficientInt_smoothNearPrimitivePoleCarrierTerm
        N p ell n a ε
  · intro p _hp
    have hphase : Continuous
        (fun alpha : ℝ ↦ paperExp (-(n : ℝ) * alpha)) := by
      unfold paperExp
      fun_prop
    exact ((smoothNearPrimitivePoleCarrierTerm_continuous
      N p ell a ε ha haε).mul hphase).intervalIntegrable 0 1

/-- The bounded-overlap square estimate instantiated with the *physical*
one-denominator carrier coefficients.  All later use of carrier annuli can
therefore be phrased directly in terms of these functions. -/
theorem coefficientEnergy_sum_projected_physicalNearCarriers_le_overlap
    (N : ℕ) (ell : ℤ) (a ε : ℝ) (s : Finset ℕ)
    (A : ℕ → Set ℤ) (B : ℕ)
    (hoverlap : ∀ n : ℤ, frequencyOverlapCount s A n ≤ B) :
    coefficientEnergy (fun n ↦
      ∑ p ∈ s, projectCoefficients (A p)
        (unitFourierCoefficientInt
          (smoothNearPrimitivePoleCarrierTerm N ell a ε p)) n) ≤
      B * ∑ p ∈ s, coefficientEnergy
        (unitFourierCoefficientInt
          (smoothNearPrimitivePoleCarrierTerm N ell a ε p)) := by
  exact coefficientEnergy_sum_projected_le_overlap
    s A
      (fun p ↦ unitFourierCoefficientInt
        (smoothNearPrimitivePoleCarrierTerm N ell a ε p))
      B hoverlap

/-- Expanding the finite carrier tail produces precisely the sum of its
physical denominator carriers.  This small theorem is useful as a rewrite
boundary before applying carrier-annulus projections. -/
theorem smoothNearPrimitivePoleCarrierTail_apply
    (N : ℕ) (ell : ℤ) (a ε : ℝ) (Q U : ℕ) (alpha : ℝ) :
    smoothNearPrimitivePoleCarrierTail N ell a ε Q U alpha =
      ∑ p ∈ Finset.Ioc Q U,
        bernoulliMarkFourierCoefficient ell *
          paperExp
            ((nearBernoulliCarrierFrequency N p ell : ℤ) * alpha) *
          smoothNearPrimitivePoleSum a ε p alpha := by
  unfold smoothNearPrimitivePoleCarrierTail
    smoothNearPrimitivePoleCarrierTerm unitModulate
  apply Finset.sum_congr rfl
  intro p _hp
  ring

end

end Erdos1002
