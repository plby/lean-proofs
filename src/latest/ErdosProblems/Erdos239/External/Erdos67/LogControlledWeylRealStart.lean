import ErdosProblems.Erdos239.External.Erdos67.LogControlledWeyl
import ErdosProblems.Erdos239.External.Erdos67.LogFixedDepth

/-!
# Real-start adapter for logarithmic Weyl sums

Residue classes turn a logarithmic sum over natural numbers into a consecutive
sum whose starting point is a positive real number.  This file transports the
integer-scale controlled-Weyl parameters to that real starting point.  The
effective height

`a * (X / U)^(s+1)`

has exactly the same normalized derivatives at the integer comparison scale
`X` as `a * log (U+x)` has at `U`.
-/

open scoped BigOperators

namespace Erdos67.LogControlledWeylRealStart

noncomputable section

open Erdos1149
open Erdos67.LogWeylParameters
open Erdos67.LogPhaseHigherDerivative

/-- The height seen by the integer-scale parameter package when the actual
positive start of the logarithmic phase is `U`. -/
def effectiveHeight (a U : ℝ) (X s : ℕ) : ℝ :=
  a * ((X : ℝ) / U) ^ (s + 1)

private theorem effectiveHeight_mul_zpow_neg
    {a U : ℝ} {X s : ℕ} (hU : 0 < U) (hX : 0 < X) :
    effectiveHeight a U X s *
        (X : ℝ) ^ (-((s + 1 : ℕ) : ℤ)) =
      a * U ^ (-((s + 1 : ℕ) : ℤ)) := by
  have hXR : (X : ℝ) ≠ 0 := by exact_mod_cast hX.ne'
  simp only [effectiveHeight, zpow_neg, zpow_natCast]
  rw [div_pow]
  field_simp

private theorem effectiveHeight_mul_three_zpow_neg
    {a U : ℝ} {X s : ℕ} (hU : 0 < U) (hX : 0 < X) :
    effectiveHeight a U X s *
        (3 * (X : ℝ)) ^ (-((s + 1 : ℕ) : ℤ)) =
      a * (3 * U) ^ (-((s + 1 : ℕ) : ℤ)) := by
  have hXR : (X : ℝ) ≠ 0 := by exact_mod_cast hX.ne'
  have hUR : U ≠ 0 := hU.ne'
  simp only [effectiveHeight, zpow_neg, zpow_natCast]
  rw [div_pow, mul_pow, mul_pow]
  field_simp

/-- Controlled-Weyl at a positive real start, with all rounding still carried
out at the natural comparison scale `X`. -/
theorem norm_sum_shiftedLogPhase_realStart_le_of_lower_or_rawStepScale_le
    {r X P : ℕ} {a U : ℝ}
    (hr : 2 ≤ r) (hX : 1 ≤ X) (hP : P ≤ X) (ha : 0 < a) (hU : 0 < U)
    (hboundaryInput :
      (X : ℝ) ^ r ≤ effectiveHeight a U X (depth r) ∨
        rawStepScale r X (effectiveHeight a U X (depth r)) ≤
          (X : ℝ) ^ (3 / 4 : ℝ))
    (haupper : effectiveHeight a U X (depth r) < (X : ℝ) ^ (r + 1))
    (hlarge : IsLargeLogWeylScale r X)
    (hwindow : (P : ℝ) + (depth r : ℝ) * shiftCount r X *
        stepSize r X (effectiveHeight a U X (depth r)) + 1 ≤ 2 * U) :
    ‖∑ n ∈ Finset.range P,
        HigherDerivative.phase (shiftedLogPhase a U n)‖ ≤
      AnalyticParameters.envelopeConstant
          10 (terminalConstant r) (depth r) *
        (X : ℝ) ^ (1 - savingExponent r) := by
  let T := effectiveHeight a U X (depth r)
  let s := depth r
  let K := shiftCount r X
  let d := stepSize r X T
  let lam := terminalLambda r X
  have hT : 0 < T := by
    dsimp only [T, effectiveHeight]
    positivity
  have hp := parameters_of_lower_or_rawStepScale_le hr hX hT
    (by simpa only [T] using hboundaryInput)
    (by simpa only [T] using haupper) hlarge
  dsimp only at hp
  have hK : 0 < K := hp.1
  have hd : 0 < d := hp.2.1
  have hupperNumerical := hp.2.2.1
  have hlowerNumerical := hp.2.2.2.1
  have hlam : 0 < lam := hp.2.2.2.2.1
  have hlamhalf : lam ≤ 1 / 2 := hp.2.2.2.2.2.1
  have hXR : 0 < (X : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  have hscaleOne :
      T * (X : ℝ) ^ (-((s + 1 : ℕ) : ℤ)) =
        a * U ^ (-((s + 1 : ℕ) : ℤ)) := by
    simpa only [T, s] using
      (effectiveHeight_mul_zpow_neg (a := a) (U := U)
        (X := X) (s := depth r) hU (by omega))
  have hscaleThree :
      T * (3 * (X : ℝ)) ^ (-((s + 1 : ℕ) : ℤ)) =
        a * (3 * U) ^ (-((s + 1 : ℕ) : ℤ)) := by
    simpa only [T, s] using
      (effectiveHeight_mul_three_zpow_neg (a := a) (U := U)
        (X := X) (s := depth r) hU (by omega))
  have hlower : lam ≤ (d : ℝ) ^ s *
      (a * (s.factorial : ℝ) *
        (3 * U) ^ (-((s + 1 : ℕ) : ℤ))) := by
    calc
      lam ≤ (d : ℝ) ^ s *
          (T * (s.factorial : ℝ) *
            (3 * (X : ℝ)) ^ (-((s + 1 : ℕ) : ℤ))) :=
        hlowerNumerical
      _ = (d : ℝ) ^ s *
          (a * (s.factorial : ℝ) *
            (3 * U) ^ (-((s + 1 : ℕ) : ℤ))) := by
        rw [show T * (s.factorial : ℝ) *
            (3 * (X : ℝ)) ^ (-((s + 1 : ℕ) : ℤ)) =
          (T * (3 * (X : ℝ)) ^ (-((s + 1 : ℕ) : ℤ))) *
            (s.factorial : ℝ) by ring,
          hscaleThree]
        ring
  have hupper : ((K : ℝ) * d) ^ s *
      (a * (s.factorial : ℝ) *
        U ^ (-((s + 1 : ℕ) : ℤ))) ≤ 1 - lam := by
    calc
      ((K : ℝ) * d) ^ s *
          (a * (s.factorial : ℝ) *
            U ^ (-((s + 1 : ℕ) : ℤ))) =
          (K : ℝ) ^ s * (d : ℝ) ^ s *
            (T * (s.factorial : ℝ) *
              (X : ℝ) ^ (-((s + 1 : ℕ) : ℤ))) := by
        rw [mul_pow]
        rw [show T * (s.factorial : ℝ) *
            (X : ℝ) ^ (-((s + 1 : ℕ) : ℤ)) =
          (T * (X : ℝ) ^ (-((s + 1 : ℕ) : ℤ))) *
            (s.factorial : ℝ) by ring,
          hscaleOne]
        ring
      _ ≤ 1 / 2 := hupperNumerical
      _ ≤ 1 - lam := by linarith
  have hleaf : ∀ leaf ∈
      RestrictedWeyl.offDiagonalHistoryLeaves
        (HigherDerivative.constantControlledSteps s K d hK) [],
      HigherDerivative.TerminalIncrementCondition
        (HigherDerivative.iteratedPairDifference
          (fun n : ℕ ↦ shiftedLogPhase a U ((0 + n : ℕ) : ℝ)) leaf) P lam := by
    intro leaf hleafMem
    simpa only [Nat.zero_add] using
      terminalIncrementCondition_shiftedLog ha hU hK leaf hleafMem
        (by simpa only [s, K, d, T] using hwindow) hlower hupper
  have hweyl :=
    HigherDerivative.norm_phaseSum_add_le_controlled_of_terminalIncrements
      (fun n ↦ shiftedLogPhase a U n) 0 P
      (HigherDerivative.constantControlledSteps s K d hK)
      lam hlam hlamhalf hleaf
  have henv := finiteHistoryEnvelope_le_of_lower_or_rawStepScale_le
    hr hX hP hT (by simpa only [T] using hboundaryInput)
      (by simpa only [T] using haupper) hlarge
  calc
    ‖∑ n ∈ Finset.range P,
        HigherDerivative.phase (shiftedLogPhase a U n)‖ ≤
        RestrictedWeyl.finiteHistoryEnvelope P (1 / lam)
          (HigherDerivative.constantControlledSteps s K d hK) := by
      simpa only [zero_add] using hweyl
    _ ≤ AnalyticParameters.envelopeConstant
          10 (terminalConstant r) (depth r) *
        (X : ℝ) ^ (1 - savingExponent r) := by
      simpa only [s, K, d, lam, T,
        HigherDerivative.constantControlledSteps,
        HigherDerivative.controlledStep] using henv

/-- Fixed-depth real-start bounds are uniform once the integer comparison
scale is sufficiently large.  This version uses the robust factor-two
adapter from `LogControlledWeyl`; unlike the exact effective-height version
above, its band conditions remain in terms of the original height `a`. -/
theorem exists_fixedDepth_realStart_threshold (r : ℕ) (hr : 2 ≤ r) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ P ≤ X, ∀ a U : ℝ,
      0 < a → (X : ℝ) ≤ U → U ≤ 2 * X →
      ((X : ℝ) ^ r ≤ a ∨
        rawStepScale r X a ≤ (X : ℝ) ^ (3 / 4 : ℝ)) →
      a < (X : ℝ) ^ (r + 1) →
      ‖∑ n ∈ Finset.range P,
          HigherDerivative.phase (shiftedLogPhase a U n)‖ ≤
        AnalyticParameters.envelopeConstant 10
            ((2 : ℝ) ^ (depth r + 1) * terminalConstant r) (depth r) *
          (X : ℝ) ^ (1 - savingExponent r) := by
  obtain ⟨Xlarge, hlarge⟩ :=
    Filter.eventually_atTop.1 (eventually_isLargeLogWeylScale r)
  obtain ⟨Xwindow, hwindow⟩ :=
    Erdos67.LogControlledWeyl.exists_window_threshold (depth r)
  refine ⟨max 1 (max Xlarge Xwindow), ?_⟩
  intro X hX P hP a U ha hXU hUX hboundary haupper
  have hXone : 1 ≤ X := (Nat.le_max_left 1 _).trans hX
  have hlargeX : IsLargeLogWeylScale r X :=
    hlarge X ((Nat.le_max_left Xlarge Xwindow).trans
      ((Nat.le_max_right 1 (max Xlarge Xwindow)).trans hX))
  have hwindowX :
      (depth r : ℝ) * (X : ℝ) ^ (3 / 4 : ℝ) + 1 ≤ X :=
    hwindow X ((Nat.le_max_right Xlarge Xwindow).trans
      ((Nat.le_max_right 1 (max Xlarge Xwindow)).trans hX))
  have hp := parameters_of_lower_or_rawStepScale_le
    hr hXone ha hboundary haupper hlargeX
  dsimp only at hp
  have hKd : (shiftCount r X : ℝ) * stepSize r X a ≤
      (X : ℝ) ^ (3 / 4 : ℝ) := hp.2.2.2.2.2.2.2.1
  have hPcast : (P : ℝ) ≤ X := by exact_mod_cast hP
  have hfullWindow :
      (P : ℝ) + (depth r : ℝ) * shiftCount r X *
          stepSize r X a + 1 ≤ 2 * U := by
    have hsnonneg : (0 : ℝ) ≤ depth r := by positivity
    have hshift : (depth r : ℝ) *
          ((shiftCount r X : ℝ) * stepSize r X a) ≤
        (depth r : ℝ) * (X : ℝ) ^ (3 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left hKd hsnonneg
    have htwoX : (2 : ℝ) * X ≤ 2 * U := by nlinarith
    calc
      (P : ℝ) + (depth r : ℝ) * shiftCount r X *
          stepSize r X a + 1 ≤
          (X : ℝ) +
            ((depth r : ℝ) * (X : ℝ) ^ (3 / 4 : ℝ) + 1) := by
        nlinarith
      _ ≤ (X : ℝ) + X := by
        simpa [add_comm] using add_le_add_left hwindowX (X : ℝ)
      _ = 2 * X := by ring
      _ ≤ 2 * U := htwoX
  exact _root_.Erdos67.LogControlledWeyl.norm_sum_shiftedLogPhase_realStart_le_of_lower_or_rawStepScale_le
      hr hXone hP ha hXU hUX hboundary haupper hlargeX hfullWindow

end

end Erdos67.LogControlledWeylRealStart
