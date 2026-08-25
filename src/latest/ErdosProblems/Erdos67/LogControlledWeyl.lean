import ErdosProblems.Erdos67.LogPhaseHigherDerivative
import ErdosProblems.Erdos67.LogWeylParameters

/-!
# A finite controlled-Weyl estimate for a logarithmic phase

This module closes the finite higher-derivative argument on one dyadic
height band.  It combines the explicit logarithmic leaf condition with the
rounded parameters and the exact finite-history Weyl envelope.

The saving here is the ordinary repeated-Weyl saving `2⁻ˢ`.  The theorem is
therefore a rigorous finite building block, but it is not by itself the
Vinogradov--Korobov estimate when the derivative order grows with the
height.
-/

open scoped BigOperators

namespace Erdos67.LogControlledWeyl

noncomputable section

open Erdos1149
open Erdos67.LogWeylParameters
open Erdos67.LogPhaseHigherDerivative

/-- The exact controlled-Weyl endpoint at an arbitrary positive real start.
This is the source-facing form used after reindexing a residue class.  Its
hypotheses expose precisely the two derivative inequalities and the complete
translation budget; no integrality assumption is made on `U`. -/
theorem norm_sum_shiftedLogPhase_realStart_le_finiteHistory
    {P s K d : ℕ} {a U lam : ℝ}
    (ha : 0 < a) (hU : 0 < U) (hK : 0 < K)
    (hlam : 0 < lam) (hlamhalf : lam ≤ 1 / 2)
    (hwindow : (P : ℝ) + (s : ℝ) * K * d + 1 ≤ 2 * U)
    (hlower : lam ≤ (d : ℝ) ^ s *
      (a * (s.factorial : ℝ) *
        (3 * U) ^ (-((s + 1 : ℕ) : ℤ))))
    (hupper : ((K : ℝ) * d) ^ s *
      (a * (s.factorial : ℝ) * U ^ (-((s + 1 : ℕ) : ℤ))) ≤
        1 - lam) :
    ‖∑ n ∈ Finset.range P,
        HigherDerivative.phase (shiftedLogPhase a U n)‖ ≤
      RestrictedWeyl.finiteHistoryEnvelope P (1 / lam)
        (HigherDerivative.constantControlledSteps s K d hK) := by
  have hleaf : ∀ leaf ∈
      RestrictedWeyl.offDiagonalHistoryLeaves
        (HigherDerivative.constantControlledSteps s K d hK) [],
      HigherDerivative.TerminalIncrementCondition
        (HigherDerivative.iteratedPairDifference
          (fun n : ℕ ↦ shiftedLogPhase a U ((0 + n : ℕ) : ℝ)) leaf) P lam := by
    intro leaf hleafMem
    simpa only [Nat.zero_add] using
      terminalIncrementCondition_shiftedLog ha hU hK leaf hleafMem
        hwindow hlower hupper
  simpa only [zero_add] using
    HigherDerivative.norm_phaseSum_add_le_controlled_of_terminalIncrements
      (fun n ↦ shiftedLogPhase a U n) 0 P
      (HigherDerivative.constantControlledSteps s K d hK)
      lam hlam hlamhalf hleaf

private theorem zpow_neg_nat_anti_of_le
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (m : ℕ) :
    y ^ (-(m : ℤ)) ≤ x ^ (-(m : ℤ)) := by
  simp only [zpow_neg, zpow_natCast]
  exact inv_anti₀ (pow_pos hx m) (pow_le_pow_left₀ hx.le hxy m)

private theorem scaled_lower_zpow
    {X U : ℝ} (hX : 0 < X) (hU : 0 < U) (hUX : U ≤ 2 * X)
    (m : ℕ) :
    (3 * X) ^ (-(m : ℤ)) / (2 : ℝ) ^ m ≤
      (3 * U) ^ (-(m : ℤ)) := by
  have h3 : 3 * U ≤ 2 * (3 * X) := by nlinarith
  have hleft :
      (3 * X) ^ (-(m : ℤ)) / (2 : ℝ) ^ m =
        (2 * (3 * X)) ^ (-(m : ℤ)) := by
    simp only [zpow_neg, zpow_natCast, mul_pow]
    rw [mul_inv_rev]
    ring
  rw [hleft]
  exact zpow_neg_nat_anti_of_le (mul_pos (by norm_num) hU) h3 m

/-- Fixed-depth power saving at an arbitrary real start within a factor two
of the natural comparison scale.  The factor `2^(depth+1)` in the terminal
constant is the complete price of replacing the lower derivative bound at
`3*X` by the one at `3*U`; the upper derivative bound only improves because
`X ≤ U`. -/
theorem norm_sum_shiftedLogPhase_realStart_le_of_lower_or_rawStepScale_le
    {r X P : ℕ} {a U : ℝ}
    (hr : 2 ≤ r) (hX : 1 ≤ X) (hP : P ≤ X) (ha : 0 < a)
    (hXU : (X : ℝ) ≤ U) (hUX : U ≤ 2 * X)
    (hboundaryInput : (X : ℝ) ^ r ≤ a ∨
      rawStepScale r X a ≤ (X : ℝ) ^ (3 / 4 : ℝ))
    (haupper : a < (X : ℝ) ^ (r + 1))
    (hlarge : IsLargeLogWeylScale r X)
    (hwindow : (P : ℝ) + (depth r : ℝ) * shiftCount r X *
        stepSize r X a + 1 ≤ 2 * U) :
    ‖∑ n ∈ Finset.range P,
        HigherDerivative.phase (shiftedLogPhase a U n)‖ ≤
      AnalyticParameters.envelopeConstant 10
          ((2 : ℝ) ^ (depth r + 1) * terminalConstant r) (depth r) *
        (X : ℝ) ^ (1 - savingExponent r) := by
  let s := depth r
  let K := shiftCount r X
  let d := stepSize r X a
  let lam₀ := terminalLambda r X
  let Cscale : ℝ := (2 : ℝ) ^ (s + 1)
  let lam := lam₀ / Cscale
  have hp := parameters_of_lower_or_rawStepScale_le hr hX ha hboundaryInput
    haupper hlarge
  dsimp only at hp
  have hK : 0 < K := hp.1
  have hd : 0 < d := hp.2.1
  have hupperNumerical := hp.2.2.1
  have hlowerNumerical := hp.2.2.2.1
  have hlam₀ : 0 < lam₀ := hp.2.2.2.2.1
  have hlam₀half : lam₀ ≤ 1 / 2 := hp.2.2.2.2.2.1
  have hKlower := hp.2.2.2.2.2.2.1
  have hKdRaw := hp.2.2.2.2.2.2.2.1
  have hterminalRaw := hp.2.2.2.2.2.2.2.2
  have hXR : 0 < (X : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  have hU : 0 < U := hXR.trans_le hXU
  have hCscale : 0 < Cscale := by dsimp only [Cscale]; positivity
  have hlam : 0 < lam := div_pos hlam₀ hCscale
  have hlamhalf : lam ≤ 1 / 2 := by
    have hCone : 1 ≤ Cscale := by
      dsimp only [Cscale]
      exact one_le_pow₀ (by norm_num)
    exact (div_le_self hlam₀.le hCone).trans hlam₀half
  have hscaleLower := scaled_lower_zpow hXR hU hUX (s + 1)
  have hfactor : 0 ≤ (d : ℝ) ^ s * (a * (s.factorial : ℝ)) := by
    positivity
  have hlower : lam ≤ (d : ℝ) ^ s *
      (a * (s.factorial : ℝ) *
        (3 * U) ^ (-((s + 1 : ℕ) : ℤ))) := by
    have hrewrite :
        ((d : ℝ) ^ s *
            (a * (s.factorial : ℝ) *
              (3 * (X : ℝ)) ^ (-((s + 1 : ℕ) : ℤ)))) / Cscale =
          ((d : ℝ) ^ s * (a * (s.factorial : ℝ))) *
            ((3 * (X : ℝ)) ^ (-((s + 1 : ℕ) : ℤ)) /
              (2 : ℝ) ^ (s + 1)) := by
      dsimp only [Cscale]
      ring
    calc
      lam = lam₀ / Cscale := rfl
      _ ≤ ((d : ℝ) ^ s *
          (a * (s.factorial : ℝ) *
            (3 * (X : ℝ)) ^ (-((s + 1 : ℕ) : ℤ)))) / Cscale := by
        exact div_le_div_of_nonneg_right hlowerNumerical hCscale.le
      _ = ((d : ℝ) ^ s * (a * (s.factorial : ℝ))) *
          ((3 * (X : ℝ)) ^ (-((s + 1 : ℕ) : ℤ)) /
            (2 : ℝ) ^ (s + 1)) := hrewrite
      _ ≤ ((d : ℝ) ^ s * (a * (s.factorial : ℝ))) *
          (3 * U) ^ (-((s + 1 : ℕ) : ℤ)) := by
        exact mul_le_mul_of_nonneg_left hscaleLower hfactor
      _ = (d : ℝ) ^ s *
          (a * (s.factorial : ℝ) *
            (3 * U) ^ (-((s + 1 : ℕ) : ℤ))) := by ring
  have hpowUpper : U ^ (-((s + 1 : ℕ) : ℤ)) ≤
      (X : ℝ) ^ (-((s + 1 : ℕ) : ℤ)) :=
    zpow_neg_nat_anti_of_le hXR hXU (s + 1)
  have hupper : ((K : ℝ) * d) ^ s *
      (a * (s.factorial : ℝ) * U ^ (-((s + 1 : ℕ) : ℤ))) ≤
        1 - lam := by
    calc
      ((K : ℝ) * d) ^ s *
          (a * (s.factorial : ℝ) * U ^ (-((s + 1 : ℕ) : ℤ))) ≤
          ((K : ℝ) * d) ^ s *
            (a * (s.factorial : ℝ) *
              (X : ℝ) ^ (-((s + 1 : ℕ) : ℤ))) := by gcongr
      _ = (K : ℝ) ^ s * (d : ℝ) ^ s *
          (a * (s.factorial : ℝ) *
            (X : ℝ) ^ (-((s + 1 : ℕ) : ℤ))) := by rw [mul_pow]
      _ ≤ 1 / 2 := hupperNumerical
      _ ≤ 1 - lam := by linarith
  have hweyl := norm_sum_shiftedLogPhase_realStart_le_finiteHistory
    ha hU hK hlam hlamhalf
    (by simpa only [s, K, d] using hwindow) hlower hupper
  have hsExp : shiftExponent r ≤ 1 / 8 := by
    unfold shiftExponent
    have hsOne : (1 : ℝ) ≤ depth r := by exact_mod_cast depth_pos r
    have hden : (8 : ℝ) ≤ 8 * depth r := by nlinarith
    exact one_div_le_one_div_of_le (by norm_num) hden
  have hκθ : shiftExponent r ≤ (7 / 8 : ℝ) := by linarith
  have hκδ : shiftExponent r ≤ 2 * (1 / 4 : ℝ) := by linarith
  have htermC : 0 ≤ Cscale * terminalConstant r := by
    dsimp only [Cscale]
    unfold terminalConstant
    positivity
  have hKd : (K : ℝ) * d ≤
      (1 : ℝ) * (X : ℝ) ^ (1 - (1 / 4 : ℝ)) := by
    dsimp only [K, d]
    rw [one_mul, show (1 - (1 / 4 : ℝ)) = 3 / 4 by norm_num]
    exact hKdRaw
  have hterminal0 : 0 ≤ 1 / lam := (one_div_pos.mpr hlam).le
  have hlamInv : 1 / lam = Cscale * (1 / lam₀) := by
    dsimp only [lam]
    field_simp [hlam₀.ne', hCscale.ne']
  have hterminal : 1 / lam ≤
      (Cscale * terminalConstant r) * (X : ℝ) ^ (1 - (7 / 8 : ℝ)) := by
    rw [hlamInv]
    calc
      Cscale * (1 / lam₀) ≤
          Cscale * (terminalConstant r * (X : ℝ) ^ (1 / 8 : ℝ)) := by
        gcongr
      _ = (Cscale * terminalConstant r) *
          (X : ℝ) ^ (1 - (7 / 8 : ℝ)) := by norm_num; ring
  have henv :=
    AnalyticParameters.finiteHistoryEnvelope_replicate_le_rpow
      X P K d s (shiftExponent r) (1 / 4 : ℝ) (7 / 8 : ℝ)
      1 (Cscale * terminalConstant r) (1 / lam)
      hX hP hK (shiftExponent_pos r) (by norm_num) htermC
      hκθ hκδ hKlower hKd hterminal0 hterminal
  norm_num only [one_pow, mul_one] at henv
  calc
    ‖∑ n ∈ Finset.range P,
        HigherDerivative.phase (shiftedLogPhase a U n)‖ ≤
        RestrictedWeyl.finiteHistoryEnvelope P (1 / lam)
          (HigherDerivative.constantControlledSteps s K d hK) := hweyl
    _ ≤ AnalyticParameters.envelopeConstant 10
          (Cscale * terminalConstant r) s *
        (X : ℝ) ^ (1 - savingExponent r) := by
      simpa only [HigherDerivative.constantControlledSteps,
        HigherDerivative.controlledStep, savingExponent, s, K, d] using henv
    _ = _ := by rfl

/-- For fixed depth, the `X^(3/4)` translation budget is eventually smaller
than the spare half of the calculus window. -/
theorem exists_window_threshold (s : ℕ) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀,
      (s : ℝ) * (X : ℝ) ^ (3 / 4 : ℝ) + 1 ≤ X := by
  have ht : Filter.Tendsto (fun X : ℕ ↦ (X : ℝ) ^ (1 / 4 : ℝ))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      tendsto_natCast_atTop_atTop
  obtain ⟨X₁, hX₁⟩ := Filter.eventually_atTop.1
    ((Filter.tendsto_atTop.1 ht) ((s : ℝ) + 1))
  refine ⟨max 1 X₁, ?_⟩
  intro X hX
  have hXone : 1 ≤ X := le_trans (Nat.le_max_left _ _) hX
  have hroot : (s : ℝ) + 1 ≤ (X : ℝ) ^ (1 / 4 : ℝ) :=
    hX₁ X (le_trans (Nat.le_max_right _ _) hX)
  have hone : 1 ≤ (X : ℝ) ^ (3 / 4 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hXone) (by norm_num)
  have hmul : ((s : ℝ) + 1) * (X : ℝ) ^ (3 / 4 : ℝ) ≤ X := by
    calc
      ((s : ℝ) + 1) * (X : ℝ) ^ (3 / 4 : ℝ) ≤
          (X : ℝ) ^ (1 / 4 : ℝ) * (X : ℝ) ^ (3 / 4 : ℝ) := by
        gcongr
      _ = (X : ℝ) ^ ((1 / 4 : ℝ) + 3 / 4) := by
        rw [← Real.rpow_add (by positivity : 0 < (X : ℝ))]
      _ = X := by norm_num
  nlinarith

/-- A checked finite logarithmic-phase estimate in the band
`X^r ≤ a < X^(r+1)`.  The additional window inequality is precisely the
space required by all controlled shifts and the terminal unit increment.

This statement is intentionally honest about the ordinary Weyl exponent:
`savingExponent r = 1 / (8(r+1)2^(r+1))` up to notation. -/
theorem norm_sum_shiftedLogPhase_le_of_lower_or_rawStepScale_le
    {r X P : ℕ} {a : ℝ}
    (hr : 2 ≤ r) (hX : 1 ≤ X) (hP : P ≤ X) (ha : 0 < a)
    (hboundaryInput : (X : ℝ) ^ r ≤ a ∨
      rawStepScale r X a ≤ (X : ℝ) ^ (3 / 4 : ℝ))
    (haupper : a < (X : ℝ) ^ (r + 1))
    (hlarge : IsLargeLogWeylScale r X)
    (hwindow : (P : ℝ) + (depth r : ℝ) * shiftCount r X *
        stepSize r X a + 1 ≤ 2 * X) :
    ‖∑ n ∈ Finset.range P,
        HigherDerivative.phase (shiftedLogPhase a X n)‖ ≤
      AnalyticParameters.envelopeConstant
          10 (terminalConstant r) (depth r) *
        (X : ℝ) ^ (1 - savingExponent r) := by
  let s := depth r
  let K := shiftCount r X
  let d := stepSize r X a
  let lam := terminalLambda r X
  have hp := parameters_of_lower_or_rawStepScale_le hr hX ha hboundaryInput
    haupper hlarge
  dsimp only at hp
  have hK : 0 < K := hp.1
  have hd : 0 < d := hp.2.1
  have hupperNumerical := hp.2.2.1
  have hlowerNumerical := hp.2.2.2.1
  have hlam : 0 < lam := hp.2.2.2.2.1
  have hlamhalf : lam ≤ 1 / 2 := hp.2.2.2.2.2.1
  have hXR : 0 < (X : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  have hlower : lam ≤ (d : ℝ) ^ s *
      (a * (s.factorial : ℝ) *
        (3 * (X : ℝ)) ^ (-((s + 1 : ℕ) : ℤ))) :=
    hlowerNumerical
  have hupper : ((K : ℝ) * d) ^ s *
      (a * (s.factorial : ℝ) *
        (X : ℝ) ^ (-((s + 1 : ℕ) : ℤ))) ≤ 1 - lam := by
    calc
      ((K : ℝ) * d) ^ s *
          (a * (s.factorial : ℝ) *
            (X : ℝ) ^ (-((s + 1 : ℕ) : ℤ))) =
          (K : ℝ) ^ s * (d : ℝ) ^ s *
            (a * (s.factorial : ℝ) *
              (X : ℝ) ^ (-((s + 1 : ℕ) : ℤ))) := by
        rw [mul_pow]
      _ ≤ 1 / 2 := hupperNumerical
      _ ≤ 1 - lam := by linarith
  have hleaf : ∀ leaf ∈
      RestrictedWeyl.offDiagonalHistoryLeaves
        (HigherDerivative.constantControlledSteps s K d hK) [],
      HigherDerivative.TerminalIncrementCondition
        (HigherDerivative.iteratedPairDifference
          (fun n : ℕ ↦ shiftedLogPhase a X ((0 + n : ℕ) : ℝ)) leaf) P lam := by
    intro leaf hleafMem
    simpa only [Nat.zero_add] using
      terminalIncrementCondition_shiftedLog ha hXR hK leaf hleafMem
        (by simpa only [s, K, d] using hwindow) hlower hupper
  have hweyl :=
    HigherDerivative.norm_phaseSum_add_le_controlled_of_terminalIncrements
      (fun n ↦ shiftedLogPhase a X n) 0 P
      (HigherDerivative.constantControlledSteps s K d hK)
      lam hlam hlamhalf hleaf
  have henv := finiteHistoryEnvelope_le_of_lower_or_rawStepScale_le
    hr hX hP ha hboundaryInput haupper hlarge
  calc
    ‖∑ n ∈ Finset.range P,
        HigherDerivative.phase (shiftedLogPhase a X n)‖ ≤
        RestrictedWeyl.finiteHistoryEnvelope P (1 / lam)
          (HigherDerivative.constantControlledSteps s K d hK) := by
      simpa only [zero_add] using hweyl
    _ ≤ AnalyticParameters.envelopeConstant
          10 (terminalConstant r) (depth r) *
        (X : ℝ) ^ (1 - savingExponent r) := by
      simpa only [s, K, d, lam, HigherDerivative.constantControlledSteps,
        HigherDerivative.controlledStep] using henv

/-- Standard height-band form. -/
theorem norm_sum_shiftedLogPhase_le
    {r X P : ℕ} {a : ℝ}
    (hr : 2 ≤ r) (hX : 1 ≤ X) (hP : P ≤ X) (ha : 0 < a)
    (halower : (X : ℝ) ^ r ≤ a)
    (haupper : a < (X : ℝ) ^ (r + 1))
    (hlarge : IsLargeLogWeylScale r X)
    (hwindow : (P : ℝ) + (depth r : ℝ) * shiftCount r X *
        stepSize r X a + 1 ≤ 2 * X) :
    ‖∑ n ∈ Finset.range P,
        HigherDerivative.phase (shiftedLogPhase a X n)‖ ≤
      AnalyticParameters.envelopeConstant
          10 (terminalConstant r) (depth r) *
        (X : ℝ) ^ (1 - savingExponent r) := by
  exact norm_sum_shiftedLogPhase_le_of_lower_or_rawStepScale_le
    hr hX hP ha (Or.inl halower) haupper hlarge hwindow

/-- Overlap-band form, with the raw translation scale checked directly. -/
theorem norm_sum_shiftedLogPhase_le_of_rawStepScale_le
    {r X P : ℕ} {a : ℝ}
    (hr : 2 ≤ r) (hX : 1 ≤ X) (hP : P ≤ X) (ha : 0 < a)
    (hDraw : rawStepScale r X a ≤ (X : ℝ) ^ (3 / 4 : ℝ))
    (haupper : a < (X : ℝ) ^ (r + 1))
    (hlarge : IsLargeLogWeylScale r X)
    (hwindow : (P : ℝ) + (depth r : ℝ) * shiftCount r X *
        stepSize r X a + 1 ≤ 2 * X) :
    ‖∑ n ∈ Finset.range P,
        HigherDerivative.phase (shiftedLogPhase a X n)‖ ≤
      AnalyticParameters.envelopeConstant
          10 (terminalConstant r) (depth r) *
        (X : ℝ) ^ (1 - savingExponent r) := by
  exact norm_sum_shiftedLogPhase_le_of_lower_or_rawStepScale_le
    hr hX hP ha (Or.inr hDraw) haupper hlarge hwindow

end

end Erdos67.LogControlledWeyl
