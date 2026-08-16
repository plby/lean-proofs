import Wikipedia.GreenTao.Sieve.CFZCanonicalDivisorIntegralCancellation
import Wikipedia.GreenTao.Sieve.CFZCanonicalDivisorRankinMassPolylog

/-!
# Vanishing of the canonical divisor-truncation error

The sharp Rankin estimate controls the complementary Fourier region. If
the canonical coordinatewise-truncation discrepancy has zero full-space
integral eventually, the interior box is the negative of that complement.
This file records that composition in the primorial regime.
-/

namespace Wikipedia.SzemeredisTheorem
open Filter MeasureTheory Topology

/-- Eventual full-space cancellation is enough to turn the canonical
Rankin-tail limit into the corresponding growing-box limit. No cancellation
claim is needed at the finitely many radii below the analytic threshold. -/
theorem
    SmoothSieveCutoff.tendsto_selectedCFZCanonicalCarryScaledTruncationBoxNorm_sqrt_log_primorial_of_eventually_integral_zero
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hbound :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k)
    (hzero :
      ∀ᶠ R : ℕ in atTop,
        (∫ tu :
            (SelectedCFZFormIndex e → ℝ) ×
              (SelectedCFZFormIndex e → ℝ),
          cfzCanonicalCarryTruncationDiscrepancy
            (N := N) χ (primorial w) b R
            (fun q : SelectedCFZFormIndex e => q.1)
            tu.1 tu.2
          ∂(volume.prod volume)) = 0) :
    Tendsto
      (fun R : ℕ =>
        χ.selectedCFZCanonicalCarryScaledTruncationBoxNorm
          (N := N) (primorial w) b R e
          (Real.sqrt (Real.log R)))
      atTop (𝓝 0) := by
  have htail :=
    χ.tendsto_selectedCFZCanonicalCarryScaledTruncationTailNorm_sqrt_log_primorial
      (N := N) hk hbound hwb e
  apply htail.congr'
  filter_upwards [eventually_ge_atTop 2, hzero] with R hR hzeroR
  exact
    (χ.selectedCFZCanonicalCarryScaledTruncationBoxNorm_eq_tailNorm
      (N := N) (primorial w) b R e
      (Real.sqrt (Real.log R)) hR hzeroR).symm

/-- **Unconditional canonical truncation limit.** In the primorial regime,
the Selberg-scaled canonical coordinatewise-truncation discrepancy vanishes
on the standard growing Fourier box. -/
theorem
    SmoothSieveCutoff.tendsto_selectedCFZCanonicalCarryScaledTruncationBoxNorm_sqrt_log_primorial
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hbound :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k) :
    Tendsto
      (fun R : ℕ =>
        χ.selectedCFZCanonicalCarryScaledTruncationBoxNorm
          (N := N) (primorial w) b R e
          (Real.sqrt (Real.log R)))
      atTop (𝓝 0) := by
  classical
  apply
    χ.tendsto_selectedCFZCanonicalCarryScaledTruncationBoxNorm_sqrt_log_primorial_of_eventually_integral_zero
      (N := N) hk hbound hwb e
  filter_upwards [eventually_ge_atTop 2] with R hR
  exact
    integral_cfzCanonicalCarryTruncationDiscrepancy_eq_zero
      (N := N) χ (primorial w) b hR
      (fun q : SelectedCFZFormIndex e => q.1)

end Wikipedia.SzemeredisTheorem
