import ErdosProblems.Erdos6.GenericS2
import BoundedGaps.Maynard.ConcreteS2TauAsymptotics
import BoundedGaps.Maynard.MaynardLambdaSharpBound

/-!
# The large-tuple `S₂` distribution error

The error estimate is dimension-generic.  The dimension occurs only in fixed
logarithmic exponents, so the arbitrary logarithmic saving in the
Bombieri--Vinogradov hypothesis absorbs it.
-/

namespace Erdos6.Maynard

open Filter Set
open scoped BigOperators

noncomputable section

def tupleMaynardSharpCoefficientEnvelope
    (H : Finset ℕ) (alpha B : ℝ) (N : ℕ) : ℝ :=
  B * (1 + Real.log (maynardRadius alpha N)) ^
    (2 * (Fintype.card H) ^ 2)

def tupleMaynardS2TauErrorEnvelope
    (H : Finset ℕ) (alpha B A C : ℝ) (N : ℕ) : ℝ :=
  (tupleMaynardSharpCoefficientEnvelope H alpha B N) ^ 2 *
    ((∑ h : H,
      BoundedGaps.Maynard.tauIndexedEndpointEnvelope H
        (maynardModulus N * maynardRadius alpha N * maynardRadius alpha N)
        C A (2 * N + h.1 - 1)) +
    ∑ h : H,
      BoundedGaps.Maynard.tauIndexedEndpointEnvelope H
        (maynardModulus N * maynardRadius alpha N * maynardRadius alpha N)
        C A (N + h.1 - 1))

theorem eventually_tupleMaynardS2_endpoint_thresholds
    (H : Finset ℕ) (X₀ : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ h : H,
      X₀ ≤ N + h.1 - 1 ∧ X₀ ≤ 2 * N + h.1 - 1 := by
  filter_upwards [eventually_ge_atTop (X₀ + 1)] with N hN h
  omega

theorem eventually_tupleMaynardS2_endpoint_cutoffs
    (H : Finset ℕ) {theta delta : ℝ}
    (htheta : 0 ≤ theta) (hdelta : 0 < delta) :
    ∀ᶠ N : ℕ in atTop, ∀ h : H,
      maynardModulus N * maynardRadius (theta / 2 - delta) N *
          maynardRadius (theta / 2 - delta) N ≤
          BoundedGaps.Maynard.modulusCutoff theta (N + h.1 - 1) ∧
        maynardModulus N * maynardRadius (theta / 2 - delta) N *
            maynardRadius (theta / 2 - delta) N ≤
          BoundedGaps.Maynard.modulusCutoff theta (2 * N + h.1 - 1) := by
  have hbase := BoundedGaps.Maynard.eventually_engelsmaMaynard_modulus_radius_cutoff
    htheta hdelta
  filter_upwards [hbase] with N hN h
  refine ⟨hN h.1, ?_⟩
  have hshift := hN (N + h.1)
  rw [show N + (N + h.1) - 1 = 2 * N + h.1 - 1 by omega] at hshift
  exact hshift

theorem bound_abs_tupleMaynardS2Error_tau
    {theta alpha A C : ℝ} {X₀ : ℕ}
    (hw : BoundedGaps.Maynard.PrimeLevelWitness theta A C X₀)
    (H : Finset ℕ) (hH : H.Nonempty) (v : ℕ → ℕ)
    (F : (H → ℝ) → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hF : ∀ x, |F x| ≤ B)
    (hv : ∀ N h, h ∈ H → Nat.Coprime (v N + h) (maynardModulus N))
    (htheta : theta ≤ 1) (N : ℕ)
    (hcoverage : BoundedGaps.Maynard.CoversShiftDifferencePrimes H
      (maynardModulus N))
    (hN : 0 < N)
    (hupper : ∀ h : H, X₀ ≤ 2 * N + h.1 - 1)
    (hlower : ∀ h : H, X₀ ≤ N + h.1 - 1)
    (hcutUpper : ∀ h : H,
      maynardModulus N * maynardRadius alpha N * maynardRadius alpha N ≤
        BoundedGaps.Maynard.modulusCutoff theta (2 * N + h.1 - 1))
    (hcutLower : ∀ h : H,
      maynardModulus N * maynardRadius alpha N * maynardRadius alpha N ≤
        BoundedGaps.Maynard.modulusCutoff theta (N + h.1 - 1)) :
    |tupleMaynardS2Error H alpha v F N| ≤
      tupleMaynardS2TauErrorEnvelope H alpha B A C N := by
  classical
  let D := tupleMaynardSupport H alpha N
  let lambda := tupleMaynardCoefficient H alpha F N
  let L := tupleMaynardSharpCoefficientEnvelope H alpha B N
  have hW : Squarefree (maynardModulus N) := by
    unfold maynardModulus BoundedGaps.Maynard.engelsmaMaynardModulus
    exact BoundedGaps.Maynard.squarefree_primorial _
  have hD : ∀ d ∈ D, BoundedGaps.Maynard.IsMaynardDivisorTuple H
      (maynardRadius alpha N) (maynardModulus N) d := by
    intro d hd
    exact tupleMaynardS2SupportProof H alpha N d (by simpa [D] using hd)
  have hL : 0 ≤ L := by
    dsimp [L, tupleMaynardSharpCoefficientEnvelope]
    positivity
  have hbound : ∀ d ∈ D, |lambda d| ≤ L := by
    intro d hd
    exact BoundedGaps.Maynard.abs_maynardCoefficient_le_sharp_log
      H (maynardRadius alpha N) (maynardModulus N) F d B hB hF hH
      (by simpa [D, tupleMaynardSupport] using hd)
  have hsizeUpper : ∀ h : H,
      maynardModulus N * maynardRadius alpha N * maynardRadius alpha N ≤
        (2 * N + h.1 - 1) + 1 := by
    intro h
    exact (hcutUpper h).trans
      ((BoundedGaps.Maynard.modulusCutoff_le_self
        (show 1 ≤ 2 * N + h.1 - 1 by omega) htheta).trans (Nat.le_succ _))
  have hsizeLower : ∀ h : H,
      maynardModulus N * maynardRadius alpha N * maynardRadius alpha N ≤
        (N + h.1 - 1) + 1 := by
    intro h
    have hthreshold := hlower h
    have hX₀ := hw.2.1
    exact (hcutLower h).trans
      ((BoundedGaps.Maynard.modulusCutoff_le_self
        (show 1 ≤ N + h.1 - 1 by omega) htheta).trans (Nat.le_succ _))
  have herror := hw.bound_abs_compatiblePairRestrictedErrorOuter_tau
    hH hW hD hcoverage (fun h hh => hv N h hh) lambda L hN hL hbound
      hupper hlower hcutUpper hcutLower hsizeUpper hsizeLower
  simpa [tupleMaynardS2Error, tupleMaynardS2TauErrorEnvelope,
    D, lambda, L] using herror

theorem exists_tupleMaynardS2Error_tau_envelope
    (H : Finset ℕ) (hH : H.Nonempty) (v : ℕ → ℕ)
    (F : (H → ℝ) → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hF : ∀ x, |F x| ≤ B)
    (hv : ∀ N h, h ∈ H → Nat.Coprime (v N + h) (maynardModulus N))
    {theta delta A : ℝ} (htheta : 0 ≤ theta)
    (hthetaHalf : theta < 1 / 2) (hdelta : 0 < delta)
    (hlevel : BoundedGaps.Maynard.hasPrimeLevel theta) (hA : 0 < A) :
    ∃ C : ℝ, ∃ X₀ : ℕ,
      BoundedGaps.Maynard.PrimeLevelWitness theta A C X₀ ∧
      ∀ᶠ N : ℕ in atTop,
        |tupleMaynardS2Error H (theta / 2 - delta) v F N| ≤
          tupleMaynardS2TauErrorEnvelope H (theta / 2 - delta) B A C N := by
  obtain ⟨C, X₀, hw⟩ :=
    BoundedGaps.Maynard.hasPrimeLevel_exists_witness hlevel hA
  refine ⟨C, X₀, hw, ?_⟩
  filter_upwards [eventually_tupleMaynard_coverage H,
    eventually_tupleMaynardS2_endpoint_thresholds H X₀,
    eventually_tupleMaynardS2_endpoint_cutoffs H htheta hdelta,
    eventually_ge_atTop 1] with N hcoverage hthresholds hcutoffs hN
  exact bound_abs_tupleMaynardS2Error_tau hw H hH v F B hB hF hv
    (by linarith) N hcoverage (by omega)
    (fun h => (hthresholds h).2) (fun h => (hthresholds h).1)
    (fun h => (hcutoffs h).2) (fun h => (hcutoffs h).1)

end

end Erdos6.Maynard
