/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1166.Erdos1166HLOZLemma410SourceBands
import ErdosProblems.Erdos1166.Erdos1166HLOZLemma410SourceAbsorption
import ErdosProblems.Erdos1166.Erdos1166HLOZProp47SourceAssembly

namespace Erdos1166.HLOZProp47NamedEstimateBridges

open Filter MeasureTheory Set
open scoped ENNReal

open HLOZPairing.ScreeningBridge HLOZProp47Parameters
open HLOZProp47SourceAssembly
open HLOZLemma410PotentialRace HLOZLemma410SourceBands
open HLOZLemma410SourceAbsorption

/-- A source-strength Lemma 4.10 estimate, stated for the exact exceptional
event consumed by the named Proposition 4.7 assembly.  The harmless shift
`m + 1` makes its comparison with the assembly's inverse-power rate exact. -/
def Prop47Lemma410StretchedExponentialEstimate (c : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ i : Fin 6, ∀ r : StageIndex, ∀ a : AlphaIndex,
    alphaValue a ≤ kappaTwo →
    simpleRandomWalkLaw (lemma410FailureEvent m i r (alphaValue a)) ≤
      ENNReal.ofReal
        (Real.exp (-c * Real.log ((m : ℝ) + 1) ^ 2))

/-- The analogous source-strength estimate for the large-gap exceptional
event.  This is kept separate because its proof uses the creation-time tail,
not the potential-kernel race estimate from Lemma 4.10. -/
def Prop47FarGapStretchedExponentialEstimate (c : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ i : Fin 6, ∀ r : StageIndex,
    simpleRandomWalkLaw (farGapEvent m i r) ≤
      ENNReal.ofReal
        (Real.exp (-c * Real.log ((m : ℝ) + 1) ^ 2))

/-- The exact source inputs left after the deterministic 454-band cover and
the planar post-hit race have been proved.  The only probabilistic premise
is the Proposition‑4.8 candidate-cardinality tail on the stopped source
pairing history; the last inequality packages its finite-band absorption
with the explicit potential-kernel race bound. -/
def Prop47Lemma410SourceBetaBandInputs (c : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ i : Fin 6, ∀ r : StageIndex, ∀ a : AlphaIndex,
    alphaValue a ≤ kappaTwo →
    let alpha := alphaValue a
    let k := stageNumber r
    let window := sourceLemma410Window m alpha
    let P := prefixPairingEvent m i (k + 1)
    2 ≤ m ∧
    2 ≤ sourceLemma410Radius m alpha ∧
    2540 ≤ 2 * Real.log (sourceLemma410Radius m alpha) ∧
    ∃ cap : SourceBetaBandIndex → ℕ,
      ∃ capTail : SourceBetaBandIndex → ℝ≥0∞,
        (∀ j : SourceBetaBandIndex,
          simpleRandomWalkLaw
              (hlozCandidateCapFailureEvent window m k
                (sourceBetaCandidateThreshold m alpha j) (cap j) ∩ P) ≤
            capTail j) ∧
        (∑ j : SourceBetaBandIndex,
            (capTail j + cap j * sourceBetaRaceBound m alpha j)) ≤
          ENNReal.ofReal
            (Real.exp (-c * Real.log ((m : ℝ) + 1) ^ 2))

/-- The exact remaining source input in the Lemma 4.10 branch.  This is the
stopped-history application of HLOZ Proposition 4.8: on the source pairing
history, the `j`th candidate set exceeds
`exp(C m^(β_j-κ₁)) log²(m+1)` only with stretched-log probability.  All
rounding, race, finite-band, and radius estimates are proved independently
of this predicate. -/
def Prop47Lemma410Prop48StoppedCandidateTail (C d : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ i : Fin 6, ∀ r : StageIndex, ∀ a : AlphaIndex,
    alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
    simpleRandomWalkLaw
        (hlozCandidateCapFailureEvent
            (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
            (sourceBetaCandidateThreshold m (alphaValue a) j)
            (sourceBetaCandidateCap C m (alphaValue a) j) ∩
          prefixPairingEvent m i (stageNumber r + 1)) ≤
      sourceBetaCandidateTail d m

/-- The source Proposition 4.8 tail supplies the only non-analytic premise
in `Prop47Lemma410SourceBetaBandInputs`. -/
theorem prop47Lemma410SourceBetaBandInputs_of_prop48StoppedCandidateTail
    {C d : ℝ} (hC : 0 ≤ C) (hd : 0 < d)
    (h : Prop47Lemma410Prop48StoppedCandidateTail C d) :
    Prop47Lemma410SourceBetaBandInputs
      (sourceLemma410AbsorptionConstant d) := by
  filter_upwards [h, eventually_sourceLemma410Radius_bounds,
    eventually_sourceBetaBand_sum_absorption hC hd,
    eventually_ge_atTop 2] with m htail hRadius hsum hm
  intro i r a ha
  refine ⟨hm, (hRadius a ha).1, (hRadius a ha).2,
    (fun j ↦ sourceBetaCandidateCap C m (alphaValue a) j),
    (fun _j ↦ sourceBetaCandidateTail d m), ?_, hsum a ha⟩
  intro j
  exact htail i r a ha j

/-- The 454-band candidate-tail hypotheses, together with the already
checked planar potential-kernel race, imply the exact source-strength
Lemma‑4.10 estimate. -/
theorem prop47Lemma410StretchedExponentialEstimate_of_sourceBetaBands
    {c : ℝ} (h : Prop47Lemma410SourceBetaBandInputs c) :
    Prop47Lemma410StretchedExponentialEstimate c := by
  filter_upwards [h] with m hm
  intro i r a ha
  rcases hm i r a ha with
    ⟨hmlarge, hR, hlarge, cap, capTail, hcap, hsum⟩
  let alpha := alphaValue a
  let k := stageNumber r
  let window := sourceLemma410Window m alpha
  let P := prefixPairingEvent m i (k + 1)
  have hk : 0 < k := by
    dsimp [k, stageNumber]
    omega
  have hcover : lemma410FailureEvent m i r alpha ⊆
      ⋃ j : SourceBetaBandIndex,
        hlozLemma410BPrimeEvent window m k
          (sourceBetaCandidateThreshold m alpha j)
          (sourceBetaRaceCount m alpha j) ∩ P := by
    simpa [alpha, k, window, P] using
      lemma410FailureEvent_subset_sourceBetaBand_cover
        m i r (alphaValue a) hmlarge ha
  have hrace (j : SourceBetaBandIndex) :
      HasHLOZLemma410PostHitRaceEstimate simpleRandomWalkLaw window
        m k (sourceBetaCandidateThreshold m alpha j)
          (sourceBetaRaceCount m alpha j)
          (fun _ ↦ sourceBetaRaceBound m alpha j) := by
    simpa only [sourceBetaRaceBound] using
      planar_hlozLemma410PostHitRaceEstimate_exp
        window m k (sourceBetaCandidateThreshold m alpha j)
          (sourceBetaRaceCount m alpha j)
          (sourceLemma410Radius m alpha) hR hlarge
          (sourceLemma410Window_geometry m alpha)
  exact (measure_le_sum_candidateCapTail_add_race_of_band_cover
    simpleRandomWalkLaw (lemma410FailureEvent m i r alpha) P
    (fun _ ↦ window) m k
    (sourceBetaCandidateThreshold m alpha)
    (sourceBetaRaceCount m alpha) cap
    (sourceBetaRaceBound m alpha) capTail (by omega) hk hcover hrace hcap).trans hsum

private theorem eventually_stretchedExponential_le_sourceExceptional
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ m : ℕ in atTop,
      ENNReal.ofReal
          (Real.exp (-c * Real.log ((m : ℝ) + 1) ^ 2)) ≤
        sourceExceptionalRateWithPrefactor m 1 kappa := by
  have hreal := (tendsto_add_atTop_nat 1).eventually
    (eventually_exponential_error_absorbed (c := c) hc)
  filter_upwards [hreal] with m hm
  have hm' :
      Real.exp (-c * Real.log ((m : ℝ) + 1) ^ 2) ≤
        ((m : ℝ) + 1) ^ (-(3 * kappa)) := by
    simpa [Nat.cast_add, Nat.cast_one] using hm
  rw [sourceExceptionalRateWithPrefactor]
  simp only [Nat.cast_one, one_mul]
  rw [sourceExceptionalRate]
  have hbase : ENNReal.ofReal ((m : ℝ) + 1) = (m : ℝ≥0∞) + 1 := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    simp
  rw [← hbase, ENNReal.ofReal_rpow_of_pos (by positivity)]
  exact ENNReal.ofReal_le_ofReal hm'

/-- A checked bridge from the source's stretched-exponential Lemma 4.10
conclusion to the exact named input of Proposition 4.7. -/
theorem prop47Lemma410Estimate_of_stretchedExponential
    {c : ℝ} (hc : 0 < c)
    (h : Prop47Lemma410StretchedExponentialEstimate c) :
    Prop47Lemma410Estimate 1 := by
  filter_upwards [h, eventually_stretchedExponential_le_sourceExceptional hc]
    with m hm herror
  intro i r a ha
  exact (hm i r a ha).trans herror

/-- Direct connection from the source `β`-band/cardinality inputs and the
unconditional planar potential-kernel race to the exact named
`Prop47Lemma410Estimate` consumed by Proposition 4.7. -/
theorem prop47Lemma410Estimate_of_sourceBetaBands
    {c : ℝ} (hc : 0 < c)
    (h : Prop47Lemma410SourceBetaBandInputs c) :
    Prop47Lemma410Estimate 1 :=
  prop47Lemma410Estimate_of_stretchedExponential hc
    (prop47Lemma410StretchedExponentialEstimate_of_sourceBetaBands h)

/-- Source-faithful closure of the named Lemma 4.10 input: after the
deterministic `B'_j` cover and planar race estimate, only the stopped-history
candidate-cardinality tail from Proposition 4.8 remains. -/
theorem prop47Lemma410Estimate_of_prop48StoppedCandidateTail
    {C d : ℝ} (hC : 0 ≤ C) (hd : 0 < d)
    (h : Prop47Lemma410Prop48StoppedCandidateTail C d) :
    Prop47Lemma410Estimate 1 :=
  prop47Lemma410Estimate_of_sourceBetaBands
    (sourceLemma410AbsorptionConstant_pos hd)
    (prop47Lemma410SourceBetaBandInputs_of_prop48StoppedCandidateTail
      hC hd h)

/-- The corresponding bridge for the named far-gap input. -/
theorem prop47FarGapEstimate_of_stretchedExponential
    {c : ℝ} (hc : 0 < c)
    (h : Prop47FarGapStretchedExponentialEstimate c) :
    Prop47FarGapEstimate 1 := by
  filter_upwards [h, eventually_stretchedExponential_le_sourceExceptional hc]
    with m hm herror
  intro i r
  exact (hm i r).trans herror

end Erdos1166.HLOZProp47NamedEstimateBridges
