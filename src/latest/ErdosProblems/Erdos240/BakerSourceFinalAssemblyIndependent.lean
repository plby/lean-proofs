/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerSourceAnalyticDataFactoryIndependent
import ErdosProblems.Erdos240.BakerSourceUniformConstantCompletion
import ErdosProblems.Erdos240.BakerSourceInnerZeroIndependent
import ErdosProblems.Erdos240.BakerSourceAlgebraicIntegralGridGrowth
import ErdosProblems.Erdos240.BakerSourcePositiveStageGrowth
import ErdosProblems.Erdos240.BakerSourceInnerZeroHonest
import ErdosProblems.Erdos240.BakerSourceRationalAnalyticEndpoints
import ErdosProblems.Erdos240.BakerSourceCoprimeCompletion

/-!
# Final source assembly for Erdős 240

This module is the cycle-free endpoint for the concrete source argument.
The analytic `Fin`-indexed construction is assembled here and then passed
to `uniformBounds_of_finAnalyticData`.
-/

noncomputable section

namespace Erdos240.BakerSourceFinalAssemblyIndependent

universe u

open Erdos240
open Erdos240.BakerInduction
open Erdos240.BakerSourceAnalyticDataFactoryIndependent
open Erdos240.BakerSourceAssemblyIndependent
open Erdos240.BakerSourceAlgebraicIntegralGridGrowth
open Erdos240.BakerSourceConcreteConstructionIndependent
open Erdos240.BakerSourceCoprimeCompletion
open Erdos240.BakerSourceInnerZeroIndependent
open Erdos240.BakerSourceInnerZeroHonest
open Erdos240.BakerSourceLogFormNormalization
open Erdos240.BakerSourceNumericalAssemblyIndependent
open Erdos240.BakerSourcePositiveStageGrowth
open Erdos240.BakerSourceRationalAnalyticEndpoints
open Erdos240.BakerSourceRationalAlternativeIndependent
open Erdos240.BakerSourceState
open Erdos240.BakerSourceUniformConstantCompletion

/-- Every canonical source parameter contains the `10/epsilon` source
requirement used by the positive Lemma-4 contour estimate. -/
theorem sourceTenThreshold_mem_sourceParameters
    {oldRank : ℕ} (old : Fin oldRank → ℕ)
    (oldPrime : ∀ i, (old i).Prime)
    (oldInjective : Function.Injective old)
    (newPrime : ℕ) (newPrimePrime : newPrime.Prime)
    (newFresh : ∀ i, old i ≠ newPrime)
    (N : ℕ) (Nlarge : Real.exp 2 ≤ (N : ℝ)) :
    let P := sourceParameters old oldPrime oldInjective newPrime
      newPrimePrime newFresh N Nlarge
    P.sourceTenThreshold ∈ P.kRequirements := by
  dsimp only
  unfold sourceParameters
  apply VDPLParameters.sourceTenThreshold_mem_withSourceRequirements

/-- The source cutoff stored in the canonical parameter is definitionally
the coefficient cutoff supplied to `sourceParameters`. -/
theorem sourceParameters_Bsrc_eq
    {oldRank : ℕ} (old : Fin oldRank → ℕ)
    (oldPrime : ∀ i, (old i).Prime)
    (oldInjective : Function.Injective old)
    (newPrime : ℕ) (newPrimePrime : newPrime.Prime)
    (newFresh : ∀ i, old i ≠ newPrime)
    (N : ℕ) (Nlarge : Real.exp 2 ≤ (N : ℝ)) :
    (sourceParameters old oldPrime oldInjective newPrime newPrimePrime
      newFresh N Nlarge).Bsrc = N := rfl

/-- Choose the normalized source constant once for a fixed old-prime family.
Besides the complete fixed-family numerical ledger, every specialization
also carries the canonical `10 / epsilon` source requirement used by the
positive Lemma-4 stages and the exact radical-degree-scale requirement used
by source Lemma 5.  Thus the final analytic construction need not re-open
the definition of `sourceParameters` at each varying prime. -/
theorem exists_uniform_completeSourceConstant_and_requirement
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (old : Fin oldRank → ℕ) (oldPrime : ∀ i, (old i).Prime)
    (oldInjective : Function.Injective old) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (newPrime : ℕ) (newPrimePrime : newPrime.Prime)
        (newFresh : ∀ i, old i ≠ newPrime)
        (N : ℕ) (Nlarge : Real.exp 2 ≤ (N : ℝ)),
        let P := sourceParameters old oldPrime oldInjective newPrime
          newPrimePrime newFresh N Nlarge
        HasFixedSourceConstantBounds P C₀ ∧
          P.sourceTenThreshold ∈ P.kRequirements ∧
          2 * (6 + 34 * (13 ^ (oldRank + 1) : ℝ)) * P.k ≤ C₀ := by
  classical
  let oldMax : ℕ := Finset.univ.sup old
  obtain ⟨referencePrime, hreferencePrime, referencePrimePrime⟩ :=
    Nat.exists_infinite_primes (oldMax + 1)
  have referenceFresh : ∀ i, old i ≠ referencePrime := by
    intro i
    have hi : old i ≤ oldMax :=
      Finset.le_sup (f := old) (Finset.mem_univ i)
    exact ne_of_lt (show old i < referencePrime by omega)
  let referenceBound : ℕ := ⌈Real.exp 2⌉₊
  have referenceBoundLarge : Real.exp 2 ≤ (referenceBound : ℝ) :=
    Nat.le_ceil (Real.exp 2)
  let Pref := sourceParameters old oldPrime oldInjective referencePrime
    referencePrimePrime referenceFresh referenceBound referenceBoundLarge
  let A : ℝ :=
    2 * (6 + 34 * (13 ^ (oldRank + 1) : ℝ)) * Pref.k
  obtain ⟨C₀, hC₀, hA, hfixed⟩ :=
    exists_uniform_completeSourceConstant_ge old oldPrime oldInjective A
  refine ⟨C₀, hC₀, ?_⟩
  intro newPrime newPrimePrime newFresh N Nlarge
  let P := sourceParameters old oldPrime oldInjective newPrime newPrimePrime
    newFresh N Nlarge
  have hk : P.k = Pref.k :=
    sourceParameters_k_eq old oldPrime oldInjective newPrime newPrimePrime
      newFresh N Nlarge old oldPrime oldInjective referencePrime
        referencePrimePrime referenceFresh referenceBound referenceBoundLarge
  refine ⟨hfixed newPrime newPrimePrime newFresh N Nlarge,
    sourceTenThreshold_mem_sourceParameters old oldPrime oldInjective
      newPrime newPrimePrime newFresh N Nlarge, ?_⟩
  simpa only [P, hk, A] using hA

/-! ## Concrete Lemma 4 input -/

/-- The exact Lemma-4 inner iteration input obtained from the sharp
level-scaled source majorants.  All pointwise analytic obligations are
discharged here; in particular the exceptional first contour and the
positive-stage contours use their distinct source bounds. -/
theorem integralStepInputs_of_sourceBounds
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (hunknown : Erdos240.BakerLemma2Concrete.initialUnknownRequirement P ∈
      P.kRequirements)
    (hsourceTen : P.sourceTenThreshold ∈ P.kRequirements)
    (state : LevelState P N) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hb : ∀ r, (b r).natAbs ≤ P.Bsrc)
    (hbLastBound : bLast.natAbs ≤ P.Bsrc) (hbLast : bLast ≠ 0)
    (hN : P.LevelOK N) {C₀ : ℝ}
    (hfixed : HasFixedSourceConstantBounds P C₀)
    (hsmall :
      |RationalPrimeBaker.indexedRationalLogForm
          P.old P.newPrime b bLast| <
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ)))) :
    IntegralStepInputs P state b bLast := by
  let outer : ℕ → VDPLMultiIndex P.rank → ℝ := fun t _m ↦
    Real.exp
      ((2 * (P.h : ℝ) * P.k + 24 * (P.h : ℝ) *
        P.k ^ (1 - P.sigma +
          P.epsilon * ((t + 1 : ℕ) : ℝ))) *
        (P.Omega * Real.log P.OmegaOld))
  have hform := norm_logForm_le_smallLinearFormBound_of_normalized
    P C₀ b bLast hsmall
  constructor
  apply innerStepCallback_of_honestAlgebraicGrowthBounds
    state b hbLast hN C₀ hsmall hfixed.2.1 hfixed.2.2.1
      hsourceTen outer
  · intro t m
    dsimp only [outer]
    exact (Real.exp_pos _).le
  · intro t ht i m' hm'
    have hl : i.1 + 1 ≤ P.lemmaFourRadius N (t + 1) := by
      exact (Nat.succ_le_iff.mpr i.2).trans
        (Erdos240.BakerSourceInnerStepAssemblyIndependent.lemmaFourRadius_mono
          P N (Nat.le_succ t))
    exact levelAlgebraicSourceRowError_integralNode_le_three_quarters
      P hunknown state b hb hbLastBound hbLast ht hl m' hm'
        hfixed.1 hfixed.2.2.2.2.2
  · intro t ht m hm z hz
    have hamp :=
      scaledAmplificationClosedForm_le_integralDisk_structural_quarter
        P hunknown N ht z (by rw [hz])
    have hpos := norm_f_le_positiveContour P hunknown state b hb
      hbLastBound hbLast t z hz m hm hfixed.1 hfixed.2.2.2.2.2 hamp hform
    rw [show outer t m = Real.exp
        ((2 * (P.h : ℝ) * P.k + 24 * (P.h : ℝ) *
          P.k ^ (1 - P.sigma +
            P.epsilon * ((t + 1 : ℕ) : ℝ))) *
          (P.Omega * Real.log P.OmegaOld)) by rfl]
    convert hpos using 1 <;>
      simp only [sourceHeightUnit, positiveStageHeightUnit] <;> ring
  · intro m hm
    norm_num [outer]
  · intro t htpos ht m hm
    exact le_rfl
  · intro t ht l _hnew hl m hm
    have hmSource :
        VDPLMultiIndex.weight (toSourceMultiIndex P m) ≤ P.Slevel N := by
      rw [weight_toSourceMultiIndex]
      exact hm.trans (P.lemmaFourBudget_le_Slevel N (t + 1))
    exact levelAlgebraicSourceRowError_integralTarget_le_threshold
      P hunknown hN state b hb hbLastBound hbLast ht hl
        (toSourceMultiIndex P m) hmSource hfixed.1 hfixed.2.2.2.2.2
          hfixed.2.2.2.1

/-! ## Concrete rational Lemma 3 and Lemma 5 inputs -/

/-- The direct rational Liouville alternative and the terminal rational
interpolation upper estimate, packaged with their definitionally identical
literal threshold.  All analytic estimates are discharged from the source
coefficient bounds and the fixed-family numerical ledger. -/
theorem rationalInputs_of_sourceBounds
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (hunknown : Erdos240.BakerLemma2Concrete.initialUnknownRequirement P ∈
      P.kRequirements)
    (state : LevelState P N) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hb : ∀ r, (b r).natAbs ≤ P.Bsrc)
    (hbLastBound : bLast.natAbs ≤ P.Bsrc) (hbLast : bLast ≠ 0)
    (hN : P.LevelOK N) {C₀ : ℝ}
    (hfixed : HasFixedSourceConstantBounds P C₀)
    (hsmall :
      |RationalPrimeBaker.indexedRationalLogForm
          P.old P.newPrime b bLast| <
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ)))) :
    AlgebraicRationalLowerInputs P state b bLast ∧
      (IntegralExtrapolatedAtLevel P (g state b bLast) N →
        RationalInterpolationUpperAtLevel P (f state b bLast)
          (BakerSourceRationalAlternativeIndependent.lower
            P state b bLast) N) := by
  refine ⟨algebraicRationalLowerInputs_of_sourceBounds P hunknown state b hb
      hbLastBound hbLast hN hfixed hsmall, ?_⟩
  intro hint
  change RationalInterpolationUpperAtLevel P (f state b bLast)
    (fun l m ↦ Erdos240.BakerLemma3Instantiation.stateRationalLiouvilleThreshold
      P N state b bLast l (toSourceMultiIndex P m)) N
  exact rationalInterpolationUpperAtLevel_of_sourceBounds P hunknown state b
    hb hbLastBound hbLast hN hint hfixed hsmall

/-! ## Unconditional fixed-family assembly -/

/-- The complete source analytic construction for every canonical finite
old-prime family.  The normalized constant is selected once for the fixed
family and is independent of the varying prime, the coefficient vector,
and the cutoff. -/
theorem hasNormalizedFinAnalyticSourceData :
    HasNormalizedFinAnalyticSourceData := by
  intro oldRank _ old oldPrime oldInjective
  obtain ⟨C₀, hC₀, huniform⟩ :=
    exists_uniform_completeSourceConstant_and_requirement
      old oldPrime oldInjective
  refine ⟨C₀, hC₀, ?_⟩
  intro p c d N hp hpFresh hN hc hd hdne _hform
  dsimp only
  intro hsmall
  let P := sourceParameters old oldPrime oldInjective p hp hpFresh N hN
  have hcP : ∀ i, (c i).natAbs ≤ P.Bsrc := by
    simpa only [P, sourceParameters_Bsrc_eq] using hc
  have hdP : d.natAbs ≤ P.Bsrc := by
    simpa only [P, sourceParameters_Bsrc_eq] using hd
  have hunknown :
      Erdos240.BakerLemma2Concrete.initialUnknownRequirement P ∈
        P.kRequirements := by
    exact initialUnknownRequirement_mem_sourceParameters old oldPrime
      oldInjective p hp hpFresh N hN
  obtain ⟨hfixed, hsourceTen, _hrationalFixed⟩ :=
    huniform p hp hpFresh N hN
  refine ⟨ofFields hdne ?_ ?_ ?_ ?_⟩
  · intro J state hJ
    exact integralStepInputs_of_sourceBounds hunknown hsourceTen state c hcP
      hdP hdne hJ hfixed hsmall
  · intro J state hJ
    exact (rationalInputs_of_sourceBounds hunknown state c hcP hdP hdne hJ
      hfixed hsmall).1
  · intro J state hJ hint
    exact (rationalInputs_of_sourceBounds hunknown state c hcP hdP hdne hJ
      hfixed hsmall).2 hint
  · intro J state hJ
    exact coprimeCompletionAtLevel_of_sourceBounds P hunknown state c hcP
      hdP hdne hJ hfixed hsmall

/-- Universe-polymorphic project-facing source component interface. -/
theorem hasNormalizedConcreteSourceComponents :
    HasNormalizedConcreteSourceComponents.{u} :=
  normalizedConcreteSourceComponents_of_finAnalyticData
    hasNormalizedFinAnalyticSourceData

/-- The source construction yields the uniform rational-prime logarithmic
form lower bound used by the resolution of Erdős 240. -/
theorem uniform_rational_prime_log_lower_bound :
    RationalPrimeBaker.HasUniformRationalPrimeLogBounds.{u} :=
  uniformBounds_of_finAnalyticData hasNormalizedFinAnalyticSourceData

end Erdos240.BakerSourceFinalAssemblyIndependent

#print axioms Erdos240.BakerSourceFinalAssemblyIndependent.sourceTenThreshold_mem_sourceParameters
#print axioms Erdos240.BakerSourceFinalAssemblyIndependent.exists_uniform_completeSourceConstant_and_requirement
#print axioms Erdos240.BakerSourceFinalAssemblyIndependent.integralStepInputs_of_sourceBounds
#print axioms Erdos240.BakerSourceFinalAssemblyIndependent.rationalInputs_of_sourceBounds
#print axioms Erdos240.BakerSourceFinalAssemblyIndependent.hasNormalizedFinAnalyticSourceData
#print axioms Erdos240.BakerSourceFinalAssemblyIndependent.hasNormalizedConcreteSourceComponents
#print axioms Erdos240.BakerSourceFinalAssemblyIndependent.uniform_rational_prime_log_lower_bound
