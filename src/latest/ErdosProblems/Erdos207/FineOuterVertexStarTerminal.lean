/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FineOuterVertexStarRate
import ErdosProblems.Erdos207.OuterOnlyVertexStarTerminal

/-!
# Canonical outer residual-degree tail

This is the canonical-schedule wrapper around the fixed-vertex martingale
bound.  The logarithmic eligible-pair clock supplies the cumulative drift;
the remaining assumptions are scalar terminal-threshold inequalities.
-/

namespace Erdos207

open Finset

noncomputable section

theorem fineOuterCanonical_probability_exists_residualDegree_ge_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (lower₀ outside t Kinc K Kpair Kglobal : ℕ)
    (hc : FineOuterCanonicalCertificates H X lower₀ outside t
      Kinc K Kpair Kglobal)
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V)
    (U : Finset V) (A : TripleSystemOn V) (S₀ : GreedyStateOn V)
    (Delta delta I Dcut R starCap : ℕ) (theta a epsilon : ℝ)
    (hAbs₀ : AbsorberGreedyInvariant F (outerOnlyAvailable U A) S₀)
    (houtside₀ : OutsideLeavePairsAlive (internalOuterGraph G U)ᶜ U S₀)
    (htri : ConsistsOfTriangles G A)
    (hchosen₀ : S₀.chosen = ∅)
    (hRpos : 0 < R)
    (hsmall : ∀ i,
      i < outerSharpStopFuel H X (fineOuterReserve outside t) →
      3 + Kpair < outerSharpLowerSchedule H X
        (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) Kinc i)
    (hrateOne : ∀ i,
      i < outerSharpStopFuel H X (fineOuterReserve outside t) →
      R * outerSharpLowerSchedule H X
          (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) Kinc i ≤
        2 * outerSharpUpperAvailability H X
          (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) Kinc i)
    (hstarCap : (univ \ U).card - 1 ≤ R + 2 * starCap)
    (hlogBudget : a + starCap ≤ (R : ℝ) / 12 *
      (Real.log (outerSharpEligiblePairs H X 0) -
        Real.log (outerSharpEligiblePairs H X
          (outerSharpStopFuel H X (fineOuterReserve outside t)))))
    (htheta : 0 < theta) (hthetaOne : theta ≤ 1)
    (hinactive :
      let fuel := outerSharpStopFuel H X (fineOuterReserve outside t)
      let D := outerSharpLowerAvailability H X
        (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) Kinc
      let d := outerSharpLowerSchedule H X
        (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) Kinc
      let M := outerSharpUpperAvailability H X
        (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) Kinc
      let u := outerSharpUpperSchedule H X
        (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) Kinc
      let active := timedSharpScheduledAggregatePairBandActive F Kpair
        Kglobal Kinc Delta delta I Dcut D d M u
      let L := FiniteLaw.timedStoppedProcessLaw fuel
        (fun _ ↦ greedyKernel F) active S₀
      ((L.probability (fun z ↦ ¬ active z.1.1 z.2) : ℝ)) ≤ epsilon) :
    let fuel := outerSharpStopFuel H X (fineOuterReserve outside t)
    let D := outerSharpLowerAvailability H X
      (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) Kinc
    let d := outerSharpLowerSchedule H X
      (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) Kinc
    let M := outerSharpUpperAvailability H X
      (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) Kinc
    let u := outerSharpUpperSchedule H X
      (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) Kinc
    let active := timedSharpScheduledAggregatePairBandActive F Kpair
      Kglobal Kinc Delta delta I Dcut D d M u
    let L := FiniteLaw.timedStoppedProcessLaw fuel
      (fun _ ↦ greedyKernel F) active S₀
    ((L.probability (fun z ↦ ∃ v : V,
      R ≤ (scheduledEdgesAt
        (preliminaryResidualInternalEdges G U z.2.chosen) v).card) : ℝ)) ≤
      epsilon + (Fintype.card V : ℝ) *
        Real.exp (-theta * a + theta ^ 2 * (fuel : ℝ)) := by
  dsimp only at hinactive ⊢
  let fuel := outerSharpStopFuel H X (fineOuterReserve outside t)
  let D := outerSharpLowerAvailability H X
    (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) Kinc
  let d := outerSharpLowerSchedule H X
    (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) Kinc
  let M := outerSharpUpperAvailability H X
    (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) Kinc
  let u := outerSharpUpperSchedule H X
    (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) Kinc
  let active := timedSharpScheduledAggregatePairBandActive F Kpair
    Kglobal Kinc Delta delta I Dcut D d M u
  have hcumulative : a + starCap ≤ cumulativeGreedyRate
      (outerOnlyVertexSelectionRate R d M) fuel := by
    apply hlogBudget.trans
    simpa only [fuel, d, M, fineOuterCanonicalVertexRate] using
      fineOuterCanonicalVertexRate_log_lower H X lower₀ outside t Kinc K
        Kpair Kglobal R hc
  apply probability_timedStoppedGreedy_exists_residualDegree_ge_le
    fuel F G U A active S₀ Kpair R starCap d M theta a epsilon
    hAbs₀ houtside₀ htri hchosen₀ hRpos
  · intro i hi S _hAbs _hout hactive
    exact hactive.1.1.1.1.1.1
  · intro i hi S _hAbs _hout hactive
    exact hactive.1.1.1.1.1.2.2.1
  · intro i hi S _hAbs _hout hactive
    exact hactive.1.1.2.2
  · intro i hi
    simpa only [fuel, M] using hc.process.upper_availability_pos i hi
  · intro i hi S _hAbs _hout hactive
    exact hactive.1.2
  · intro i hi
    simpa only [fuel, d] using hsmall i hi
  · intro i hi
    simpa only [fuel, d, M] using hrateOne i hi
  · exact hstarCap
  · exact hcumulative
  · exact htheta
  · exact hthetaOne
  · simpa only [fuel, D, d, M, u, active] using hinactive

end

end Erdos207
