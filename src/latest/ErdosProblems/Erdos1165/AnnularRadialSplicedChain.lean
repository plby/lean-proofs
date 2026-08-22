/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRadialChainLower

/-!
# Spatially spliced chronological radial chains

This is the source-correct three-piece event used in HLOZ Appendix A.6:

1. an initial stopped hit of profile boundary `1`;
2. one chronological successive-different-boundary label chain;
3. a fresh final escape event depending on the random level-zero endpoint.

All intermediate spatial endpoints are summed.  Strong Markov gives an exact
kernel factorization, and uniform scalar lower bounds multiply without any
fixed-endpoint Harnack assertion.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.AnnularRadialSplicedChain

open AnnularRadialLabelWord AnnularRadialChainLower
  AnnularOffspringRenewal
  MarkedBoundaryVisitKernel PlanarPotential TerminalExcursionBridge
  TerminalSequentialVisitLaw ThickPoint

noncomputable section

/-- A chronological radial chain followed by an endpoint-dependent fresh
escape event. -/
def radialChainFinalAtom (n : ℕ) (center : Point)
    (final : Point → Set StepPath) :
    Fin (n + 2) → List (Fin (n + 2)) → Point → Set StepPath
  | _, [], start => final start
  | source, target :: tail, start =>
      ⋃ endpoint : RadialBoundaryPoint n center target,
        boundaryExitMarkedSteps (otherRadialBoundaries n center source)
            {endpoint.1} start ∩
          postWithTopStoppingSteps
              (boundaryExitTime (otherRadialBoundaries n center source) start) ⁻¹'
            radialChainFinalAtom n center final target tail endpoint.1

/-- Endpoint-summed kernel of a chronological radial chain with its final
fresh escape factor. -/
def radialChainFinalKernelENNReal (n : ℕ) (center : Point)
    (finalMass : Point → ℝ≥0∞) :
    Fin (n + 2) → List (Fin (n + 2)) → Point → ℝ≥0∞
  | _, [], start => finalMass start
  | source, target :: tail, start =>
      ∑ endpoint : RadialBoundaryPoint n center target,
        skeletonExitKernel (otherRadialBoundaries n center source)
            start endpoint.1 *
          radialChainFinalKernelENNReal n center finalMass
            target tail endpoint.1

private theorem disjoint_boundaryExitMarkedSteps_singletons
    (boundary : Set Point) (start left right : Point) (hne : left ≠ right) :
    Disjoint (boundaryExitMarkedSteps boundary {left} start)
      (boundaryExitMarkedSteps boundary {right} start) := by
  rw [Set.disjoint_left]
  intro omega hleft hright
  apply hne
  simpa only [Set.mem_singleton_iff] using hleft.2.symm.trans hright.2

private theorem fairSteps_boundaryExitMarkedSteps_inter_post
    (boundary mark : Set Point) (start : Point)
    {C : Set StepPath} (hC : MeasurableSet C) :
    fairSteps (boundaryExitMarkedSteps boundary mark start ∩
        postWithTopStoppingSteps (boundaryExitTime boundary start) ⁻¹' C) =
      fairSteps (boundaryExitMarkedSteps boundary mark start) * fairSteps C := by
  have hmarkov := strongMarkov_withTop_fullTail_finiteEvent
    (isStoppingTime_boundaryExitTime boundary start)
    (isMeasurableAtWithTopStopping_boundaryExitMarkedSteps boundary mark start)
    hC
  have hfinite : boundaryExitMarkedSteps boundary mark start ∩
      {omega | boundaryExitTime boundary start omega < ⊤} =
        boundaryExitMarkedSteps boundary mark start := by
    apply Set.Subset.antisymm inter_subset_left
    intro omega homega
    exact ⟨homega, homega.1⟩
  rw [hfinite] at hmarkov
  exact hmarkov

theorem measurableSet_radialChainFinalAtom
    (n : ℕ) (center : Point) {final : Point → Set StepPath}
    (hfinal : ∀ z, MeasurableSet (final z)) :
    ∀ source targets start,
      MeasurableSet (radialChainFinalAtom n center final source targets start) := by
  intro source targets
  induction targets generalizing source with
  | nil =>
      intro start
      exact hfinal start
  | cons target tail ih =>
      intro start
      apply MeasurableSet.iUnion
      intro endpoint
      exact (measurableSet_boundaryExitMarkedSteps _ _ _).inter
        ((ih target endpoint.1).preimage
          (measurable_postWithTopStoppingSteps
            (isStoppingTime_boundaryExitTime
              (otherRadialBoundaries n center source) start)))

/-- Exact finite Strong-Markov factorization including the final escape. -/
theorem fairSteps_radialChainFinalAtom
    (n : ℕ) (center : Point) {final : Point → Set StepPath}
    (hfinal : ∀ z, MeasurableSet (final z)) :
    ∀ source targets start,
      fairSteps (radialChainFinalAtom n center final source targets start) =
        radialChainFinalKernelENNReal n center
          (fun z ↦ fairSteps (final z)) source targets start := by
  intro source targets
  induction targets generalizing source with
  | nil =>
      intro start
      rfl
  | cons target tail ih =>
      intro start
      rw [radialChainFinalAtom, measure_iUnion]
      · rw [radialChainFinalKernelENNReal, tsum_fintype]
        apply Finset.sum_congr rfl
        intro endpoint _
        rw [fairSteps_boundaryExitMarkedSteps_inter_post,
          ih target endpoint.1]
        rfl
        exact measurableSet_radialChainFinalAtom n center hfinal
          target tail endpoint.1
      · intro left right hne
        exact (disjoint_boundaryExitMarkedSteps_singletons
          (otherRadialBoundaries n center source) start left.1 right.1
          (fun heq ↦ hne (Subtype.ext heq))).mono
            inter_subset_left inter_subset_left
      · intro endpoint
        exact (measurableSet_boundaryExitMarkedSteps _ _ _).inter
          ((measurableSet_radialChainFinalAtom n center hfinal
              target tail endpoint.1).preimage
            (measurable_postWithTopStoppingSteps
              (isStoppingTime_boundaryExitTime
                (otherRadialBoundaries n center source) start)))

/-- The scalar row reference and a uniform final factor multiply through
the exact endpoint-summed chain. -/
theorem radialChainReference_mul_final_le_finalKernel
    {n : ℕ} (center : Point)
    (edge : Fin (n + 2) → Fin (n + 2) → ℝ≥0∞)
    (finalLower : ℝ≥0∞)
    (hrow : ∀ source target : Fin (n + 2),
      ∀ start : Point, start ∈ radialBoundary n center source →
        edge source target ≤
          ∑ endpoint : RadialBoundaryPoint n center target,
            skeletonExitKernel (otherRadialBoundaries n center source)
              start endpoint.1)
    (finalMass : Point → ℝ≥0∞)
    (hfinal : ∀ z, z ∈ radialBoundary n center ⟨0, by omega⟩ →
      finalLower ≤ finalMass z) :
    ∀ source targets start,
      start ∈ radialBoundary n center source →
      targets.getLast? = some ⟨0, by omega⟩ →
      radialChainReference edge source targets * finalLower ≤
        radialChainFinalKernelENNReal n center finalMass source targets start := by
  intro source targets
  induction targets generalizing source with
  | nil =>
      intro start _ hlast
      simp at hlast
  | cons target tail ih =>
      intro start hstart hlast
      rw [radialChainReference, radialChainFinalKernelENNReal]
      by_cases htail : tail = []
      · subst tail
        simp only [List.getLast?_singleton, Option.some.injEq] at hlast
        subst target
        have hhead := hrow source ⟨0, by omega⟩ start hstart
        have hhead' : edge source ⟨0, by omega⟩ * 1 ≤
            ∑ endpoint : RadialBoundaryPoint n center ⟨0, by omega⟩,
              skeletonExitKernel (otherRadialBoundaries n center source)
                start endpoint.1 := by
          simpa using hhead
        calc
          edge source ⟨0, by omega⟩ * 1 * finalLower ≤
              (∑ endpoint : RadialBoundaryPoint n center ⟨0, by omega⟩,
                skeletonExitKernel (otherRadialBoundaries n center source)
                  start endpoint.1) * finalLower := by
            exact mul_le_mul hhead' le_rfl bot_le bot_le
          _ = ∑ endpoint : RadialBoundaryPoint n center ⟨0, by omega⟩,
                skeletonExitKernel (otherRadialBoundaries n center source)
                  start endpoint.1 * finalLower := by rw [Finset.sum_mul]
          _ ≤ ∑ endpoint : RadialBoundaryPoint n center ⟨0, by omega⟩,
                skeletonExitKernel (otherRadialBoundaries n center source)
                  start endpoint.1 * finalMass endpoint.1 := by
            exact Finset.sum_le_sum fun endpoint _ ↦
              mul_le_mul le_rfl (hfinal endpoint.1 endpoint.2) bot_le bot_le
      · have htailLast : tail.getLast? = some ⟨0, by omega⟩ := by
          cases tail with
          | nil => simp at htail
          | cons next rest =>
              simpa only [List.getLast?_cons_cons] using hlast
        have hhead := hrow source target start hstart
        have htailBound (endpoint : RadialBoundaryPoint n center target) :=
          ih target endpoint.1 endpoint.2 htailLast
        calc
          edge source target * radialChainReference edge target tail * finalLower =
              edge source target *
                (radialChainReference edge target tail * finalLower) := by ring
          _ ≤ (∑ endpoint : RadialBoundaryPoint n center target,
                skeletonExitKernel (otherRadialBoundaries n center source)
                  start endpoint.1) *
              (radialChainReference edge target tail * finalLower) := by
            exact mul_le_mul hhead le_rfl bot_le bot_le
          _ = ∑ endpoint : RadialBoundaryPoint n center target,
                skeletonExitKernel (otherRadialBoundaries n center source)
                  start endpoint.1 *
                (radialChainReference edge target tail * finalLower) := by
            rw [Finset.sum_mul]
          _ ≤ ∑ endpoint : RadialBoundaryPoint n center target,
                skeletonExitKernel (otherRadialBoundaries n center source)
                  start endpoint.1 *
                radialChainFinalKernelENNReal n center finalMass
                  target tail endpoint.1 := by
            exact Finset.sum_le_sum fun endpoint _ ↦
              mul_le_mul le_rfl (htailBound endpoint) bot_le bot_le

/-- Add the initial stopped hit and pass its random endpoint to the radial
chain. -/
def spatiallySplicedRadialChainAtom
    (n : ℕ) (center initialStart : Point) (initialBoundary : Set Point)
    (source : Fin (n + 2)) (targets : List (Fin (n + 2)))
    (final : Point → Set StepPath) : Set StepPath :=
  ⋃ endpoint : RadialBoundaryPoint n center source,
    boundaryExitMarkedSteps initialBoundary {endpoint.1} initialStart ∩
      postWithTopStoppingSteps
          (boundaryExitTime initialBoundary initialStart) ⁻¹'
        radialChainFinalAtom n center final source targets endpoint.1

/-- Exact mass factorization of the complete initial/radial/final splice. -/
theorem fairSteps_spatiallySplicedRadialChainAtom
    (n : ℕ) (center initialStart : Point) (initialBoundary : Set Point)
    (source : Fin (n + 2)) (targets : List (Fin (n + 2)))
    {final : Point → Set StepPath} (hfinal : ∀ z, MeasurableSet (final z)) :
    fairSteps (spatiallySplicedRadialChainAtom n center initialStart
        initialBoundary source targets final) =
      ∑ endpoint : RadialBoundaryPoint n center source,
        skeletonExitKernel initialBoundary initialStart endpoint.1 *
          radialChainFinalKernelENNReal n center
            (fun z ↦ fairSteps (final z)) source targets endpoint.1 := by
  rw [spatiallySplicedRadialChainAtom, measure_iUnion]
  · rw [tsum_fintype]
    apply Finset.sum_congr rfl
    intro endpoint _
    rw [fairSteps_boundaryExitMarkedSteps_inter_post,
      fairSteps_radialChainFinalAtom n center hfinal]
    rfl
    exact measurableSet_radialChainFinalAtom n center hfinal
      source targets endpoint.1
  · intro left right hne
    exact (disjoint_boundaryExitMarkedSteps_singletons
      initialBoundary initialStart left.1 right.1
      (fun heq ↦ hne (Subtype.ext heq))).mono
        inter_subset_left inter_subset_left
  · intro endpoint
    exact (measurableSet_boundaryExitMarkedSteps _ _ _).inter
      ((measurableSet_radialChainFinalAtom n center hfinal
          source targets endpoint.1).preimage
        (measurable_postWithTopStoppingSteps
          (isStoppingTime_boundaryExitTime initialBoundary initialStart)))

/-- Fully scalar lower bound for the three-piece stopped splice. -/
theorem initial_mul_reference_mul_final_le_splicedMass
    {n : ℕ} (center initialStart : Point) (initialBoundary : Set Point)
    (source : Fin (n + 2)) (targets : List (Fin (n + 2)))
    {final : Point → Set StepPath} (hfinalMeas : ∀ z, MeasurableSet (final z))
    (edge : Fin (n + 2) → Fin (n + 2) → ℝ≥0∞)
    (initialLower finalLower : ℝ≥0∞)
    (hinitial : initialLower ≤
      ∑ endpoint : RadialBoundaryPoint n center source,
        skeletonExitKernel initialBoundary initialStart endpoint.1)
    (hrow : ∀ left right : Fin (n + 2),
      ∀ start : Point, start ∈ radialBoundary n center left →
        edge left right ≤
          ∑ endpoint : RadialBoundaryPoint n center right,
            skeletonExitKernel (otherRadialBoundaries n center left)
              start endpoint.1)
    (hfinal : ∀ z, z ∈ radialBoundary n center ⟨0, by omega⟩ →
      finalLower ≤ fairSteps (final z))
    (hlast : targets.getLast? = some ⟨0, by omega⟩) :
    initialLower * radialChainReference edge source targets * finalLower ≤
      fairSteps (spatiallySplicedRadialChainAtom n center initialStart
        initialBoundary source targets final) := by
  rw [fairSteps_spatiallySplicedRadialChainAtom n center initialStart
    initialBoundary source targets hfinalMeas]
  have hchain (endpoint : RadialBoundaryPoint n center source) :=
    radialChainReference_mul_final_le_finalKernel center edge finalLower hrow
      (fun z ↦ fairSteps (final z)) hfinal source targets endpoint.1
        endpoint.2 hlast
  calc
    initialLower * radialChainReference edge source targets * finalLower =
        initialLower * (radialChainReference edge source targets * finalLower) := by
      ring
    _ ≤ (∑ endpoint : RadialBoundaryPoint n center source,
          skeletonExitKernel initialBoundary initialStart endpoint.1) *
        (radialChainReference edge source targets * finalLower) := by
      exact mul_le_mul hinitial le_rfl bot_le bot_le
    _ = ∑ endpoint : RadialBoundaryPoint n center source,
          skeletonExitKernel initialBoundary initialStart endpoint.1 *
            (radialChainReference edge source targets * finalLower) := by
      rw [Finset.sum_mul]
    _ ≤ ∑ endpoint : RadialBoundaryPoint n center source,
          skeletonExitKernel initialBoundary initialStart endpoint.1 *
            radialChainFinalKernelENNReal n center
              (fun z ↦ fairSteps (final z)) source targets endpoint.1 := by
      exact Finset.sum_le_sum fun endpoint _ ↦
        mul_le_mul le_rfl (hchain endpoint) bot_le bot_le

end

end Erdos1165.AnnularRadialSplicedChain
