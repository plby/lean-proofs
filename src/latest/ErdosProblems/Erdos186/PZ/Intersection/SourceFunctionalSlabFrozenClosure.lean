/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.SourceFunctionalSlabFrozenBoxScale
import ErdosProblems.Erdos186.PZ.Intersection.SourceFunctionalSlabFrozenLowRank

namespace Erdos186.PZ.Intersection

open Filter
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- Exact source slab hierarchy with all analytic parameters frozen at the
initial population and uniformly valid above any fixed positive power of
that population. -/
theorem eventually_sourceFunctionalSlabPowerRangeScalarHierarchies
    {beta eta : ℝ}
    (context : Reduction.HigherDimensionalContext beta eta)
    (rankCeiling : ℕ) (heta : 0 < eta)
    (p : ℝ) (hp : 0 < p)
    (kappa K : ℝ) (hK : 0 < K)
    (forwardConstant reverseConstant : ℝ)
    (hforward : 0 ≤ forwardConstant) (hreverse : 0 ≤ reverseConstant) :
    ∀ᶠ initialCard : ℕ in atTop,
      ∀ {ambient : ℕ} (selector : Reduction.BoundedCFPSelector context)
        (A : Finset (LatticePoint ambient)) (hA : selector.Eligible A),
        Real.rpow (initialCard : ℝ) p ≤ (A.card : ℝ) →
        (selector.chosen A hA).dimension ≤ rankCeiling →
        0 < (selector.chosen A hA).dimension →
        (1 / 2 : ℝ) * (A.card : ℝ) ≤
          ((selector.chosen A hA).identifiedCore.card : ℝ) →
        let slab := sourceFunctionalSlabBudget
          (delta kappa initialCard) A.card
        let t := sourceFunctionalSlabThickness context rankCeiling
          forwardConstant reverseConstant (gamma kappa K initialCard)
        SourceFunctionalSlabScalarHierarchy selector A hA
            (delta kappa initialCard) (gamma kappa K initialCard)
            forwardConstant slab t ∧
          SourceFunctionalSlabScalarHierarchy selector A hA
            (delta kappa initialCard) (gamma kappa K initialCard)
            reverseConstant slab t := by
  have hbox := eventually_sourceFunctionalSlab_powerRange_boxScale
    context rankCeiling p hp kappa K hK forwardConstant reverseConstant
      hforward hreverse
  have hlow := eventually_sourceFunctionalSlab_powerRange_lowRank
    context rankCeiling heta p hp kappa K hK
      forwardConstant reverseConstant hforward hreverse
  filter_upwards [hbox, hlow, eventually_delta_pos kappa,
      eventually_gamma_pos kappa hK]
    with initialCard hboxN hlowN hdeltaN hgammaN
  intro ambient selector A hA hlower hrank hd hhalf
  let slab := sourceFunctionalSlabBudget
    (delta kappa initialCard) A.card
  let t := sourceFunctionalSlabThickness context rankCeiling
    forwardConstant reverseConstant (gamma kappa K initialCard)
  have ht : 0 < t := by
    dsimp only [t]
    exact sourceFunctionalSlabThickness_pos hforward hreverse hgammaN
  have hdensity : delta kappa initialCard * (A.card : ℝ) ≤
      (slab : ℝ) := by
    dsimp only [slab]
    exact sourceFunctionalSlabBudget_density _ _
  have hboxScale :
      1 ≤ (2 * ((selector.chosen A hA).dimension : ℝ) * t) *
        ((controlIntegerBox (selector.chosen A hA).progression
          (2 * context.scaleDen
            (selector.chosen A hA).dimension)).carrier.card : ℝ) := by
    simpa only [t] using hboxN selector A hA hlower hd hhalf
  have hlowForward :
      ∀ (Z : Finset (LatticePoint (selector.chosen A hA).dimension))
        (hZ : selector.Eligible Z),
        delta kappa initialCard * (A.card : ℝ) ≤ (Z.card : ℝ) →
        sourceFunctionalSlabFixedTerm context forwardConstant
            (selector.chosen A hA).dimension <
          ((selector.chosen Z hZ).dilation : ℝ) *
            gamma kappa K initialCard := by
    intro Z hZ hdense
    exact (hlowN A.card hlower (selector.input Z hZ) hrank hdense).1
  have hlowReverse :
      ∀ (Z : Finset (LatticePoint (selector.chosen A hA).dimension))
        (hZ : selector.Eligible Z),
        delta kappa initialCard * (A.card : ℝ) ≤ (Z.card : ℝ) →
        sourceFunctionalSlabFixedTerm context reverseConstant
            (selector.chosen A hA).dimension <
          ((selector.chosen Z hZ).dilation : ℝ) *
            gamma kappa K initialCard := by
    intro Z hZ hdense
    exact (hlowN A.card hlower (selector.input Z hZ) hrank hdense).2
  have hfullForward :
      sourceFunctionalSlabFullTerm context forwardConstant
          (selector.chosen A hA).dimension * t <
        gamma kappa K initialCard := by
    dsimp only [t]
    exact sourceFunctionalSlabFullTerm_mul_thickness_lt
      hforward hreverse hgammaN hrank
  have hfullReverse :
      sourceFunctionalSlabFullTerm context reverseConstant
          (selector.chosen A hA).dimension * t <
        gamma kappa K initialCard := by
    dsimp only [t]
    exact sourceFunctionalSlabReverseFullTerm_mul_thickness_lt
      hforward hreverse hgammaN hrank
  dsimp only
  constructor
  · refine {
      t_pos := ht
      density := hdensity
      box_scale := hboxScale
      low_rank := ?_
      full_rank := ?_ }
    · intro Z hZ hdense
      simpa only [sourceFunctionalSlabFixedTerm] using
        hlowForward Z hZ hdense
    · rw [sourceFunctionalSlabFullExpression_eq]
      exact hfullForward
  · refine {
      t_pos := ht
      density := hdensity
      box_scale := hboxScale
      low_rank := ?_
      full_rank := ?_ }
    · intro Z hZ hdense
      simpa only [sourceFunctionalSlabFixedTerm] using
        hlowReverse Z hZ hdense
    · rw [sourceFunctionalSlabFullExpression_eq]
      exact hfullReverse

/-- Population-threshold form of the frozen arbitrary power-range hierarchy. -/
theorem exists_sourceFunctionalSlabPowerRangeScalarHierarchyThreshold
    {beta eta : ℝ}
    (context : Reduction.HigherDimensionalContext beta eta)
    (rankCeiling : ℕ) (heta : 0 < eta)
    (p : ℝ) (hp : 0 < p)
    (kappa K : ℝ) (hK : 0 < K)
    (forwardConstant reverseConstant : ℝ)
    (hforward : 0 ≤ forwardConstant) (hreverse : 0 ≤ reverseConstant) :
    ∃ threshold : ℕ, ∀ {initialCard ambient : ℕ},
      threshold ≤ initialCard →
      ∀ (selector : Reduction.BoundedCFPSelector context)
        (A : Finset (LatticePoint ambient)) (hA : selector.Eligible A),
        Real.rpow (initialCard : ℝ) p ≤ (A.card : ℝ) →
        (selector.chosen A hA).dimension ≤ rankCeiling →
        0 < (selector.chosen A hA).dimension →
        (1 / 2 : ℝ) * (A.card : ℝ) ≤
          ((selector.chosen A hA).identifiedCore.card : ℝ) →
        let slab := sourceFunctionalSlabBudget
          (delta kappa initialCard) A.card
        let t := sourceFunctionalSlabThickness context rankCeiling
          forwardConstant reverseConstant (gamma kappa K initialCard)
        SourceFunctionalSlabScalarHierarchy selector A hA
            (delta kappa initialCard) (gamma kappa K initialCard)
            forwardConstant slab t ∧
          SourceFunctionalSlabScalarHierarchy selector A hA
            (delta kappa initialCard) (gamma kappa K initialCard)
            reverseConstant slab t := by
  obtain ⟨threshold, hthreshold⟩ := Filter.eventually_atTop.mp
    (eventually_sourceFunctionalSlabPowerRangeScalarHierarchies
      context rankCeiling heta p hp kappa K hK
        forwardConstant reverseConstant hforward hreverse)
  exact ⟨threshold, fun hlarge selector A hA hlower hrank hd hhalf ↦
    hthreshold _ hlarge selector A hA hlower hrank hd hhalf⟩

/-- Exact source slab hierarchy with all analytic parameters frozen at the
initial population and uniformly valid on its retained square-root range. -/
theorem eventually_sourceFunctionalSlabFrozenScalarHierarchies
    {beta eta : ℝ}
    (context : Reduction.HigherDimensionalContext beta eta)
    (rankCeiling : ℕ) (heta : 0 < eta)
    (kappa K : ℝ) (hK : 0 < K)
    (forwardConstant reverseConstant : ℝ)
    (hforward : 0 ≤ forwardConstant) (hreverse : 0 ≤ reverseConstant) :
    ∀ᶠ initialCard : ℕ in atTop,
      ∀ {ambient : ℕ} (selector : Reduction.BoundedCFPSelector context)
        (A : Finset (LatticePoint ambient)) (hA : selector.Eligible A),
        Real.sqrt (initialCard : ℝ) ≤ (A.card : ℝ) →
        (selector.chosen A hA).dimension ≤ rankCeiling →
        0 < (selector.chosen A hA).dimension →
        (1 / 2 : ℝ) * (A.card : ℝ) ≤
          ((selector.chosen A hA).identifiedCore.card : ℝ) →
        let slab := sourceFunctionalSlabBudget
          (delta kappa initialCard) A.card
        let t := sourceFunctionalSlabThickness context rankCeiling
          forwardConstant reverseConstant (gamma kappa K initialCard)
        SourceFunctionalSlabScalarHierarchy selector A hA
            (delta kappa initialCard) (gamma kappa K initialCard)
            forwardConstant slab t ∧
          SourceFunctionalSlabScalarHierarchy selector A hA
            (delta kappa initialCard) (gamma kappa K initialCard)
            reverseConstant slab t := by
  have hbox := eventually_sourceFunctionalSlab_frozen_boxScale
    context rankCeiling kappa K hK forwardConstant reverseConstant
      hforward hreverse
  have hlow := eventually_sourceFunctionalSlab_frozen_lowRank
    context rankCeiling heta kappa K hK forwardConstant reverseConstant
      hforward hreverse
  filter_upwards [hbox, hlow, eventually_delta_pos kappa,
      eventually_gamma_pos kappa hK]
    with initialCard hboxN hlowN hdeltaN hgammaN
  intro ambient selector A hA hsqrt hrank hd hhalf
  let slab := sourceFunctionalSlabBudget
    (delta kappa initialCard) A.card
  let t := sourceFunctionalSlabThickness context rankCeiling
    forwardConstant reverseConstant (gamma kappa K initialCard)
  have ht : 0 < t := by
    dsimp only [t]
    exact sourceFunctionalSlabThickness_pos hforward hreverse hgammaN
  have hdensity : delta kappa initialCard * (A.card : ℝ) ≤
      (slab : ℝ) := by
    dsimp only [slab]
    exact sourceFunctionalSlabBudget_density _ _
  have hboxScale :
      1 ≤ (2 * ((selector.chosen A hA).dimension : ℝ) * t) *
        ((controlIntegerBox (selector.chosen A hA).progression
          (2 * context.scaleDen
            (selector.chosen A hA).dimension)).carrier.card : ℝ) := by
    simpa only [t] using hboxN selector A hA hsqrt hd hhalf
  have hlowForward :
      ∀ (Z : Finset (LatticePoint (selector.chosen A hA).dimension))
        (hZ : selector.Eligible Z),
        delta kappa initialCard * (A.card : ℝ) ≤ (Z.card : ℝ) →
        sourceFunctionalSlabFixedTerm context forwardConstant
            (selector.chosen A hA).dimension <
          ((selector.chosen Z hZ).dilation : ℝ) *
            gamma kappa K initialCard := by
    intro Z hZ hdense
    exact (hlowN A.card hsqrt (selector.input Z hZ) hrank hdense).1
  have hlowReverse :
      ∀ (Z : Finset (LatticePoint (selector.chosen A hA).dimension))
        (hZ : selector.Eligible Z),
        delta kappa initialCard * (A.card : ℝ) ≤ (Z.card : ℝ) →
        sourceFunctionalSlabFixedTerm context reverseConstant
            (selector.chosen A hA).dimension <
          ((selector.chosen Z hZ).dilation : ℝ) *
            gamma kappa K initialCard := by
    intro Z hZ hdense
    exact (hlowN A.card hsqrt (selector.input Z hZ) hrank hdense).2
  have hfullForward :
      sourceFunctionalSlabFullTerm context forwardConstant
          (selector.chosen A hA).dimension * t <
        gamma kappa K initialCard := by
    dsimp only [t]
    exact sourceFunctionalSlabFullTerm_mul_thickness_lt
      hforward hreverse hgammaN hrank
  have hfullReverse :
      sourceFunctionalSlabFullTerm context reverseConstant
          (selector.chosen A hA).dimension * t <
        gamma kappa K initialCard := by
    dsimp only [t]
    exact sourceFunctionalSlabReverseFullTerm_mul_thickness_lt
      hforward hreverse hgammaN hrank
  dsimp only
  constructor
  · refine {
      t_pos := ht
      density := hdensity
      box_scale := hboxScale
      low_rank := ?_
      full_rank := ?_ }
    · intro Z hZ hdense
      simpa only [sourceFunctionalSlabFixedTerm] using
        hlowForward Z hZ hdense
    · rw [sourceFunctionalSlabFullExpression_eq]
      exact hfullForward
  · refine {
      t_pos := ht
      density := hdensity
      box_scale := hboxScale
      low_rank := ?_
      full_rank := ?_ }
    · intro Z hZ hdense
      simpa only [sourceFunctionalSlabFixedTerm] using
        hlowReverse Z hZ hdense
    · rw [sourceFunctionalSlabFullExpression_eq]
      exact hfullReverse

/-- Population-threshold spelling of the frozen hierarchy. -/
theorem exists_sourceFunctionalSlabFrozenScalarHierarchyThreshold
    {beta eta : ℝ}
    (context : Reduction.HigherDimensionalContext beta eta)
    (rankCeiling : ℕ) (heta : 0 < eta)
    (kappa K : ℝ) (hK : 0 < K)
    (forwardConstant reverseConstant : ℝ)
    (hforward : 0 ≤ forwardConstant) (hreverse : 0 ≤ reverseConstant) :
    ∃ threshold : ℕ, ∀ {initialCard ambient : ℕ},
      threshold ≤ initialCard →
      ∀ (selector : Reduction.BoundedCFPSelector context)
        (A : Finset (LatticePoint ambient)) (hA : selector.Eligible A),
        Real.sqrt (initialCard : ℝ) ≤ (A.card : ℝ) →
        (selector.chosen A hA).dimension ≤ rankCeiling →
        0 < (selector.chosen A hA).dimension →
        (1 / 2 : ℝ) * (A.card : ℝ) ≤
          ((selector.chosen A hA).identifiedCore.card : ℝ) →
        let slab := sourceFunctionalSlabBudget
          (delta kappa initialCard) A.card
        let t := sourceFunctionalSlabThickness context rankCeiling
          forwardConstant reverseConstant (gamma kappa K initialCard)
        SourceFunctionalSlabScalarHierarchy selector A hA
            (delta kappa initialCard) (gamma kappa K initialCard)
            forwardConstant slab t ∧
          SourceFunctionalSlabScalarHierarchy selector A hA
            (delta kappa initialCard) (gamma kappa K initialCard)
            reverseConstant slab t := by
  obtain ⟨threshold, hthreshold⟩ := Filter.eventually_atTop.mp
    (eventually_sourceFunctionalSlabFrozenScalarHierarchies
      context rankCeiling heta kappa K hK forwardConstant reverseConstant
        hforward hreverse)
  exact ⟨threshold, fun hlarge selector A hA hsqrt hrank hd hhalf ↦
    hthreshold _ hlarge selector A hA hsqrt hrank hd hhalf⟩

end

end Erdos186.PZ.Intersection
