/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.SourceFunctionalSlabBoxScale
import ErdosProblems.Erdos186.PZ.Intersection.SourceFunctionalSlabLowRank

/-!
# Uniform source functional-slab scalar closure

This file packages the explicit ceiling slab and common thickness into the
literal scalar hierarchy consumed by the source and box-weighted functional
slab cardinality theorems.  All choices depend only on the fixed context,
rank ceiling, source parameters, and the two slab constants; the population
threshold is independent of the eligible input and its selected witness.
-/

namespace Erdos186.PZ.Intersection

open Filter
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- At the source parameter choice, one explicit ceiling slab and one common
positive thickness eventually satisfy all four forward and reverse scalar
requirements simultaneously. -/
theorem eventually_sourceFunctionalSlabScalarHierarchies
    {beta eta : ℝ}
    (context : Reduction.HigherDimensionalContext beta eta)
    (rankCeiling : ℕ) (heta : 0 < eta)
    (kappa K : ℝ) (hkappa : 0 < kappa) (hK : 0 < K)
    (forwardConstant reverseConstant : ℝ)
    (hforward : 0 ≤ forwardConstant) (hreverse : 0 ≤ reverseConstant) :
    ∀ᶠ N : ℕ in atTop,
      ∀ {ambient : ℕ} (selector : Reduction.BoundedCFPSelector context)
        (A : Finset (LatticePoint ambient)) (hA : selector.Eligible A),
        A.card = N →
        (selector.chosen A hA).dimension ≤ rankCeiling →
        0 < (selector.chosen A hA).dimension →
        (1 / 2 : ℝ) * (N : ℝ) ≤
          ((selector.chosen A hA).identifiedCore.card : ℝ) →
        let slab := sourceFunctionalSlabBudget (delta kappa N) N
        let t := sourceFunctionalSlabThickness context rankCeiling
          forwardConstant reverseConstant (gamma kappa K N)
        SourceFunctionalSlabScalarHierarchy selector A hA
            (delta kappa N) (gamma kappa K N) forwardConstant slab t ∧
          SourceFunctionalSlabScalarHierarchy selector A hA
            (delta kappa N) (gamma kappa K N) reverseConstant slab t := by
  have hbox := eventually_sourceFunctionalSlab_boxScale context rankCeiling
    kappa K hkappa hK forwardConstant reverseConstant hforward hreverse
  have hlow := eventually_sourceFunctionalSlab_lowRank context rankCeiling
    heta kappa K hK forwardConstant reverseConstant hforward hreverse
  filter_upwards [hbox, hlow, eventually_delta_pos kappa,
      eventually_gamma_pos kappa hK]
    with N hboxN hlowN hdeltaN hgammaN
  intro ambient selector A hA hcard hrank hd hhalf
  subst N
  let slab := sourceFunctionalSlabBudget (delta kappa A.card) A.card
  let t := sourceFunctionalSlabThickness context rankCeiling
    forwardConstant reverseConstant (gamma kappa K A.card)
  have ht : 0 < t := by
    dsimp only [t]
    exact sourceFunctionalSlabThickness_pos hforward hreverse hgammaN
  have hdensity : delta kappa A.card * (A.card : ℝ) ≤ (slab : ℝ) := by
    dsimp only [slab]
    exact sourceFunctionalSlabBudget_density _ _
  have hboxScale :
      1 ≤ (2 * ((selector.chosen A hA).dimension : ℝ) * t) *
        ((controlIntegerBox (selector.chosen A hA).progression
          (2 * context.scaleDen
            (selector.chosen A hA).dimension)).carrier.card : ℝ) := by
    simpa only [t] using hboxN selector A hA rfl hd hhalf
  have hlowForward :
      ∀ (Z : Finset (LatticePoint (selector.chosen A hA).dimension))
        (hZ : selector.Eligible Z),
        delta kappa A.card * (A.card : ℝ) ≤ (Z.card : ℝ) →
        sourceFunctionalSlabFixedTerm context forwardConstant
            (selector.chosen A hA).dimension <
          ((selector.chosen Z hZ).dilation : ℝ) * gamma kappa K A.card := by
    intro Z hZ hdense
    exact (hlowN (selector.input Z hZ) hrank hdense).1
  have hlowReverse :
      ∀ (Z : Finset (LatticePoint (selector.chosen A hA).dimension))
        (hZ : selector.Eligible Z),
        delta kappa A.card * (A.card : ℝ) ≤ (Z.card : ℝ) →
        sourceFunctionalSlabFixedTerm context reverseConstant
            (selector.chosen A hA).dimension <
          ((selector.chosen Z hZ).dilation : ℝ) * gamma kappa K A.card := by
    intro Z hZ hdense
    exact (hlowN (selector.input Z hZ) hrank hdense).2
  have hfullForward :
      sourceFunctionalSlabFullTerm context forwardConstant
          (selector.chosen A hA).dimension * t < gamma kappa K A.card := by
    dsimp only [t]
    exact sourceFunctionalSlabFullTerm_mul_thickness_lt
      hforward hreverse hgammaN hrank
  have hfullReverse :
      sourceFunctionalSlabFullTerm context reverseConstant
          (selector.chosen A hA).dimension * t < gamma kappa K A.card := by
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

/-- Population-threshold form of
`eventually_sourceFunctionalSlabScalarHierarchies`. -/
theorem exists_sourceFunctionalSlabScalarHierarchyThreshold
    {beta eta : ℝ}
    (context : Reduction.HigherDimensionalContext beta eta)
    (rankCeiling : ℕ) (heta : 0 < eta)
    (kappa K : ℝ) (hkappa : 0 < kappa) (hK : 0 < K)
    (forwardConstant reverseConstant : ℝ)
    (hforward : 0 ≤ forwardConstant) (hreverse : 0 ≤ reverseConstant) :
    ∃ M : ℕ,
      ∀ {ambient : ℕ} (selector : Reduction.BoundedCFPSelector context)
        (A : Finset (LatticePoint ambient)) (hA : selector.Eligible A),
        M ≤ A.card →
        (selector.chosen A hA).dimension ≤ rankCeiling →
        0 < (selector.chosen A hA).dimension →
        (1 / 2 : ℝ) * (A.card : ℝ) ≤
          ((selector.chosen A hA).identifiedCore.card : ℝ) →
        let slab := sourceFunctionalSlabBudget
          (delta kappa A.card) A.card
        let t := sourceFunctionalSlabThickness context rankCeiling
          forwardConstant reverseConstant (gamma kappa K A.card)
        SourceFunctionalSlabScalarHierarchy selector A hA
            (delta kappa A.card) (gamma kappa K A.card)
            forwardConstant slab t ∧
          SourceFunctionalSlabScalarHierarchy selector A hA
            (delta kappa A.card) (gamma kappa K A.card)
            reverseConstant slab t := by
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp
    (eventually_sourceFunctionalSlabScalarHierarchies context rankCeiling
      heta kappa K hkappa hK forwardConstant reverseConstant
      hforward hreverse)
  refine ⟨M, ?_⟩
  intro ambient selector A hA hlarge hrank hd hhalf
  exact hM A.card hlarge selector A hA rfl hrank hd hhalf

end

end Erdos186.PZ.Intersection
