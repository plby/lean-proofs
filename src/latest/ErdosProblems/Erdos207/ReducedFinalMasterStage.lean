/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.IterationDynamicMasterLinkStageReduced
import ErdosProblems.Erdos207.MasterCoverDownExtraction

/-!
# Terminal extraction from the reduced dynamic-link scalars

At the final vortex step one may deterministically choose the robust link
matchings.  The resulting master cover step can be sent immediately to the
outside-packing extraction theorem, so no distributional estimate for a
later stage is required.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The reduced dynamic-link hypotheses at the terminal vortex step produce
the exact KSSS outside packing. -/
theorem exists_ksssOutsidePacking_of_reducedFinalLinkScalars
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k : Fin (ell + 1)}
    {q : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B : TripleSystemOn V}
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A I D R : TripleSystemOn V}
    {p eta xi : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W k G A p eta xi h)
    (htri : ConsistsOfTriangles G A)
    (i : Fin ell) (hki : k.val ≤ i.val)
    (hX : X = W.U i.succ)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V))
    (heven : ∀ v, Even (G.degree v))
    (hold : G ≤ leaveGraph (I ∪ D))
    (hRselected : R ⊆ A)
    (hRcover : ∀ u v : V, G.Adj u v →
      u ∉ W.U i.succ → v ∉ W.U i.succ →
      (coveredGraph R).Adj u v)
    (hpreDisjoint : Disjoint I (D ∪ R))
    (hprePacking : IsPackingOn (I ∪ (D ∪ R)))
    (hpreAvoid : AvoidsForbidden (I ∪ (D ∪ R))
      (absorberErdosForbiddenConfigurationsOn q B))
    (m d Dmax codegree loss sideMax : ℕ)
    (hh : 3 ≤ h)
    (hlower : (m + loss + 1 : ℝ≥0) ≤
      (1 - xi) * (p ^ 2 * eta * (W.U i.succ).card))
    (hupper : (1 + xi) * (p ^ 2 * eta * (W.U i.succ).card) ≤
      (Dmax : ℝ≥0))
    (hcodegree : (1 + xi) *
      (p ^ 3 * eta ^ 2 * (W.U i.succ).card) ≤ (codegree : ℝ≥0))
    (hstageDegree : ∀ v : V, G.degree v ≤ sideMax)
    (hcoveredBudget : ∀ v : V,
      (coveredGraph (I ∪ (D ∪ R))).degree v + G.degree v ≤ loss)
    (hbisectionScalar : (sideMax : ℝ≥0) *
      (2 * (2 : ℝ≥0) ^ d * (3 / 4 : ℝ≥0) ^ (m - 2 * d)) < 1)
    (Delta groupSize density candidate cutoff degreeCutoff rootCutoff
      familyCutoff momentOrder : ℕ)
    (hdensityLe : density ≤ d)
    (hmixingScalar : sideMax * (Dmax + codegree * sideMax) <
      (cutoff + 1) * (d - density) ^ 2)
    (hdegreeScalar : Delta * groupSize + groupSize ≤ d - cutoff)
    (hdTwo : 2 ≤ d)
    (hdensityScalar : 3 * candidate ≤ density)
    (hcandidateScalar : Delta * groupSize + groupSize ≤ candidate)
    (sampleProbability : ℝ≥0) (hprob : sampleProbability ≤ 1)
    (kappa epsilon : ℝ≥0)
    (hkappa : ∀ (P : TripleSystemOn V),
      IsDynamicLinkState
        (absorberErdosForbiddenConfigurationsOn q B) A I D R P →
      ∀ o : {x : V // x ∉ W.U i.succ},
      ∀ K : BipartiteLink V, IsResidualBipartition G P o.1 K →
      ∀ x : ↥K.left ⊕ ↥K.right,
        HasExtensionBound
          (fun z : RootedThreatWitness V
              (absorberErdosForbiddenConfigurationsOn q B) K.center
              (linkSideEndpoint K x) ↦
            relativeRootedThreatRemainder P z)
          (fun _ ↦ sampleProbability) kappa)
    (hrootScalar : (2 * sideMax : ℝ≥0) *
      ((((2 : ℝ≥0) ^ (momentOrder * (familyCutoff - 1)) * kappa) ^
          momentOrder) /
        (rootCutoff + 1 : ℝ≥0) ^ momentOrder) ≤ epsilon)
    (hsampleScalar : epsilon +
      (2 * 4 ^ sideMax * (Delta * sideMax + 1) : ℝ≥0) *
        (1 - sampleProbability) ^ groupSize < 1)
    (hfamily : ∀ C ∈ absorberErdosForbiddenConfigurationsOn q B,
      C.card ≤ familyCutoff)
    (hdegreeBudget : ∀ u v : V,
      ((coveredGraph (I ∪ (D ∪ R))).degree u + G.degree u) +
        ((coveredGraph (I ∪ (D ∪ R))).degree v + G.degree v) ≤
          degreeCutoff)
    (hdeletionScalar : degreeCutoff + rootCutoff * familyCutoff ≤ Delta)
    (hA : A ⊆ outsideAvailableTriangles H B)
    (hselected : I ∪ D ⊆ outsideAvailableTriangles H B)
    (hcover : CoversOriginalGraph
      (graphDifference (SimpleGraph.completeGraph V) H) G I D) :
    ∃ P : TripleSystemOn V, HasKSSSOutsidePacking q H X B P := by
  obtain ⟨M, hM⟩ := htyp.exists_masterCoverStep_of_reduced_link_scalars_good
    htri i hki hGsupp heven hold hRselected hRcover hpreDisjoint
    hprePacking hpreAvoid m d Dmax codegree loss sideMax hh hlower hupper
    hcodegree hstageDegree hcoveredBudget hbisectionScalar Delta groupSize
    density candidate cutoff degreeCutoff rootCutoff familyCutoff momentOrder
    hdensityLe hmixingScalar hdegreeScalar hdTwo hdensityScalar
    hcandidateScalar sampleProbability hprob kappa epsilon hkappa
    hrootScalar hsampleScalar hfamily hdegreeBudget hdeletionScalar
  refine ⟨I ∪ (D ∪ M), ?_⟩
  subst X
  exact hasKSSSOutsidePacking_of_finalMasterCoverStep_of_available_subset
    hA hselected hcover hM

end

end Erdos207
