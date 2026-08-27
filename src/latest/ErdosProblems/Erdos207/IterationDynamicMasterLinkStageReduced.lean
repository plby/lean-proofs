/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.DynamicLinkScalarControl

/-!
# State-independent hypotheses for the dynamic master link stage

This wrapper removes the degree, bisection, mixing, sampling, and endpoint
degree hypotheses quantified over every dynamically reached packing.  They
are all consequences of fixed degree budgets for the stage graph and the
pre-link packing.  The only remaining state-dependent probabilistic input is
the relative rooted-threat extension bound.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem IsIterationTypical.exists_masterCoverStep_of_reduced_link_scalars_good
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k : Fin (ell + 1)}
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {F : ForbiddenFamilyOn V} {A I D R : TripleSystemOn V}
    {p eta ξ : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W k G A p eta ξ h)
    (htri : ConsistsOfTriangles G A)
    (i : Fin ell) (hki : k.val ≤ i.val)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V))
    (heven : ∀ v, Even (G.degree v))
    (hold : G ≤ leaveGraph (I ∪ D))
    (hRselected : R ⊆ A)
    (hRcover : ∀ u v : V, G.Adj u v →
      u ∉ W.U i.succ → v ∉ W.U i.succ →
      (coveredGraph R).Adj u v)
    (hpreDisjoint : Disjoint I (D ∪ R))
    (hprePacking : IsPackingOn (I ∪ (D ∪ R)))
    (hpreAvoid : AvoidsForbidden (I ∪ (D ∪ R)) F)
    (m d Dmax codegree loss sideMax : ℕ)
    (hh : 3 ≤ h)
    (hlower : (m + loss + 1 : ℝ≥0) ≤
      (1 - ξ) * (p ^ 2 * eta * (W.U i.succ).card))
    (hupper : (1 + ξ) * (p ^ 2 * eta * (W.U i.succ).card) ≤
      (Dmax : ℝ≥0))
    (hcodegree : (1 + ξ) *
      (p ^ 3 * eta ^ 2 * (W.U i.succ).card) ≤
        (codegree : ℝ≥0))
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
      IsDynamicLinkState F A I D R P →
      ∀ o : {x : V // x ∉ W.U i.succ},
      ∀ K : BipartiteLink V, IsResidualBipartition G P o.1 K →
      ∀ x : ↥K.left ⊕ ↥K.right,
        HasExtensionBound
          (fun z : RootedThreatWitness V F K.center
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
    (hfamily : ∀ C ∈ F, C.card ≤ familyCutoff)
    (hdegreeBudget : ∀ u v : V,
      ((coveredGraph (I ∪ (D ∪ R))).degree u + G.degree u) +
        ((coveredGraph (I ∪ (D ∪ R))).degree v + G.degree v) ≤
          degreeCutoff)
    (hdeletionScalar : degreeCutoff + rootCutoff * familyCutoff ≤ Delta) :
    ∃ M : TripleSystemOn V,
      IsMasterCoverStep F G (W.U i.succ) A I D M := by
  refine htyp.exists_masterCoverStep_of_dynamic_link_scalars_good htri i hki
    hGsupp heven hold hRselected hRcover hpreDisjoint hprePacking hpreAvoid
    m d Dmax codegree loss hh hlower hupper hcodegree ?_ ?_
    Delta groupSize density candidate cutoff degreeCutoff rootCutoff
    familyCutoff hdensityLe ?_ hdegreeScalar hdTwo hdensityScalar
    hcandidateScalar sampleProbability hprob epsilon ?_ ?_ hfamily ?_
    hdeletionScalar
  · intro P hstate o
    exact dynamic_covered_degree_le_of_fixed_budget htri hstate
      hcoveredBudget o.1
  · intro P _hstate o
    apply dynamic_bisection_scalar_of_degree P o.1 m d
    apply lt_of_le_of_lt _ hbisectionScalar
    gcongr
    exact_mod_cast hstageDegree o.1
  · intro P _hstate o K hK hpositive
    apply hK.mixing_scalar_of_degree_upper sideMax d Dmax codegree density
      cutoff
    · simpa only [hK.1] using hstageDegree o.1
    · exact hmixingScalar
  · intro P hstate o K hK _hpositive
    exact hK.rootedBad_le_of_degree_extension_scalar F sampleProbability
      hprob sideMax (by simpa only [hK.1] using hstageDegree o.1)
      kappa epsilon rootCutoff hfamily (hkappa P hstate o K hK)
      hrootScalar
  · intro P _hstate o K hK _hpositive
    apply hK.sampling_scalar_of_degree_upper sideMax Delta groupSize
      sampleProbability epsilon
    · simpa only [hK.1] using hstageDegree o.1
    · exact hsampleScalar
  · intro P hstate _o K _hK
    exact dynamic_link_side_degrees_le_of_fixed_budget htri hstate
      hdegreeBudget K

end

end Erdos207
