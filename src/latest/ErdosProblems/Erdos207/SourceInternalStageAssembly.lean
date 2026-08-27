/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CorrelatedInternalLinkPerturbation
import ErdosProblems.Erdos207.IntermediateLinkSourceGeometry

/-! # One actual correlated internal kernel supplies the corrected law and link preparation -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem IsResidualReserveStronglyWellDistributed.exists_source_internal_preparation
    {Omega Xi V : Type*} [Fintype Omega] [DecidableEq Omega] [Fintype Xi] [DecidableEq Xi]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {W : Vortex V ell} (i : Fin ell)
    (orders : Finset ℕ) (F : ℕ → ForbiddenFamilyOn V)
    (G : Omega → SimpleGraph V) (A initial later : Omega → TripleSystemOn V)
    (bits : Omega → Sym2 V → Bool) (Gamma : SimpleGraph V)
    {p r C beta : ℝ≥0}
    (hstrong : IsResidualReserveStronglyWellDistributed L W i.castSucc Gamma initial later
      (fun omega ↦ reserveEdges (G omega) (W.U i.succ) (bits omega)) p r C beta)
    (Kpre : Omega → FiniteLaw Xi) (pre : Omega → Xi → TripleSystemOn V)
    (survival point constant preError rate mu alpha factor epsilon error : ℝ≥0)
    (degreeMoment : ℕ) (s : ℕ → ℕ) (y z leftError : ℕ → ℝ≥0)
    (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1) (hC : 1 ≤ C)
    (hconstant : 1 ≤ constant) (hfactor : 1 ≤ factor) (hmu : 512 ≤ mu)
    (halpha : alpha ≤ 1) (hrate : rate ≤ r) (hepsilon : 0 < epsilon)
    (hnonempty : ∀ j, (W.U j).Nonempty)
    (hnew : alpha*p^3 ≤ factor*(p/(W.U i.castSucc).card))
    (halphaBound : constant*point+(constant*survival)*(64/mu) ≤ alpha)
    (hRate : constant*survival ≤ rate)
    (hcap : epsilon*p^2*r^2*(W.U i.succ).card ≤ ⌈mu/128⌉₊)
    (hdegreeMoment : 2*degreeMoment ≤ ⌊mu/256⌋₊+1)
    (hsource : ∀ j ∈ orders, SourceVortexWellSpread (W.prefix i.castSucc) j (F j) (y j) (z j))
    (hscale : ∀ j ∈ orders, z j ≤ y j*r^2*p^3*(W.U i.succ).card)
    (hscalar : ∀ j ∈ orders,
      sourceLeftFailureBound i.val j (s j) (Fintype.card V) p r
        (2*max (C^3*factor) (2*constant)) (beta+preError) (y j)
        (epsilon/(orders.card+1 : ℝ≥0)) (W.U i.succ).card ≤ leftError j)
    (hmixed : ∀ omega, 0 < L.mass omega → IsGraphMixedProductBound (Kpre omega) (pre omega)
      (reserveProtectedOuterGraph (G omega) (W.U i.succ)
        (reserveEdges (G omega) (W.U i.succ) (bits omega))) survival point constant preError)
    (hGsupport : ∀ omega, 0 < L.mass omega → GraphSupportedOn (G omega) (W.U i.castSucc : Set V))
    (hbase : ∀ omega, 0 < L.mass omega → G omega ≤ Gamma)
    (hGleave : ∀ omega, 0 < L.mass omega → G omega ≤ leaveGraph (initial omega ∪ later omega))
    (htri : ∀ omega, 0 < L.mass omega → ConsistsOfTriangles (G omega) (A omega))
    (heven : HasEvenStageGraphs L G)
    (hdisjoint : ∀ omega, 0 < L.mass omega → Disjoint (initial omega) (later omega))
    (hpre : ∀ omega, 0 < L.mass omega → (Kpre omega).SupportedOn fun xi ↦ pre omega xi ⊆ A omega ∧
      IsPackingOn ((initial omega ∪ later omega) ∪ pre omega xi) ∧
      Disjoint (initial omega ∪ later omega) (pre omega xi) ∧
      AvoidsForbidden ((initial omega ∪ later omega) ∪ pre omega xi) (orders.biUnion F))
    (hinitial : ∀ omega, 0 < L.mass omega → ∀ T ∈ A omega,
      ¬ CompletesForbidden (orders.biUnion F) (initial omega) T)
    (hprotected : ∀ omega, 0 < L.mass omega → (Kpre omega).SupportedOn fun xi ↦
      pre omega xi ⊆ reserveProtectedAvailable (reserveEdges (G omega) (W.U i.succ) (bits omega)) (A omega))
    (hmeet : ∀ omega, 0 < L.mass omega → (Kpre omega).SupportedOn fun xi ↦
      TrianglesMeetAtMostOne (W.U i.succ) (pre omega xi))
    (hreserve : ∀ omega, 0 < L.mass omega →
      InternalReserveSupplyGood (G omega) (A omega) (W.U i.succ) ⌊mu/8⌋₊ (bits omega))
    (herror : error < 1)
    (herrorBound : sourcePreliminaryDegreeFailure (Fintype.card V) (W.U i.castSucc).card
      ⌊mu/256⌋₊ degreeMoment rate constant preError +
      (Fintype.card V : ℝ≥0)^2*∑ j ∈ orders, leftError j ≤ error) :
    let old := fun omega ↦ initial omega ∪ later omega
    let Kint := correlatedRawInternalKernel W i (orders.biUnion F) G A old pre bits ⌊mu/32⌋₊
    let intAdded := correlatedRawInternalAdded old pre
    let kernel := fun omega ↦ (Kpre omega).jointBind (Kint omega)
    let added := fun omega sample ↦ preliminaryInternalCombinedAdded (pre omega) (intAdded omega) sample
    let joint := L.jointBind kernel
    let reserve := fun sample : Omega × (Xi × InternalEdgeGreedyStateOn V) ↦
      preliminaryAugmentedReserve (G sample.1) (W.U i.succ)
        (reserveEdges (G sample.1) (W.U i.succ) (bits sample.1)) (added sample.1 sample.2)
    let Success := fun sample : Omega × (Xi × InternalEdgeGreedyStateOn V) ↦ sample.2.2.failed = false
    ∃ hpos : 0 < joint.probability Success,
      1-error ≤ joint.probability Success ∧
      IsResidualReserveStronglyWellDistributed (joint.conditionOn Success hpos) W i.castSucc Gamma
        (jointInitial initial) (jointLater later added) reserve p r
        ((2*max (C^3*factor) (2*constant))/(1-error)) (beta+preError) ∧
      (joint.conditionOn Success hpos).probability (fun sample ↦ ¬ PreliminaryResidualDegreeGood
        (reserveProtectedOuterGraph (G sample.1) (W.U i.succ)
          (reserveEdges (G sample.1) (W.U i.succ) (bits sample.1))) (W.U i.succ)
          (pre sample.1 sample.2.1) ⌊mu/256⌋₊) ≤
        sourcePreliminaryDegreeFailure (Fintype.card V) (W.U i.castSucc).card ⌊mu/256⌋₊
          degreeMoment rate constant preError/(1-error) ∧
      ∃ links : Omega × (Xi × InternalEdgeGreedyStateOn V) → {x : V // x ∉ W.U i.succ} → BipartiteLink V,
        (joint.conditionOn Success hpos).SupportedOn fun sample ↦
          IsIntermediateLinkState (G sample.1) (W.U i.succ) (A sample.1)
            (initial sample.1) (later sample.1) (added sample.1 sample.2) (links sample) ∧
          (∀ o, (links sample o).center = outsideVertexEmbedding (W.U i.succ) o) ∧
          (∀ o, (links sample o).left ⊆ W.U i.succ) ∧
          (∀ o, (links sample o).right ⊆ W.U i.succ) ∧
          (∀ o, (links sample o).SpokesIn (reserve sample)) ∧
          IsPackingOn (initial sample.1 ∪ (later sample.1 ∪ added sample.1 sample.2)) ∧
          AvoidsForbidden (initial sample.1 ∪ (later sample.1 ∪ added sample.1 sample.2)) (orders.biUnion F) ∧
          TrianglesMeetAtMostOne (W.U i.succ) (added sample.1 sample.2) := by
  dsimp only
  have hJ : 1 ≤ 2*constant := by
    have hh := mul_le_mul_of_nonneg_left hconstant (zero_le (a := (2 : ℝ≥0)))
    exact (by norm_num : (1 : ℝ≥0) ≤ 2).trans (by simpa only [mul_one] using hh)
  have hCraw : 1 ≤ 2*max (C^3*factor) (2*constant) := by
    have hm := mul_le_mul_of_nonneg_left (le_max_right (C^3*factor) (2*constant))
      (zero_le (a := (2 : ℝ≥0)))
    have hdouble : 1 ≤ 2*(2*constant) := by
      have hh := mul_le_mul_of_nonneg_left hJ (zero_le (a := (2 : ℝ≥0)))
      exact (by norm_num : (1 : ℝ≥0) ≤ 2).trans (by simpa only [mul_one] using hh)
    exact hdouble.trans hm
  have hvertices : ∀ omega, 0 < L.mass omega → ∀ T ∈ A omega, T.1 ⊆ W.U i.castSucc := by
    intro omega hm T hT
    exact (htri omega hm).triple_vertices_subset (hGsupport omega hm) hT
  have htriBase : ∀ omega, 0 < L.mass omega → ∀ T ∈ A omega, tripleEdgeFinset T ⊆ graphEdges Gamma := by
    intro omega hm
    have htriGamma : ConsistsOfTriangles Gamma (A omega) :=
      fun T hT u hu v hv huv ↦ hbase omega hm (htri omega hm T hT u hu v hv huv)
    exact fun T hT ↦ htriGamma.triple_edges_subset hT
  have hlevel : ∀ omega, 0 < L.mass omega → ∀ T ∈ A omega,
      (W.prefix i.castSucc).level T = Fin.last i.val := by
    intro omega hm T hT
    exact W.prefix_level_eq_last_of_subset i.castSucc T (hvertices omega hm T hT)
  have hraw := hstrong.jointBind_raw_correlatedInternal i (orders.biUnion F) G A initial later bits Gamma
    Kpre pre survival point constant mu alpha rate (2*constant) factor preError r hmu hC hJ hfactor
    halpha (hrate.trans hr1) le_rfl hrate hnonempty hnew hmixed halphaBound hRate le_rfl hGleave hpre
    htriBase hvertices
  have hfailure := correlatedRawInternal_failure_probability_le L W i orders F G A initial later bits Gamma
    Kpre pre p r (2*max (C^3*factor) (2*constant)) (beta+preError) survival point constant preError rate
    mu epsilon degreeMoment s y z leftError hmu hp hp1 hr hr1 hCraw hepsilon (hnonempty i.succ)
    hcap hdegreeMoment hsource hscale hscalar hmixed hRate hGsupport hbase hGleave hdisjoint hpre
    hlevel hinitial hprotected hreserve hraw
  obtain ⟨hpos, hlower, hgood, links, hlinks⟩ := condition_correlatedRawInternal_success L W i
    (orders.biUnion F) G A initial later bits Gamma Kpre pre ⌊mu/32⌋₊
    (internal_cover_rounded_budgets mu hmu).1 p r (2*max (C^3*factor) (2*constant)) (beta+preError)
    error herror heven hGleave htri hdisjoint hpre hmeet hraw (hfailure.trans herrorBound)
  refine ⟨hpos, hlower, hgood, ?_, links, hlinks⟩
  exact conditioned_correlatedRawInternal_degree_failure_le L W i (orders.biUnion F) G A
    (fun omega ↦ initial omega ∪ later omega) pre bits Kpre ⌊mu/32⌋₊ ⌊mu/256⌋₊ degreeMoment
    survival point constant preError rate error herror hmixed hGsupport hRate hdegreeMoment hpos hlower

end

end Erdos207
