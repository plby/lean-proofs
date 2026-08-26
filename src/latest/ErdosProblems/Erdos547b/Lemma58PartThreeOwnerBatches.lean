/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58PartThreeEmbedding
import ErdosProblems.Erdos547b.Lemma58ChosenOwnerBatches

/-!
# Concrete owner-by-owner realization of Zhao Lemma 5.4(3)

This module discharges the chosen owner-batch callback with the actual
Appendix A.2/A.1 constructor.  Its inputs are only the live root pools,
finite Appendix capacity data, parent identities, and regular-pair scalar
facts at each residual state.  No local embedding, copy, or continuation
conclusion is supplied by the caller.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma58PartThreeOwnerBatches

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma54AppendixA
open Erdos547b.ZhaoLemma58DynamicBatchAppend
open Erdos547b.ZhaoLemma58ChosenOwnerBatches
open Erdos547b.ZhaoLemma58PartThreeEmbedding

universe v

/-- Realize every owner batch on one Part-3 matching edge, choosing its
orientation from the current live capacities and deleting its actual image
before processing the next owner. -/
theorem exists_partThreeEmbedding_of_ownerBatches
    {b r : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B) (parent : Fin r → B)
    (whole available : Fin 2 → Finset B)
    (owner : Fin b → Fin r)
    (small rootMargin sideMargin : ℕ)
    (rho density gamma epsilon N : ℝ)
    (hunif : G.IsUniform rho (whole 0) (whole 1))
    (havailable : ∀ c, available c ⊆ whole c)
    (hwholeDisjoint : Disjoint (whole 0) (whole 1))
    (hdensity : density ≤ G.edgeDensity (whole 0) (whole 1))
    (hfactor : 0 ≤ density - rho)
    (hepsilonN : 0 ≤ epsilon * N)
    (hregularRoot : ∀ c,
      rho * (#(whole c) : ℝ) < 3 * epsilon * N)
    (hregularInterior : ∀ c,
      rho * (#(whole c) : ℝ) ≤ gamma * N)
    (hdata : ∀ n (hn : n < r)
      (Eprefix : ChosenPartialDynamicEmbedding F G externalParent available
        (ownerPrefix Finset.univ owner n)),
      ∃ rootPool : Fin 2 → Finset B,
        Nonempty (AppendixA2NumericData
          (selectedForest F (ownerBatch Finset.univ owner ⟨n, hn⟩))
          small rootMargin sideMargin
          #(available 0 \ Eprefix.used 0)
          #(available 1 \ Eprefix.used 1)
          #(rootPool 0) #(rootPool 1) gamma epsilon N) ∧
        (∀ c, rootPool c ⊆ available c \ Eprefix.used c) ∧
        (∀ k, externalParent
          (OrderedBranchForest.selectedEquiv
            (ownerBatch Finset.univ owner ⟨n, hn⟩) k) = parent ⟨n, hn⟩) ∧
        (∀ c w, w ∈ rootPool c → G.Adj (parent ⟨n, hn⟩) w) ∧
        (∀ i c,
          ((selectedForest F
            (ownerBatch Finset.univ owner ⟨n, hn⟩)).size i : ℝ) +
              rho * (#(whole c) : ℝ) ≤
            (density - rho) * (gamma * N))) :
    ∃ orient : Fin b → Fin 2 ≃ Fin 2,
      Nonempty (DynamicAttachedForestEmbedding
        F G externalParent orient available) := by
  apply exists_dynamicAttachedForestEmbedding_of_chosenOwnerBatches
    F G externalParent whole available havailable hwholeDisjoint owner
  intro n hn Eprefix
  obtain ⟨rootPool, ⟨D⟩, hrootPool, hparent, hattach, hmargin⟩ :=
    hdata n hn Eprefix
  let Fbatch := selectedForest F
    (ownerBatch Finset.univ owner ⟨n, hn⟩)
  let live : Fin 2 → Finset B := fun c ↦ available c \ Eprefix.used c
  have hlive (c : Fin 2) : live c ⊆ whole c :=
    Finset.sdiff_subset.trans (havailable c)
  obtain ⟨E⟩ := exists_partThreeDynamicGroupEmbedding
    Fbatch small rootMargin sideMargin G (parent ⟨n, hn⟩)
    whole live rootPool rho density gamma epsilon N D hunif hlive
    hrootPool hwholeDisjoint hdensity hfactor hepsilonN hregularRoot
    hregularInterior hmargin hattach
  let Eactual : DynamicAttachedForestEmbedding Fbatch G
      (fun k ↦ externalParent
        (OrderedBranchForest.selectedEquiv
          (ownerBatch Finset.univ owner ⟨n, hn⟩) k))
      E.orient live := {
    embedding := E.embedding.embedding
    attach := by
      intro k
      rw [hparent k]
      exact E.embedding.attach k
    map_side := E.embedding.map_side
  }
  exact ⟨E.orient, ⟨Eactual⟩⟩

end Erdos547b.ZhaoLemma58PartThreeOwnerBatches

#print axioms Erdos547b.ZhaoLemma58PartThreeOwnerBatches.exists_partThreeEmbedding_of_ownerBatches
