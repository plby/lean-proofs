/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceResidualRootPacking

/-!
# Actual matching volume bounds in the two-q-vertex host

Each matching edge occupies two disjoint clusters of the actual common
size, and different matching edges have disjoint supports. Their literal
union therefore bounds the global and every local allocation count.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMatchingVolume

open Finset SimpleGraph Erdos547b.ZhaoSourceResidualRootPacking
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.ZhaoLemma611Full

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)

theorem matchingVolume_bound (hhost : hostN = 2 * q)
    (edges : Finset (MatchingEdge Q.claim67.M)) : (W.clusterSize : ℝ) * edges.card ≤ q := by
  let pair := fun e => edgeWhole W Q e 0 ∪ edgeWhole W Q e 1
  have hcard (e : MatchingEdge Q.claim67.M) : (pair e).card = 2 * W.clusterSize := by
    rw [Finset.card_union_of_disjoint (edgeWhole_disjoint W Q e), edgeWhole_card, edgeWhole_card]
    omega
  have hdisjoint : ∀ e ∈ edges, ∀ f ∈ edges, e ≠ f → Disjoint (pair e) (pair f) := by
    intro e _ f _ hne
    rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
    exact ⟨⟨edgeWhole_cross_disjoint W Q e f hne 0 0, edgeWhole_cross_disjoint W Q e f hne 0 1⟩,
      ⟨edgeWhole_cross_disjoint W Q e f hne 1 0, edgeWhole_cross_disjoint W Q e f hne 1 1⟩⟩
  have hcount : (edges.biUnion pair).card = edges.card * (2 * W.clusterSize) := by
    rw [Finset.card_biUnion hdisjoint]
    simp only [hcard, Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
  have hbound : edges.card * (2 * W.clusterSize) ≤ 2 * q := by
    rw [← hcount, ← hhost]
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (edges.biUnion pair))
  have hboundR : (edges.card : ℝ) * (2 * W.clusterSize) ≤ 2 * q := by exact_mod_cast hbound
  nlinarith only [hboundR]

theorem fullMatchingVolume_bound (hhost : hostN = 2 * q) :
    (W.clusterSize : ℝ) * Fintype.card (MatchingEdge Q.claim67.M) ≤ q := by
  simpa only [Finset.card_univ] using matchingVolume_bound W Q hhost Finset.univ

end Erdos547b.ZhaoSourceMatchingVolume

#print axioms Erdos547b.ZhaoSourceMatchingVolume.matchingVolume_bound
#print axioms Erdos547b.ZhaoSourceMatchingVolume.fullMatchingVolume_bound
