/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim61RichFull
import ErdosProblems.Erdos547b.Claim615HierarchicalSourceLayout
import ErdosProblems.Erdos547b.Claim616HierarchicalHostPools

/-!
# Concrete no-`C` host pools for Zhao Lemma 6.15

The Lemma-6.15 hierarchy has only two kinds of root slots: the exact
quantitative reserves `A₀`, `B₀`, and an oriented endpoint of a literal edge
of the original Claim-6.7 matching.  Matching-endpoint candidates have both
root reserves deleted.  This file records the resulting subset, cardinality,
and collision facts.

There is deliberately no exceptional-family selection, source orientation,
packing, embedding, copy, or continuation datum in this module.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim615HierarchicalHostPools

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoSection6Dichotomy
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim616HierarchicalHostPools
open Erdos547b.ZhaoClaim615HierarchicalSourceLayout

universe u v

variable {Bv : Type u} {I : Type v}
variable [Fintype Bv] [DecidableEq Bv] [Fintype I] [DecidableEq I]
variable (Pcluster : ClusterAssignment Bv I)
variable (Gdegree : SimpleGraph Bv) [DecidableRel Gdegree.Adj]
variable (threshold quota : ℕ)
variable (R : SimpleGraph I) [DecidableRel R.Adj]
variable (miss : ℕ)
variable
  (Q : RichClaim61Certificate Pcluster Gdegree threshold quota R
    (largeClustersAtLeast Pcluster Gdegree threshold quota) miss)

abbrev Edge := MatchingEdge Q.claim67.M
abbrev RootSlot := ZhaoClaim615HierarchicalSourceLayout.RootSlot (Edge Q)
abbrev Pool := ZhaoClaim615HierarchicalSourceLayout.PhysicalPool (Edge Q)

/-! ## Literal whole and raw slots -/

/-- The original cluster underlying a distinguished `A₀`/`B₀` slot. -/
def distinguishedCluster (side : Fin 2) : I :=
  if side = 0 then Q.A else Q.B

/-- The exact rich-cluster reserve underlying a distinguished slot. -/
def rootReserve (side : Fin 2) : Finset Bv :=
  if side = 0 then Q.A₀ else Q.B₀

/-- Delete precisely the two exact-size rich-cluster reserves. -/
def removeRootReserves (X : Finset Bv) : Finset Bv :=
  X \ (Q.A₀ ∪ Q.B₀)

/-- The whole host cluster represented by a Lemma-6.15 root slot. -/
def slotWhole : RootSlot Q → Finset Bv
  | Sum.inl side => clusterVertices Pcluster (distinguishedCluster Q side)
  | Sum.inr (e, side) =>
      padCluster (clusterVertices Pcluster)
        (matchingEdgeEndpoint e.1 side)

/-- The actual raw candidate represented by a Lemma-6.15 root slot.
Matching-side candidates exclude both exact distinguished reserves. -/
def slotRaw : RootSlot Q → Finset Bv
  | Sum.inl side => rootReserve Q side
  | Sum.inr (e, side) =>
      removeRootReserves Q
        (padCluster (clusterVertices Pcluster)
          (matchingEdgeEndpoint e.1 side))

theorem removeRootReserves_subset (X : Finset Bv) :
    removeRootReserves Q X ⊆ X :=
  Finset.sdiff_subset

theorem A₀_disjoint_removeRootReserves (X : Finset Bv) :
    Disjoint Q.A₀ (removeRootReserves Q X) := by
  rw [Finset.disjoint_left]
  intro z hz hzX
  exact (Finset.mem_sdiff.mp hzX).2 (Finset.mem_union_left _ hz)

theorem B₀_disjoint_removeRootReserves (X : Finset Bv) :
    Disjoint Q.B₀ (removeRootReserves Q X) := by
  rw [Finset.disjoint_left]
  intro z hz hzX
  exact (Finset.mem_sdiff.mp hzX).2 (Finset.mem_union_right _ hz)

theorem A₀_disjoint_B₀ : Disjoint Q.A₀ Q.B₀ := by
  exact (clusterVertices_disjoint Pcluster Q.adj.ne).mono
    Q.A₀_subset Q.B₀_subset

theorem rootReserves_card_le : (Q.A₀ ∪ Q.B₀).card ≤ 2 * quota := by
  calc
    (Q.A₀ ∪ Q.B₀).card ≤ Q.A₀.card + Q.B₀.card :=
      Finset.card_union_le _ _
    _ = 2 * quota := by rw [Q.A₀_card, Q.B₀_card]; omega

/-- Removing the two exact reserves costs at most `2 * quota` vertices. -/
theorem card_le_removeRootReserves_card_add (X : Finset Bv) :
    X.card ≤ (removeRootReserves Q X).card + 2 * quota := by
  have hsplit := Finset.card_sdiff_add_card_inter X (Q.A₀ ∪ Q.B₀)
  calc
    X.card = (removeRootReserves Q X).card + (X ∩ (Q.A₀ ∪ Q.B₀)).card := by
      simpa [removeRootReserves] using hsplit.symm
    _ ≤ (removeRootReserves Q X).card + (Q.A₀ ∪ Q.B₀).card :=
      Nat.add_le_add_left
        (Finset.card_le_card Finset.inter_subset_right) _
    _ ≤ (removeRootReserves Q X).card + 2 * quota :=
      Nat.add_le_add_left (rootReserves_card_le Q) _

theorem slotRaw_subset_slotWhole (slot : RootSlot Q) :
    slotRaw Pcluster Q slot ⊆ slotWhole Pcluster Q slot := by
  rcases slot with side | edgeSide
  · fin_cases side
    · simpa [slotRaw, slotWhole, rootReserve, distinguishedCluster]
        using Q.A₀_subset
    · simpa [slotRaw, slotWhole, rootReserve, distinguishedCluster]
        using Q.B₀_subset
  · rcases edgeSide with ⟨e, side⟩
    exact removeRootReserves_subset Q _

@[simp] theorem slotRaw_reserve_card (side : Fin 2) :
    (slotRaw Pcluster Q (Sum.inl side)).card = quota := by
  fin_cases side
  · simpa [slotRaw, rootReserve] using Q.A₀_card
  · simpa [slotRaw, rootReserve] using Q.B₀_card

/-- Every matching root slot retains the whole endpoint cluster except for
at most the two exact root reserves. -/
theorem slotWhole_card_le_slotRaw_card_add
    (e : Edge Q) (side : Fin 2) :
    (slotWhole Pcluster Q (Sum.inr (e, side))).card ≤
      (slotRaw Pcluster Q (Sum.inr (e, side))).card + 2 * quota := by
  simpa [slotWhole, slotRaw] using card_le_removeRootReserves_card_add Q
    (padCluster (clusterVertices Pcluster)
      (matchingEdgeEndpoint e.1 side))

/-! ## Slot and physical-pool separation -/

/-- Distinct raw root slots are disjoint.  In particular, the two oriented
sides of one matching edge are distinct clusters because the original
Claim-6.7 subgraph is a matching. -/
theorem slotRaw_disjoint_of_ne
    (x y : RootSlot Q) (hxy : x ≠ y) :
    Disjoint (slotRaw Pcluster Q x) (slotRaw Pcluster Q y) := by
  rcases x with sx | edgeX
  · rcases y with sy | edgeY
    · fin_cases sx <;> fin_cases sy
      · exact False.elim (hxy rfl)
      · simpa [slotRaw, rootReserve] using A₀_disjoint_B₀ Pcluster Q
      · simpa [slotRaw, rootReserve] using (A₀_disjoint_B₀ Pcluster Q).symm
      · exact False.elim (hxy rfl)
    · rcases edgeY with ⟨e, side⟩
      fin_cases sx
      · simpa [slotRaw, rootReserve] using A₀_disjoint_removeRootReserves Q
          (padCluster (clusterVertices Pcluster)
            (matchingEdgeEndpoint e.1 side))
      · simpa [slotRaw, rootReserve] using B₀_disjoint_removeRootReserves Q
          (padCluster (clusterVertices Pcluster)
            (matchingEdgeEndpoint e.1 side))
  · rcases y with sy | edgeY
    · exact (slotRaw_disjoint_of_ne Pcluster Q
        (Sum.inl sy) (Sum.inr edgeX) (Ne.symm hxy)).symm
    · rcases edgeX with ⟨e, side⟩
      rcases edgeY with ⟨f, other⟩
      have hpair : (e, side) ≠ (f, other) := by
        intro h
        exact hxy (congrArg Sum.inr h)
      have hendpoint : matchingEdgeEndpoint e.1 side ≠
          matchingEdgeEndpoint f.1 other := by
        intro h
        have hp := matchingEdgeEndpoint_original_injective
          Q.claim67.M Q.claim67.isMatching h
        exact hpair hp
      have hwhole : Disjoint
          (padCluster (clusterVertices Pcluster)
            (matchingEdgeEndpoint e.1 side))
          (padCluster (clusterVertices Pcluster)
            (matchingEdgeEndpoint f.1 other)) := by
        simpa only [clusterVertices_padAssignment] using
          clusterVertices_disjoint (padAssignment Pcluster) hendpoint
      exact hwhole.mono Finset.sdiff_subset Finset.sdiff_subset

/-- Coarse physical-pool separation is an immediate consequence. -/
theorem slotRaw_disjoint_of_pool_ne
    (x y : RootSlot Q)
    (hpool : ZhaoClaim615HierarchicalSourceLayout.rootSlotPool x ≠
      ZhaoClaim615HierarchicalSourceLayout.rootSlotPool y) :
    Disjoint (slotRaw Pcluster Q x) (slotRaw Pcluster Q y) := by
  apply slotRaw_disjoint_of_ne Pcluster Q x y
  intro hxy
  apply hpool
  exact congrArg ZhaoClaim615HierarchicalSourceLayout.rootSlotPool hxy

#print axioms removeRootReserves_subset
#print axioms rootReserves_card_le
#print axioms slotRaw_subset_slotWhole
#print axioms slotWhole_card_le_slotRaw_card_add
#print axioms slotRaw_disjoint_of_ne
#print axioms slotRaw_disjoint_of_pool_ne

end Erdos547b.ZhaoClaim615HierarchicalHostPools
