/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim61RichFull
import ErdosProblems.Erdos547b.Claim616
import ErdosProblems.Erdos547b.Claim615CoordinateSourceAllocation

/-!
# Literal coordinate host pools for Zhao Lemma 6.15

The two distinguished slots are the exact rich reserves `A₀` and `B₀`.
Every matching-side slot is a literal endpoint cluster with both reserves
removed.  Since the coordinate online backend uses the slot itself as its
physical pool, distinct matching endpoints remain distinct even on the same
matching edge.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim615HierarchicalCoordinateHostPools

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoSection6Dichotomy
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim615CoordinateSourceAllocation

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
abbrev RootSlot :=
  ZhaoClaim615CoordinateSourceAllocation.RootSlot
    (Edge Pcluster Gdegree threshold quota R miss Q)

def slotWhole : RootSlot Pcluster Gdegree threshold quota R miss Q → Finset Bv
  | Sum.inl side =>
      clusterVertices Pcluster (if side = 0 then Q.A else Q.B)
  | Sum.inr (e, side) =>
      padCluster (clusterVertices Pcluster) (matchingEdgeEndpoint e.1 side)

def slotRaw : RootSlot Pcluster Gdegree threshold quota R miss Q → Finset Bv
  | Sum.inl side => if side = 0 then Q.A₀ else Q.B₀
  | Sum.inr (e, side) =>
      padCluster (clusterVertices Pcluster) (matchingEdgeEndpoint e.1 side) \
        (Q.A₀ ∪ Q.B₀)

theorem removeRootReserves_subset (X : Finset Bv) :
    X \ (Q.A₀ ∪ Q.B₀) ⊆ X :=
  Finset.sdiff_subset

theorem A₀_disjoint_removeRootReserves (X : Finset Bv) :
    Disjoint Q.A₀ (X \ (Q.A₀ ∪ Q.B₀)) := by
  rw [Finset.disjoint_left]
  intro z hz hzX
  exact (Finset.mem_sdiff.mp hzX).2 (Finset.mem_union_left _ hz)

theorem B₀_disjoint_removeRootReserves (X : Finset Bv) :
    Disjoint Q.B₀ (X \ (Q.A₀ ∪ Q.B₀)) := by
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

theorem card_le_removeRootReserves_card_add (X : Finset Bv) :
    X.card ≤ (X \ (Q.A₀ ∪ Q.B₀)).card + 2 * quota := by
  have hsplit := Finset.card_sdiff_add_card_inter X (Q.A₀ ∪ Q.B₀)
  calc
    X.card = (X \ (Q.A₀ ∪ Q.B₀)).card +
        (X ∩ (Q.A₀ ∪ Q.B₀)).card := hsplit.symm
    _ ≤
        (X \ (Q.A₀ ∪ Q.B₀)).card +
          (Q.A₀ ∪ Q.B₀).card :=
      Nat.add_le_add_left
        (Finset.card_le_card Finset.inter_subset_right) _
    _ ≤
        (X \ (Q.A₀ ∪ Q.B₀)).card + 2 * quota :=
      Nat.add_le_add_left
        (rootReserves_card_le Pcluster Gdegree threshold quota R miss Q) _

theorem slotRaw_subset_slotWhole
    (slot : RootSlot Pcluster Gdegree threshold quota R miss Q) :
    slotRaw Pcluster Gdegree threshold quota R miss Q slot ⊆
      slotWhole Pcluster Gdegree threshold quota R miss Q slot := by
  rcases slot with side | edgeSide
  · fin_cases side
    · simpa [slotRaw, slotWhole]
        using Q.A₀_subset
    · simpa [slotRaw, slotWhole]
        using Q.B₀_subset
  · rcases edgeSide with ⟨e, side⟩
    exact Finset.sdiff_subset

@[simp] theorem slotRaw_reserve_card (side : Fin 2) :
    (slotRaw Pcluster Gdegree threshold quota R miss Q
      (Sum.inl side)).card = quota := by
  fin_cases side
  · simpa [slotRaw] using Q.A₀_card
  · simpa [slotRaw] using Q.B₀_card

theorem slotWhole_card_le_slotRaw_card_add
    (e : Edge Pcluster Gdegree threshold quota R miss Q) (side : Fin 2) :
    (slotWhole Pcluster Gdegree threshold quota R miss Q
      (Sum.inr (e, side))).card ≤
      (slotRaw Pcluster Gdegree threshold quota R miss Q
        (Sum.inr (e, side))).card +
        2 * quota := by
  simpa [slotWhole, slotRaw] using
    card_le_removeRootReserves_card_add Pcluster Gdegree threshold quota R miss Q
    (padCluster (clusterVertices Pcluster) (matchingEdgeEndpoint e.1 side))

private theorem matchingEndpoint_injective :
    Function.Injective (fun ec :
      Edge Pcluster Gdegree threshold quota R miss Q × Fin 2 ↦
      matchingEdgeEndpoint ec.1.1 ec.2) := by
  rintro ⟨e, c⟩ ⟨f, d⟩ hendpoint
  let flip : Fin 2 → Fin 2 := fun q ↦ if q = 0 then 1 else 0
  have horiented
      (g : Edge Pcluster Gdegree threshold quota R miss Q) (q : Fin 2) :
      orientedEndpoint Q.claim67.M ∅ g (flip q) =
        matchingEdgeEndpoint g.1 q := by
    fin_cases q <;>
      simp [flip, orientedEndpoint, rawEndpoint, matchingEdgeEndpoint]
  have hpair : (e, flip c) = (f, flip d) := by
    apply orientedEndpoint_injective Q.claim67.M Q.claim67.isMatching
      (∅ : Finset (EvenPadding I))
    change orientedEndpoint Q.claim67.M ∅ e (flip c) =
      orientedEndpoint Q.claim67.M ∅ f (flip d)
    simpa only [horiented] using hendpoint
  have hedge : e = f := congrArg Prod.fst hpair
  subst f
  have hside : c = d := by
    have hflip := congrArg Prod.snd hpair
    fin_cases c <;> fin_cases d <;> simp [flip] at hflip ⊢
  subst d
  rfl

/-- Distinct literal coordinate slots have disjoint raw candidates. -/
theorem slotRaw_disjoint_of_ne
    (x y : RootSlot Pcluster Gdegree threshold quota R miss Q) (hxy : x ≠ y) :
    Disjoint (slotRaw Pcluster Gdegree threshold quota R miss Q x)
      (slotRaw Pcluster Gdegree threshold quota R miss Q y) := by
  rcases x with sx | edgeX
  · rcases y with sy | edgeY
    · fin_cases sx <;> fin_cases sy
      · exact False.elim (hxy rfl)
      · simpa [slotRaw] using
          A₀_disjoint_B₀ Pcluster Gdegree threshold quota R miss Q
      · simpa [slotRaw] using
          (A₀_disjoint_B₀ Pcluster Gdegree threshold quota R miss Q).symm
      · exact False.elim (hxy rfl)
    · rcases edgeY with ⟨e, side⟩
      fin_cases sx
      · simpa [slotRaw] using
          A₀_disjoint_removeRootReserves Pcluster Gdegree threshold quota R
            miss Q
          (padCluster (clusterVertices Pcluster) (matchingEdgeEndpoint e.1 side))
      · simpa [slotRaw] using
          B₀_disjoint_removeRootReserves Pcluster Gdegree threshold quota R
            miss Q
          (padCluster (clusterVertices Pcluster) (matchingEdgeEndpoint e.1 side))
  · rcases y with sy | edgeY
    · rcases edgeX with ⟨e, side⟩
      fin_cases sy
      · simpa [slotRaw] using
          (A₀_disjoint_removeRootReserves Pcluster Gdegree threshold quota R
            miss Q
            (padCluster (clusterVertices Pcluster)
              (matchingEdgeEndpoint e.1 side))).symm
      · simpa [slotRaw] using
          (B₀_disjoint_removeRootReserves Pcluster Gdegree threshold quota R
            miss Q
            (padCluster (clusterVertices Pcluster)
              (matchingEdgeEndpoint e.1 side))).symm
    · rcases edgeX with ⟨e, side⟩
      rcases edgeY with ⟨f, other⟩
      have hpair : (e, side) ≠ (f, other) := by
        intro h
        exact hxy (congrArg Sum.inr h)
      have hendpoint : matchingEdgeEndpoint e.1 side ≠
          matchingEdgeEndpoint f.1 other := by
        intro h
        exact hpair
          (matchingEndpoint_injective Pcluster Gdegree threshold quota R miss Q h)
      have hwhole : Disjoint
          (padCluster (clusterVertices Pcluster)
            (matchingEdgeEndpoint e.1 side))
          (padCluster (clusterVertices Pcluster)
            (matchingEdgeEndpoint f.1 other)) := by
        simpa only [clusterVertices_padAssignment] using
          clusterVertices_disjoint (padAssignment Pcluster) hendpoint
      exact hwhole.mono Finset.sdiff_subset Finset.sdiff_subset

end Erdos547b.ZhaoClaim615HierarchicalCoordinateHostPools

#print axioms Erdos547b.ZhaoClaim615HierarchicalCoordinateHostPools.slotRaw_disjoint_of_ne
