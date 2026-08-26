/- Positive row-orientation characterization for a haven-controlled grid. -/
import ErdosProblems.Erdos73.ControlledGrid

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Erdos73Infrastructure.SimpleGraph
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {g : ℕ}

theorem minorSupport_disjoint {W : Type*} {H : SimpleGraph W}
    (M : MinorModel H G) {S T : Finset W} (hST : Disjoint S T) :
    Disjoint (minorSupport M S) (minorSupport M T) := by
  rw [Finset.disjoint_left]
  intro v hvS hvT
  obtain ⟨s, hs, hvs⟩ := (mem_minorSupport M S v).mp hvS
  obtain ⟨t, ht, hvt⟩ := (mem_minorSupport M T v).mp hvT
  have hst : s ≠ t := fun h => Finset.disjoint_left.mp hST hs (h ▸ ht)
  exact Finset.disjoint_left.mp (M.branch_disjoint hst) hvs hvt

theorem gridRowSupport_pairwise_disjoint (M : MinorModel (squareGrid g) G) :
    Pairwise fun r s => Disjoint (gridRowSupport M r) (gridRowSupport M s) := by
  intro r s hrs
  rw [gridRowSupport_eq_minorSupport, gridRowSupport_eq_minorSupport]
  apply minorSupport_disjoint
  rw [Finset.disjoint_left]
  intro x hxr hxs
  exact hrs ((mem_productRow.mp hxr).symm.trans (mem_productRow.mp hxs))

theorem gridRowSupport_connected (M : MinorModel (squareGrid g) G) (r : Fin g) :
    (G.induce (gridRowSupport M r : Set V)).Connected := by
  have : Nonempty (Fin g) := ⟨r⟩
  rw [gridRowSupport_eq_minorSupport]
  exact M.connected_induce_branchUnion _
    (productRow_connected (SimpleGraph.pathGraph g) (SimpleGraph.pathGraph g)
      ⟨SimpleGraph.pathGraph_preconnected g⟩ r)

theorem exists_gridRowSupport_disjoint (M : MinorModel (squareGrid g) G)
    (S : Finset V) (hS : S.card < g) :
    ∃ r : Fin g, Disjoint (gridRowSupport M r) S := by
  by_contra hno
  have hbound := card_le_of_pairwise_disjoint_hits Finset.univ (gridRowSupport M) S
    (fun r _ s _ hrs => gridRowSupport_pairwise_disjoint M hrs)
    (fun r _ => Finset.not_disjoint_iff.mp (fun h => hno ⟨r, h⟩))
  rw [Finset.card_univ, Fintype.card_fin] at hbound
  omega

theorem BrambleHaven.pointsTo_or {β : Finset (Finset V)} {q : ℕ}
    (h : BrambleHaven G β q) {C D : Finset V}
    (hCD : IsVertexSeparation G C D) (hsmall : (C ∩ D).card < q) :
    h.PointsTo C D ∨ h.PointsTo D C := by
  rcases connected_finset_subset_side_of_disjoint_separator hCD
      (h.connected ⟨C ∩ D, hsmall⟩) (h.avoids ⟨C ∩ D, hsmall⟩) with hC | hD
  · right
    refine ⟨by rw [Finset.inter_comm]; exact hsmall, ?_⟩
    simpa only [Finset.inter_comm D C] using hC.trans Finset.sdiff_subset
  · exact Or.inl ⟨hsmall, hD.trans Finset.sdiff_subset⟩

theorem NoGridRowInHavenSmallSide.exists_row_in_exclusive_largeSide
    {β : Finset (Finset V)} {q : ℕ} {h : BrambleHaven G β q}
    {M : MinorModel (squareGrid g) G} (hM : NoGridRowInHavenSmallSide h M)
    {C D : Finset V} (hCD : IsVertexSeparation G C D) (hsmall : (C ∩ D).card < g)
    (hpoint : h.PointsTo C D) : ∃ r : Fin g, gridRowSupport M r ⊆ D \ C := by
  obtain ⟨r, hr⟩ := exists_gridRowSupport_disjoint M (C ∩ D) hsmall
  rcases connected_finset_subset_side_of_disjoint_separator hCD
      (gridRowSupport_connected M r) hr with hC | hD
  · exact (hM C D hCD hsmall hpoint r (hC.trans Finset.sdiff_subset)).elim
  · exact ⟨r, hD⟩

theorem NoGridRowInHavenSmallSide.pointsTo_iff_contains_row
    {β : Finset (Finset V)} {q : ℕ} {h : BrambleHaven G β q}
    {M : MinorModel (squareGrid g) G} (hM : NoGridRowInHavenSmallSide h M) (hgq : g ≤ q)
    {C D : Finset V} (hCD : IsVertexSeparation G C D) (hsmall : (C ∩ D).card < g) :
    h.PointsTo C D ↔ ∃ r : Fin g, gridRowSupport M r ⊆ D := by
  constructor
  · intro hp
    obtain ⟨r, hr⟩ := hM.exists_row_in_exclusive_largeSide hCD hsmall hp
    exact ⟨r, hr.trans Finset.sdiff_subset⟩
  · rintro ⟨r, hr⟩
    rcases h.pointsTo_or hCD (hsmall.trans_le hgq) with hp | hp
    · exact hp
    · exact (hM D C hCD.flip (by rw [Finset.inter_comm]; exact hsmall) hp r hr).elim

end
end Erdos73
