import StackExchange.Puzzling139335.InterfaceParity
import StackExchange.Puzzling139335.StraightBranchCount

/-!
# Intrinsic branch counts in an exact interface partition

At a junction the two incident arcs on each boundary are precisely its two
local Jordan branches.  Thus their finite straight-occurrence count is the
intrinsic count, independent of the chosen interface parametrizations.
-/

open Set

namespace Puzzling139335.ExactBoundaryArcFamily

variable {d : SquareDissection} (F : ExactBoundaryArcFamily d)

theorem endpoint_arc_between (i : ExtendedPieceIndex) (k : Fin (F.n i)) {v : Plane}
    (hv : v = F.left i k ∨ v = F.right i k) :
    ∃ u, Schoenflies.IsArcBetween (F.arc i k) v u ∧
      ({v, u} : Set Plane) = {F.left i k, F.right i k} := by
  rcases hv with rfl | rfl
  · exact ⟨F.right i k, F.arc_between i k, rfl⟩
  · exact ⟨F.left i k, (F.arc_between i k).reverse, Set.pair_comm _ _⟩

theorem hasStraightBranchCount_straightBoundaryOccurrences
    (hTwo : F.HasTwoGerms) (i : ExtendedPieceIndex) {v : Plane}
    (hv : v ∈ frontier (d.extendedPiece i) ∩ tripleContactSet d.extendedPiece) :
    HasStraightBranchCount (frontier (d.extendedPiece i)) v
      (F.straightBoundaryOccurrences i v).card := by
  classical
  obtain ⟨k, l, hkl, hvertices⟩ := Set.encard_eq_two.mp (hTwo i v hv)
  have hk : v = F.left i k ∨ v = F.right i k := by
    have : k ∈ ({k, l} : Set (Fin (F.n i))) := by simp
    rwa [← hvertices] at this
  have hl : v = F.left i l ∨ v = F.right i l := by
    have : l ∈ ({k, l} : Set (Fin (F.n i))) := by simp
    rwa [← hvertices] at this
  obtain ⟨a, hA, hAends⟩ := F.endpoint_arc_between i k hk
  obtain ⟨b, hB, _⟩ := F.endpoint_arc_between i l hl
  have hinter : F.arc i k ∩ F.arc i l ⊆ ({v, a} : Set Plane) := by
    rw [hAends]
    exact (F.meet_endpoints i k l hkl).trans inter_subset_left
  have hcount := hasStraightBranchCount_of_two_endpoint_arcs
    (d.extendedPiece_frontier_jordan i) hA hB
    (fun _ hx => (F.subset_frontiers i k hx).1)
    (fun _ hx => (F.subset_frontiers i l hx).1) hinter
  have hfilter : F.straightBoundaryOccurrences i v =
      ({k, l} : Finset (Fin (F.n i))).filter (fun j => IsStraightAt (F.arc i j) v) := by
    ext j
    simp only [F.mem_straightBoundaryOccurrences, Finset.mem_filter, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hj
      have hend : v = F.left i j ∨ v = F.right i j := by
        by_contra hnot
        exact Set.disjoint_left.mp (F.arcInterior_disjoint i j) ⟨hj.mem, hnot⟩ hv.2
      have hjpair : j ∈ ({k, l} : Set (Fin (F.n i))) := by
        rw [← hvertices]
        exact hend
      exact ⟨hjpair, hj⟩
    · exact fun hj => hj.2
  have hcard : (F.straightBoundaryOccurrences i v).card =
      straightGermIndicator (F.arc i k) v + straightGermIndicator (F.arc i l) v := by
    rw [hfilter]
    by_cases hkstraight : IsStraightAt (F.arc i k) v <;>
      by_cases hlstraight : IsStraightAt (F.arc i l) v <;>
      simp [Finset.filter_insert, Finset.filter_singleton,
        straightGermIndicator, hkstraight, hlstraight, hkl]
  rw [hcard]
  exact hcount

/-- Any intrinsically specified count agrees with the count in this actual
partition at a junction. -/
theorem card_straightBoundaryOccurrences_eq
    (hTwo : F.HasTwoGerms) (i : ExtendedPieceIndex) {v : Plane} {n : ℕ}
    (hv : v ∈ frontier (d.extendedPiece i) ∩ tripleContactSet d.extendedPiece)
    (hn : HasStraightBranchCount (frontier (d.extendedPiece i)) v n) :
    (F.straightBoundaryOccurrences i v).card = n :=
  (F.hasStraightBranchCount_straightBoundaryOccurrences hTwo i hv).unique hn

/-- A boundary not containing the point contributes no straight occurrence. -/
theorem straightBoundaryOccurrences_eq_empty_of_not_mem_frontier
    (i : ExtendedPieceIndex) {v : Plane} (hv : v ∉ frontier (d.extendedPiece i)) :
    F.straightBoundaryOccurrences i v = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro k hk
  exact hv ((F.subset_frontiers i k (F.mem_straightBoundaryOccurrences.mp hk).mem).1)

end Puzzling139335.ExactBoundaryArcFamily
