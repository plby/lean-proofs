/- Retaining haven control through objects anchored on distinct grid columns. -/
import ErdosProblems.Erdos73.GridSeparation

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Erdos73Infrastructure.SimpleGraph
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {g : ℕ}

def transposeGridModel (M : MinorModel (squareGrid g) G) : MinorModel (squareGrid g) G where
  branchSet := fun x => M.branchSet (x.2, x.1)
  branch_nonempty := fun x => M.branch_nonempty (x.2, x.1)
  branch_connected := fun x => M.branch_connected (x.2, x.1)
  branch_disjoint := by
    intro x y hxy
    apply M.branch_disjoint
    intro he
    exact hxy (Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he))
  adjacent := by
    intro x y hxy
    apply M.adjacent
    rcases hxy with h | h
    · exact Or.inr h
    · exact Or.inl h

def gridColumnSupport (M : MinorModel (squareGrid g) G) (c : Fin g) : Finset V :=
  gridRowSupport (transposeGridModel M) c

theorem mem_gridColumnSupport (M : MinorModel (squareGrid g) G) (c : Fin g) (v : V) :
    v ∈ gridColumnSupport M c ↔ ∃ r : Fin g, v ∈ M.branchSet (r, c) :=
  mem_gridRowSupport (transposeGridModel M) c v

theorem gridColumnSupport_pairwise_disjoint (M : MinorModel (squareGrid g) G) :
    Pairwise fun c d => Disjoint (gridColumnSupport M c) (gridColumnSupport M d) :=
  gridRowSupport_pairwise_disjoint (transposeGridModel M)

theorem gridColumnSupport_connected (M : MinorModel (squareGrid g) G) (c : Fin g) :
    (G.induce (gridColumnSupport M c : Set V)).Connected :=
  gridRowSupport_connected (transposeGridModel M) c

theorem grid_row_meets_column (M : MinorModel (squareGrid g) G) (r c : Fin g) :
    ∃ v ∈ gridRowSupport M r, v ∈ gridColumnSupport M c := by
  obtain ⟨v, hv⟩ := M.branch_nonempty (r, c)
  exact ⟨v, (mem_gridRowSupport M r v).mpr ⟨c, hv⟩,
    (mem_gridColumnSupport M c v).mpr ⟨r, hv⟩⟩

/-- Any grid column meeting the haven-small side crosses its separator:
it also meets the untouched grid row on the exclusive large side. -/
theorem NoGridRowInHavenSmallSide.column_hits_separator
    {β : Finset (Finset V)} {q : ℕ} {h : BrambleHaven G β q}
    {M : MinorModel (squareGrid g) G} (hM : NoGridRowInHavenSmallSide h M)
    {C D : Finset V} (hCD : IsVertexSeparation G C D) (hsmall : (C ∩ D).card < g)
    (hpoint : h.PointsTo C D) (c : Fin g)
    (hhit : ∃ v ∈ gridColumnSupport M c, v ∈ C) :
    ∃ v ∈ gridColumnSupport M c, v ∈ C ∩ D := by
  obtain ⟨r, hr⟩ := hM.exists_row_in_exclusive_largeSide hCD hsmall hpoint
  obtain ⟨x, hxR, hxQ⟩ := grid_row_meets_column M r c
  obtain ⟨y, hyQ, hyC⟩ := hhit
  apply Finset.not_disjoint_iff.mp
  intro hd
  rcases connected_finset_subset_side_of_disjoint_separator hCD
      (gridColumnSupport_connected M c) hd with hC | hD
  · exact (Finset.mem_sdiff.mp (hC hxQ)).2 (Finset.mem_sdiff.mp (hr hxR)).1
  · exact (Finset.mem_sdiff.mp (hD hyQ)).2 hyC

theorem NoGridRowInHavenSmallSide.card_columns_meeting_smallSide_le
    {β : Finset (Finset V)} {q : ℕ} {h : BrambleHaven G β q}
    {M : MinorModel (squareGrid g) G} (hM : NoGridRowInHavenSmallSide h M)
    {C D : Finset V} (hCD : IsVertexSeparation G C D) (hsmall : (C ∩ D).card < g)
    (hpoint : h.PointsTo C D) (J : Finset (Fin g))
    (hhit : ∀ c ∈ J, ∃ v ∈ gridColumnSupport M c, v ∈ C) : J.card ≤ (C ∩ D).card := by
  apply card_le_of_pairwise_disjoint_hits J (gridColumnSupport M) (C ∩ D)
    (fun c _ d _ hcd => gridColumnSupport_pairwise_disjoint M hcd)
  intro c hc
  exact hM.column_hits_separator hCD hsmall hpoint c (hhit c hc)

/-- This criterion applies to a smaller wall row even after the original
grid minor branches have been shrunk to subdivision branch vertices. -/
theorem NoGridRowInHavenSmallSide.not_subset_smallSide_of_column_hits
    {β : Finset (Finset V)} {q : ℕ} {h : BrambleHaven G β q}
    {M : MinorModel (squareGrid g) G} (hM : NoGridRowInHavenSmallSide h M)
    {C D S : Finset V} {k : ℕ} (hCD : IsVertexSeparation G C D)
    (hsmall : (C ∩ D).card < g) (hk : (C ∩ D).card < k)
    (hpoint : h.PointsTo C D) (hhit : HitsColumns (gridColumnSupport M) S k) : ¬ S ⊆ C := by
  intro hSC
  obtain ⟨J, hJ, hhits⟩ := hhit
  have hbound := hM.card_columns_meeting_smallSide_le hCD hsmall hpoint J (fun c hc => by
    obtain ⟨v, hvQ, hvS⟩ := hhits c hc
    exact ⟨v, hvQ, hSC hvS⟩)
  omega

end
end Erdos73
