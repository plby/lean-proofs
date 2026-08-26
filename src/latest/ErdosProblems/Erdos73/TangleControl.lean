/- Root independence and connected-column counting for controlled extraction. -/
import ErdosProblems.Erdos73.OrdinaryGrid

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Erdos73Infrastructure.SimpleGraph
variable {V : Type*} [Fintype V] {G : SimpleGraph V}
variable {β : Finset (Finset V)} {q : ℕ}

theorem BrambleHaven.pointsTo_join (h : BrambleHaven G β q)
    {A B C D : Finset V} (hAB : IsVertexSeparation G A B) (hCD : IsVertexSeparation G C D)
    (hpAB : h.PointsTo A B) (hpCD : h.PointsTo C D)
    (hunion : ((A ∩ B) ∪ (C ∩ D)).card < q)
    (hsmall : ((A ∪ C) ∩ (B ∩ D)).card < q) : h.PointsTo (A ∪ C) (B ∩ D) := by
  obtain ⟨hABsmall, hABregion⟩ := hpAB
  obtain ⟨hCDsmall, hCDregion⟩ := hpCD
  let U : {S : Finset V // S.card < q} := ⟨(A ∩ B) ∪ (C ∩ D), hunion⟩
  have hUA : h.region U ⊆ B \ A :=
    (h.antitone ⟨A ∩ B, hABsmall⟩ U Finset.subset_union_left).trans
      (h.pointsTo_exclusive hABregion)
  have hUC : h.region U ⊆ D \ C :=
    (h.antitone ⟨C ∩ D, hCDsmall⟩ U Finset.subset_union_right).trans
      (h.pointsTo_exclusive hCDregion)
  have hright : h.region U ⊆ (B ∩ D) \ (A ∪ C) := by
    intro v hv
    obtain ⟨hvB, hvA⟩ := Finset.mem_sdiff.mp (hUA hv)
    obtain ⟨hvD, hvC⟩ := Finset.mem_sdiff.mp (hUC hv)
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hvB, hvD⟩,
      fun h => (Finset.mem_union.mp h).elim hvA hvC⟩
  exact h.pointsTo_of_touches_right (hAB.join hCD) hsmall hright
    (h.touches ⟨(A ∪ C) ∩ (B ∩ D), hsmall⟩ U)

/-- A forward-minimal boundary has at most separator-order many roots
in any haven-small side, while the union-of-separators bound is available. -/
theorem BrambleHaven.boundary_smallSide_card_le (h : BrambleHaven G β q)
    {A B C D : Finset V} (hAB : IsVertexSeparation G A B) (hCD : IsVertexSeparation G C D)
    (hpAB : h.PointsTo A B) (hpCD : h.PointsTo C D) (hmin : h.ForwardMinimal A B)
    (hsize : (A ∩ B).card + (C ∩ D).card < q) :
    ((A ∩ B) ∩ C).card ≤ (C ∩ D).card := by
  by_contra hnot
  have hsub : (A ∪ C) ∩ (B ∩ D) ⊆ ((A ∩ B) \ C) ∪ (C ∩ D) := by
    intro v hv
    obtain ⟨hvAC, hvBD⟩ := Finset.mem_inter.mp hv
    obtain ⟨hvB, hvD⟩ := Finset.mem_inter.mp hvBD
    by_cases hvC : v ∈ C
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hvC, hvD⟩)
    · have hvA := (Finset.mem_union.mp hvAC).resolve_right hvC
      exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hvA, hvB⟩, hvC⟩)
  have hbound := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hsplit := Finset.card_sdiff_add_card_inter (A ∩ B) C
  have hlt : ((A ∪ C) ∩ (B ∩ D)).card < (A ∩ B).card := by omega
  have hpoint := h.pointsTo_join hAB hCD hpAB hpCD
    ((Finset.card_union_le _ _).trans_lt hsize) (hlt.trans hpAB.choose)
  exact hlt.not_ge (hmin _ _ (hAB.join hCD) Finset.subset_union_left Finset.inter_subset_left hpoint)

/-- A separated small side can meet only as many disjoint rooted connected
sets as the separator and its contained roots can account for. -/
theorem card_connected_columns_meeting_side_le {I : Type*}
    (indices : Finset I) (Q : I → Finset V) (Z : Finset V)
    (hconn : ∀ i ∈ indices, (G.induce (Q i : Set V)).Connected)
    (hdisj : (indices : Set I).Pairwise fun i j => Disjoint (Q i) (Q j))
    (hroot : ∀ i ∈ indices, ∃ v ∈ Q i, v ∈ Z)
    {C D : Finset V} (hCD : IsVertexSeparation G C D)
    (hhit : ∀ i ∈ indices, ∃ v ∈ Q i, v ∈ C) :
    indices.card ≤ (C ∩ D).card + (Z ∩ C).card := by
  let crossing := indices.filter fun i => ¬ Disjoint (Q i) (C ∩ D)
  have hcross : crossing ⊆ indices := Finset.filter_subset _ _
  have hcrosscard : crossing.card ≤ (C ∩ D).card := by
    apply card_le_of_pairwise_disjoint_hits crossing Q (C ∩ D)
      (fun i hi j hj hij => hdisj (hcross hi) (hcross hj) hij)
    intro i hi
    exact Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hi).2
  have hrestcard : (indices \ crossing).card ≤ (Z ∩ C).card := by
    apply card_le_of_pairwise_disjoint_hits (indices \ crossing) Q (Z ∩ C)
      (fun i hi j hj hij => hdisj (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hj).1 hij)
    intro i hi
    obtain ⟨hiI, hiCross⟩ := Finset.mem_sdiff.mp hi
    have havoid : Disjoint (Q i) (C ∩ D) := by
      by_contra h
      exact hiCross (Finset.mem_filter.mpr ⟨hiI, h⟩)
    have hsub : Q i ⊆ C := by
      rcases connected_finset_subset_side_of_disjoint_separator hCD (hconn i hiI) havoid
        with hC | hD
      · exact hC.trans Finset.sdiff_subset
      · obtain ⟨v, hvQ, hvC⟩ := hhit i hiI
        exact ((Finset.mem_sdiff.mp (hD hvQ)).2 hvC).elim
    obtain ⟨v, hvQ, hvZ⟩ := hroot i hiI
    exact ⟨v, hvQ, Finset.mem_inter.mpr ⟨hvZ, hsub hvQ⟩⟩
  have hsum := Finset.card_sdiff_add_card_eq_card hcross
  omega

def gridRowSupport {g : ℕ} (M : MinorModel (squareGrid g) G) (r : Fin g) : Finset V :=
  Finset.univ.biUnion fun c : Fin g => M.branchSet (r, c)

/-- The orientation criterion to be retained by the controlled extraction.
Unlike ordinary minor containment, this explicitly refers to the original haven. -/
def NoGridRowInHavenSmallSide {g : ℕ} (h : BrambleHaven G β q)
    (M : MinorModel (squareGrid g) G) : Prop :=
  ∀ C D : Finset V, IsVertexSeparation G C D → (C ∩ D).card < g →
    h.PointsTo C D → ∀ r : Fin g, ¬ gridRowSupport M r ⊆ C

/-- Rich intersections with disjoint connected root-bearing columns force
the correct low-order haven orientation for every grid row. -/
theorem noGridRowInHavenSmallSide_of_column_witnesses
    {I : Type*} {g : ℕ} (h : BrambleHaven G β q)
    {A B : Finset V} (hAB : IsVertexSeparation G A B)
    (hpoint : h.PointsTo A B) (hmin : h.ForwardMinimal A B)
    (hsize : (A ∩ B).card + g ≤ q)
    (Q : I → Finset V) (hconn : ∀ i, (G.induce (Q i : Set V)).Connected)
    (hdisj : Pairwise fun i j => Disjoint (Q i) (Q j))
    (hroot : ∀ i, ∃ v ∈ Q i, v ∈ A ∩ B)
    (M : MinorModel (squareGrid g) G)
    (hrich : ∀ r : Fin g, ∃ indices : Finset I, 2 * g ≤ indices.card ∧
      ∀ i ∈ indices, ∃ v ∈ Q i, v ∈ gridRowSupport M r) :
    NoGridRowInHavenSmallSide h M := by
  intro C D hCD hsmall hpCD r hrow
  have hroots := h.boundary_smallSide_card_le hAB hCD hpoint hpCD hmin
    (show (A ∩ B).card + (C ∩ D).card < q by omega)
  obtain ⟨indices, hcard, hhits⟩ := hrich r
  have hbound := card_connected_columns_meeting_side_le indices Q (A ∩ B)
    (fun i _ => hconn i) (fun i _ j _ hij => hdisj hij) (fun i _ => hroot i) hCD
    (fun i hi => by
      obtain ⟨v, hvQ, hvrow⟩ := hhits i hi
      exact ⟨v, hvQ, hrow hvrow⟩)
  omega

end
end Erdos73
