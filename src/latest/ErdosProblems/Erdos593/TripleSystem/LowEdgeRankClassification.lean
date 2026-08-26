import ErdosProblems.Erdos593.TripleSystem.LowCodegreeLayering
import ErdosProblems.Erdos593.TripleSystem.LowCrossingAtomBridge

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Rank shapes of low-pair hyperedges

The finite low-pair closure layering rules out a unique latest vertex in a
low-pair triple.  Consequently, every such triple is either contained in one
rank fibre or has exactly two equal latest vertices and one earlier vertex.
The latter alternative is recorded as an edge of the low crossing graph.
-/

namespace Erdos593

universe u v

namespace TripleSystem

/-- A displayed triple lies in one rank fibre. -/
def AllSameRank {W : Type u} {I : Type u}
    (rank : W → I) (x y z : W) : Prop :=
  rank x = rank y ∧ rank y = rank z

/-- A displayed pair has a common rank strictly above the remaining vertex. -/
def EqualTopRankPair {W : Type u} {I : Type u} [LT I]
    (rank : W → I) (x y z : W) : Prop :=
  rank x = rank y ∧ rank z < rank x

/-- A low-pair triple has no unique latest vertex.  More precisely, it is
either monochromatic with respect to the rank map, or one of its three pairs
is an equal top-rank pair. -/
theorem lowPair_rank_shape
    {W : Type u} {D : Type v} {I : Type u} [LinearOrder I]
    {H : TripleSystem W D} {t : Nat} {x y z : W}
    (L : FiniteClosureLayering 2 (lowPairClosureFinset H t) I)
    (p : ThirdVertexWitness H x y z)
    (hlow : H.lowPairEdge t p.edge) :
    AllSameRank L.rank x y z ∨
      EqualTopRankPair L.rank x y z ∨
        EqualTopRankPair L.rank x z y ∨
          EqualTopRankPair L.rank y z x := by
  have hx : H.Inc x p.edge := by
    change x ∈ H.edgeSet p.edge
    rw [p.edgeSet_eq]
    simp
  have hy : H.Inc y p.edge := by
    change y ∈ H.edgeSet p.edge
    rw [p.edgeSet_eq]
    simp
  have hz : H.Inc z p.edge := by
    change z ∈ H.edgeSet p.edge
    rw [p.edgeSet_eq]
    simp
  have hnot_xy : ¬ HighPair H t x y :=
    H.not_highPair_of_lowPairEdge hlow hx hy
  have hnot_xz : ¬ HighPair H t x z :=
    H.not_highPair_of_lowPairEdge hlow hx hz
  have hnot_yz : ¬ HighPair H t y z :=
    H.not_highPair_of_lowPairEdge hlow hy hz
  have hnot_top_z : ¬ (L.rank x < L.rank z ∧ L.rank y < L.rank z) :=
    not_both_rank_lt_of_thirdVertexWitness_of_not_highPair L p hnot_xy
  have hnot_top_y : ¬ (L.rank x < L.rank y ∧ L.rank z < L.rank y) :=
    not_both_rank_lt_of_thirdVertexWitness_of_not_highPair L p.rotate hnot_xz
  have hnot_top_x : ¬ (L.rank y < L.rank x ∧ L.rank z < L.rank x) :=
    not_both_rank_lt_of_thirdVertexWitness_of_not_highPair L p.swap.rotate hnot_yz
  rcases lt_trichotomy (L.rank x) (L.rank y) with hrxy | hrxy | hryx
  · rcases lt_trichotomy (L.rank z) (L.rank y) with hrzy | hrzy | hryz
    · exact False.elim (hnot_top_y ⟨hrxy, hrzy⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨hrzy.symm, hrxy⟩))
    · exact False.elim (hnot_top_z ⟨lt_trans hrxy hryz, hryz⟩)
  · rcases lt_trichotomy (L.rank z) (L.rank x) with hrzx | hrzx | hrxz
    · exact Or.inr (Or.inl ⟨hrxy, hrzx⟩)
    · exact Or.inl ⟨hrxy, hrxy.symm.trans hrzx.symm⟩
    · exact False.elim
        (hnot_top_z ⟨hrxz, by simpa [hrxy] using! hrxz⟩)
  · rcases lt_trichotomy (L.rank z) (L.rank x) with hrzx | hrzx | hrxz
    · exact False.elim (hnot_top_x ⟨hryx, hrzx⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hrzx.symm, hryx⟩))
    · exact False.elim (hnot_top_z ⟨hrxz, lt_trans hryx hrxz⟩)

/-- The non-monochromatic alternatives of `lowPair_rank_shape` are precisely
edges of the low crossing graph, with the equal top-rank pair as endpoints. -/
theorem lowPair_rank_shape_or_lowCrossingAdj
    {W : Type u} {D : Type v} {I : Type u} [LinearOrder I]
    {H : TripleSystem W D} {t : Nat} {x y z : W}
    (L : FiniteClosureLayering 2 (lowPairClosureFinset H t) I)
    (p : ThirdVertexWitness H x y z)
    (hlow : H.lowPairEdge t p.edge) :
    AllSameRank L.rank x y z ∨
      (lowCrossingGraph H L.rank t).Adj x y ∨
        (lowCrossingGraph H L.rank t).Adj x z ∨
          (lowCrossingGraph H L.rank t).Adj y z := by
  rcases lowPair_rank_shape L p hlow with hall | hxy | hxz | hyz
  · exact Or.inl hall
  · refine Or.inr (Or.inl ?_)
    exact (lowCrossingGraph_adj H L.rank t x y).mpr
      ⟨z, hxy.2, hxy.1, p, hlow⟩
  · refine Or.inr (Or.inr (Or.inl ?_))
    apply (lowCrossingGraph_adj H L.rank t x z).mpr
    refine ⟨y, hxz.2, hxz.1, p.rotate, ?_⟩
    exact hlow
  · refine Or.inr (Or.inr (Or.inr ?_))
    apply (lowCrossingGraph_adj H L.rank t y z).mpr
    refine ⟨x, hyz.2, hyz.1, p.swap.rotate, ?_⟩
    exact hlow

/-- Every low-pair host edge admits a displayed three-vertex form to which
the rank classification applies.  Thus it is entirely contained in one rank
fibre or supplies an edge of the low crossing graph. -/
theorem exists_lowPair_rank_shape_or_lowCrossingAdj
    {W : Type u} {D : Type v} {I : Type u} [LinearOrder I]
    {H : TripleSystem W D} {t : Nat} {e : D}
    (L : FiniteClosureLayering 2 (lowPairClosureFinset H t) I)
    (hlow : H.lowPairEdge t e) :
    ∃ x y z : W, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      H.edgeSet e = {x, y, z} ∧
        (AllSameRank L.rank x y z ∨
          (lowCrossingGraph H L.rank t).Adj x y ∨
            (lowCrossingGraph H L.rank t).Adj x z ∨
              (lowCrossingGraph H L.rank t).Adj y z) := by
  obtain ⟨x, y, z, hxy, hxz, hyz, hedge⟩ :=
    Set.ncard_eq_three.mp (H.edgeSet_ncard e)
  let p : ThirdVertexWitness H x y z := ⟨e, hedge⟩
  have hlow' : H.lowPairEdge t p.edge := by
    simpa [p] using! hlow
  refine ⟨x, y, z, hxy, hxz, hyz, hedge, ?_⟩
  exact lowPair_rank_shape_or_lowCrossingAdj L p hlow'

end TripleSystem

end Erdos593
