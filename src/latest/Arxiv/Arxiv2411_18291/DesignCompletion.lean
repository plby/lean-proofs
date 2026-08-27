import Arxiv.Arxiv2411_18291.Absorption
import Arxiv.Arxiv2411_18291.CliqueCover

/-! # Combining a packing, a reserve cover, and an absorber -/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

/-- The set algebra in the final design construction. The packing covers
the complement of the absorber and reserve except for a leave; the cover
uses only that leave and reserve edges. -/
theorem complete_of_packing_cover_absorber (hqr : r ≤ q)
    {A R B C : Hypergraph V r} (hdiv : Divisible q (complete V r))
    (habs : IsAbsorber q A R)
    (hB : HasDecomposition q B) (hC : HasDecomposition q C)
    (hBG : B ⊆ complete V r \ (A ∪ R))
    (hLC : (complete V r \ (A ∪ R)) \ B ⊆ C)
    (hCL : C ⊆ ((complete V r \ (A ∪ R)) \ B) ∪ R) :
    HasDecomposition q (complete V r) := by
  have hBC : Disjoint B C := by
    apply disjoint_left.mpr
    intro e heB heC
    rcases mem_union.mp (hCL heC) with heL | heR
    · exact (mem_sdiff.mp heL).2 heB
    · exact (mem_sdiff.mp (hBG heB)).2 (mem_union_right _ heR)
  apply complete_of_absorber hqr hdiv habs (hB.union hqr hC hBC)
  · intro e he
    refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
    intro heA
    rcases mem_union.mp he with heB | heC
    · exact (mem_sdiff.mp (hBG heB)).2 (mem_union_left _ heA)
    · rcases mem_union.mp (hCL heC) with heL | heR
      · exact (mem_sdiff.mp (mem_sdiff.mp heL).1).2 (mem_union_left _ heA)
      · exact disjoint_left.mp habs.1 heA heR
  · intro e he
    obtain ⟨heCA, heBC⟩ := mem_sdiff.mp he
    by_contra heR
    have heG : e ∈ complete V r \ (A ∪ R) := by
      refine mem_sdiff.mpr ⟨(mem_sdiff.mp heCA).1, ?_⟩
      simpa only [mem_union, not_or] using ⟨(mem_sdiff.mp heCA).2, heR⟩
    have heL := mem_sdiff.mpr ⟨heG, fun heB => heBC (mem_union_left _ heB)⟩
    exact heBC (mem_union_right _ (hLC heL))

end Arxiv2411_18291
