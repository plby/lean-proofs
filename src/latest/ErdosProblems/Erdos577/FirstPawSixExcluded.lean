import ErdosProblems.Erdos577.FirstPawSixSmallExcluded
import ErdosProblems.Erdos577.FirstPawSixWeightedExcluded
import ErdosProblems.Erdos577.FirstPawSixReduction

/-! The exact case reduction and all three contradictions complete Wang Lemma4.8. -/

namespace Erdos577

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem TriangleChain.Feasible.not_first_paw_pattern6 {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u)
    (hn : ¬HasPacking G k) (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hheavy : 9 ≤ contacts G p.support q.support) : ¬PawBlock.Pattern6 p q := by
  intro h
  have hd : Disjoint p.support q.support := by
    apply disjoint_left.mpr
    intro u hu hqu
    exact (mem_sdiff.mp (c.complementPartition.block_subset hb (hq ▸ hqu))).2 (hp ▸ hu)
  obtain ⟨d, p', q', tag, hdf, hp', hq', hd', hdiag', hrows'⟩ :=
    FirstPawSix.reduce_to_three_cases hc hcard hdeg hn p hp hb q hq hd h hheavy
  fin_cases tag
  · exact FirstPawSix.SmallCases.excluded hdf hcard hdeg hn p' hp' hq' q' rfl
      hd' hdiag' false hrows'
  · exact FirstPawSix.SmallCases.excluded hdf hcard hdeg hn p' hp' hq' q' rfl hd' hdiag' true hrows'
  · exact FirstPawSix.WeightedCase.excluded hdf hcard hdeg hn p' hp' hq' q' rfl hd' hdiag' hrows'

end Erdos577
