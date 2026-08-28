import ErdosProblems.Erdos577.FirstPawFourDiamond
import ErdosProblems.Erdos577.FirstPawFourLarge
import ErdosProblems.Erdos577.FirstPawFourCompleteSwap

/-! Full exclusion of pattern (4), including both possible old block scores. -/

namespace Erdos577

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem TriangleChain.Feasible.not_first_paw_pattern4 {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u)
    (hn : ¬HasPacking G k) (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hheavy : 9 ≤ contacts G p.support q.support) : ¬PawBlock.Pattern4 p q := by
  intro h
  have hd : Disjoint p.support q.support := by
    apply disjoint_left.mpr
    intro u hu hqu
    exact (mem_sdiff.mp (c.complementPartition.block_subset hb (hq ▸ hqu))).2 (hp ▸ hu)
  obtain ⟨a, ha, hab, hweight⟩ := FirstPawFour.heavy_block hcard hdeg hn p hp hb q hq hd h
  by_cases hlow : G.Adj (q 1) (q 3)
  · by_cases hlarge : 7 ≤ degreeIn G p.leaf a + degreeIn G (p.vertices 2) a +
        degreeIn G (p.vertices 3) a
    · exact FirstPawFour.large_three_false hc hcard hdeg hn p hp hb q hq hd h hheavy
        ha hab hweight hlarge
    obtain ⟨d, p', q', hdf, hp', hq', hd', hpat, hnine, hleaf, h2, h3, hq1, hq3, hkeep⟩ :=
      FirstPawFour.exists_complete_swap hc hcard hn p hp hb q hq hd h hheavy hlow
    obtain ⟨ha', haneq⟩ := hkeep a ha hab
    have hweight' : 13 ≤ FirstPawFour.weight p' q' a := by
      unfold FirstPawFour.weight at hweight ⊢
      rw [hleaf, h2, h3, hq1, hq3]
      omega
    have hlarge' : 7 ≤ degreeIn G p'.leaf a + degreeIn G (p'.vertices 2) a +
        degreeIn G (p'.vertices 3) a := by
      rw [hleaf, h2, h3]
      unfold FirstPawFour.weight at hweight
      omega
    exact FirstPawFour.large_three_false hdf hcard hdeg hn p' hp' hq' q' rfl hd' hpat hnine
      ha' haneq hweight' hlarge'
  · exact FirstPawFour.diamond_false hc hcard hdeg hn p hp hb q hq hd h hheavy hlow
      ha hab hweight

end Erdos577
