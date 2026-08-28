import ErdosProblems.Erdos577.WeightedPaw
import ErdosProblems.Erdos577.WeightedPawClauses

/-! The complete initial weighted classification, with no later exclusion assumed. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

variable [Fintype V]

/-- Source Lemma 4.4's initial twelve alternatives and all its replacement clauses.
The six later global exclusions are deliberately not assumed or omitted. -/
theorem TriangleChain.Feasible.weighted_paw_initial {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (hn : ¬HasPacking G k) (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hheavy : 7 ≤ degreeIn G p.leaf q.support + degreeIn G (p.vertices 2) q.support +
      degreeIn G (p.vertices 3) q.support) (hleaf : 0 < degreeIn G p.leaf q.support) :
    WeightedPawBlock.FullClassification p q := by
  have hd : Disjoint p.support q.support := by
    rw [hp, hq]
    apply disjoint_left.mpr
    intro v hv hvb
    exact (mem_sdiff.mp (c.complementPartition.block_subset hb hvb)).2 hv
  exact (hc.weighted_paw_rows hcard hdeg hn p hp hb q hq hheavy hleaf).with_replacements p q hd

end Erdos577
