import ErdosProblems.Erdos577.WeightedPawFinite0
import ErdosProblems.Erdos577.WeightedPawFinite1
import ErdosProblems.Erdos577.WeightedPawFinite2
import ErdosProblems.Erdos577.WeightedPawFinite3
import ErdosProblems.Erdos577.WeightedPawPatterns
import ErdosProblems.Erdos577.PawNineTransport

/-! The initial weighted classification in every feasible chain, retaining patterns (9)–(20). -/

namespace Erdos577

open Finset

namespace WeightedPaw

theorem finite_classification (diagonal : Fin 4) (m : Fin 65536)
    (hl : 1 ≤ DenseOutside.terminalCount m.val)
    (hh : 7 + PawNine.rowCount m.val 1 ≤ PathExchange.crossCount m.val) :
    FirstPaw.Positive diagonal m.val ∨ Classified diagonal m.val := by
  fin_cases diagonal
  · exact D0.finite_classification m hl hh
  · exact D1.finite_classification m hl hh
  · exact D2.finite_classification m hl hh
  · exact D3.finite_classification m hl hh

end WeightedPaw

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem TriangleChain.Feasible.weighted_paw_rows {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (hn : ¬HasPacking G k) (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hheavy : 7 ≤ degreeIn G p.leaf q.support + degreeIn G (p.vertices 2) q.support +
      degreeIn G (p.vertices 3) q.support) (hleaf : 0 < degreeIn G p.leaf q.support) :
    WeightedPawBlock.Classified p q := by
  have hh : 7 + PawNine.rowCount (PawEncoding.encoded p q).val 1 ≤
      PathExchange.crossCount (PawEncoding.encoded p q).val := by
    rw [PawNine.rowCount_encoded, PawEncoding.crossCount_encoded,
      p.contacts_support, p.contacts_triangle]
    omega
  have hf := WeightedPaw.finite_classification (Unattached.diagonal q) (PawEncoding.encoded p q)
    (by rw [PawEncoding.terminalCount_encoded]; omega) hh
  rcases hf with hpos | hrows
  · exact False.elim (FirstPaw.positive_excluded hc hcard hdeg hn p hp hb q hq hpos)
  · exact hrows.transport p q

end Erdos577
