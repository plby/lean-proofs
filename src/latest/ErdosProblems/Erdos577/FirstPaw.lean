import ErdosProblems.Erdos577.FirstPawFinite0
import ErdosProblems.Erdos577.FirstPawFinite1
import ErdosProblems.Erdos577.FirstPawFinite2
import ErdosProblems.Erdos577.FirstPawFinite3
import ErdosProblems.Erdos577.FirstPawPatterns

/-! The row-classification part of Wang's first paw-block lemma in every feasible chain. -/

namespace Erdos577

open Finset

namespace FirstPaw

theorem finite_classification (diagonal : Fin 4) (m : Fin 65536)
    (hl : 1 ≤ DenseOutside.terminalCount m.val) (hh : 9 ≤ PathExchange.crossCount m.val) :
    Positive diagonal m.val ∨ Classified diagonal m.val := by
  fin_cases diagonal
  · exact D0.finite_classification m hl hh
  · exact D1.finite_classification m hl hh
  · exact D2.finite_classification m hl hh
  · exact D3.finite_classification m hl hh

end FirstPaw

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem TriangleChain.Feasible.first_paw_rows {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (hn : ¬HasPacking G k) (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hheavy : 9 ≤ contacts G p.support q.support) (hleaf : 0 < degreeIn G p.leaf q.support) :
    PawBlock.Classified p q := by
  have hf := FirstPaw.finite_classification (Unattached.diagonal q) (PawEncoding.encoded p q)
    (by rw [PawEncoding.terminalCount_encoded]; omega)
    (by rw [PawEncoding.crossCount_encoded]; exact hheavy)
  rcases hf with hpos | hrows
  · exact False.elim (FirstPaw.positive_excluded hc hcard hdeg hn p hp hb q hq hpos)
  · exact hrows.transport p q

end Erdos577
