import ErdosProblems.Erdos577.CommonTripleWitnesses0
import ErdosProblems.Erdos577.CommonTripleWitnesses1
import ErdosProblems.Erdos577.CommonTripleWitnesses2
import ErdosProblems.Erdos577.CommonTripleWitnesses3
import ErdosProblems.Erdos577.CommonTriplePattern

/-! Wang's common-triple lemma with actual replacements and exact weighted contacts. -/

namespace Erdos577

open Finset

namespace CommonTriple

theorem finite_classification (diagonal : Fin 4) (m : Fin 65536) (hh : Hypotheses m.val) :
    Positive diagonal m.val ∨ Conclusion m.val := by
  fin_cases diagonal
  · exact D0.finite_classification m hh
  · exact D1.finite_classification m hh
  · exact D2.finite_classification m hh
  · exact D3.finite_classification m hh

end CommonTriple

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem Paw.common_triple (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (z : V) (hz : z ∉ p.support ∪ q.support)
    (hreplace : ¬CommonReplacement G (p.vertices 2) (p.vertices 3) z q.support)
    (hgain : ¬TwoEdgeReduction G (p.support ∪ q.support) (edgeCount G q.support + 2))
    (hheavy : 9 ≤ degreeIn G p.leaf q.support + degreeIn G (p.vertices 2) q.support +
      degreeIn G (p.vertices 3) q.support + degreeIn G z q.support)
    (hcases :
      (degreeIn G p.leaf q.support = 1 ∧ degreeIn G (p.vertices 2) q.support = 3 ∧
        ∀ v ∈ q.support, G.Adj (p.vertices 2) v ↔ G.Adj (p.vertices 3) v) ∨
      (degreeIn G p.leaf q.support = 0 ∧
        7 ≤ degreeIn G (p.vertices 2) q.support + degreeIn G (p.vertices 3) q.support)) :
    degreeIn G p.leaf q.support + degreeIn G (p.vertices 2) q.support +
        degreeIn G (p.vertices 3) q.support + degreeIn G z q.support = 9 ∧
      ∃ q' : Quadrilateral G, q'.support = q.support ∧
        (∀ j : Fin 4, j ≠ 0 → G.Adj (p.vertices 2) (q' j) ∧ G.Adj (p.vertices 3) (q' j)) ∧
        G.Adj z (q' 2) := by
  have hh := CommonTriple.hypotheses_encoded p q z hheavy hcases
  rcases CommonTriple.finite_classification (Unattached.diagonal q)
    (CommonTriple.encoded p q z) hh with hp | hc
  · rcases hp.transport p q hd z hz with hr | hg
    · exact False.elim (hreplace hr)
    · exact False.elim (hgain hg)
  · exact CommonTriple.conclusion_transport p q z hc

end Erdos577
