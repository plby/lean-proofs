import ErdosProblems.Erdos577.FirstPawSixWeightedModel

/-! The case24 insertion table forbids every leaf pair and the two final high-pair insertions. -/

namespace Erdos577.FirstPawSix.WeightedCase

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma no_common_replacement {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (hdiag : PawBlock.OnlyFirst q)
    (hrows : PawBlock.ExactRows p q (caseRows 2))
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (tag : Fin 8) :
    ¬CommonReplacement G (PawEncoding.labeling p q hd (FactorTable.triple tag 0))
      (PawEncoding.labeling p q hd (FactorTable.triple tag 2))
      (PawEncoding.labeling p q hd (FactorTable.terminal tag)) a := by
  classical
  let d := ((FactorTable.partition tag).image
    (CaseModel.copy p q hd hdiag.1 2 hrows)).withSupport
    ((CaseModel.copy_image p q hd hdiag.1 2 hrows).trans
      (show p.support ∪ q.support = c.remainder ∪ b by rw [hp, hq]))
  exact c.no_common_replacement hcard hn hb ha hab d

lemma no_leaf_pair {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (hdiag : PawBlock.OnlyFirst q)
    (hrows : PawBlock.ExactRows p q (caseRows 2))
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (v w : Fin 8) (hv : v ∈ vertexSet.erase 0) (hw : w ∈ vertexSet.erase 0) (hvw : v ≠ w) :
    ¬CommonReplacement G (PawEncoding.labeling p q hd v)
      (PawEncoding.labeling p q hd w) p.leaf a := by
  obtain ⟨tag, ht, hend⟩ := FactorTable.endpoint_coverage v w hv hw hvw
  have hno := no_common_replacement hcard hn p hp hb q hq hd hdiag hrows ha hab tag
  rw [ht] at hno
  rcases hend with ⟨h0, h2⟩ | ⟨h0, h2⟩
  · rw [h0, h2] at hno
    exact hno
  · rw [h0, h2] at hno
    rintro ⟨z, hz, hvz, hwz, hrep⟩
    exact hno ⟨z, hz, hwz, hvz, hrep⟩

lemma no_noncentral_insert {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (hdiag : PawBlock.OnlyFirst q)
    (hrows : PawBlock.ExactRows p q (caseRows 2))
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (i : Fin 4) (hi : i = 2 ∨ i = 3) :
    ¬CommonReplacement G (q 3) (q 1) (p.vertices i) a := by
  rcases hi with rfl | rfl
  · exact no_common_replacement hcard hn p hp hb q hq hd hdiag hrows ha hab 7
  · rintro ⟨z, hz, hq3, hq1, hrep⟩
    exact no_common_replacement hcard hn p hp hb q hq hd hdiag hrows ha hab 6
      ⟨z, hz, hq1, hq3, hrep⟩

end Erdos577.FirstPawSix.WeightedCase
