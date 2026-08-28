import ErdosProblems.Erdos577.FirstPawSixSmallModel

/-! The six explicit path partitions forbid every required common insertion in cases (22)/(23). -/

namespace Erdos577.FirstPawSix.SmallCases

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma no_common_replacement {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (hdiag : PawBlock.OnlyFirst q) (variant : Bool)
    (hrows : PawBlock.ExactRows p q (caseRows (caseTag variant)))
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (tag : Fin 6) :
    ¬CommonReplacement G (PawEncoding.labeling p q hd (FactorTable.triple tag 0))
      (PawEncoding.labeling p q hd (FactorTable.triple tag 2))
      (PawEncoding.labeling p q hd (FactorTable.terminal tag)) a := by
  classical
  let d := ((FactorTable.partition variant tag).image
    (CaseModel.copy p q hd hdiag.1 _ hrows)).withSupport
    ((CaseModel.copy_image p q hd hdiag.1 _ hrows).trans
      (show p.support ∪ q.support = c.remainder ∪ b by rw [hp, hq]))
  exact c.no_common_replacement hcard hn hb ha hab d

lemma no_common_pair {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (hdiag : PawBlock.OnlyFirst q) (variant : Bool)
    (hrows : PawBlock.ExactRows p q (caseRows (caseTag variant)))
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (u v w : Fin 8) (hu : u ∈ terminalSet) (hv : v ∈ weightSet.erase u)
    (hw : w ∈ weightSet.erase u) (hvw : v ≠ w) :
    ¬CommonReplacement G (PawEncoding.labeling p q hd v)
      (PawEncoding.labeling p q hd w) (PawEncoding.labeling p q hd u) a := by
  obtain ⟨tag, ht, hend⟩ := FactorTable.endpoint_coverage u v w hu hv hw hvw
  have hno := no_common_replacement hcard hn p hp hb q hq hd hdiag variant hrows ha hab tag
  rw [ht] at hno
  rcases hend with ⟨h0, h2⟩ | ⟨h0, h2⟩
  · rw [h0, h2] at hno
    exact hno
  · rw [h0, h2] at hno
    rintro ⟨z, hz, hvz, hwz, hrep⟩
    exact hno ⟨z, hz, hwz, hvz, hrep⟩

end Erdos577.FirstPawSix.SmallCases
