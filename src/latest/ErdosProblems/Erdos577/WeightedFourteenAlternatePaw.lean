import ErdosProblems.Erdos577.WeightedFourteenTerminals
import ErdosProblems.Erdos577.PawEleven

/-! The second strong paw presentation in pattern (14), with all outside blocks retained. -/

namespace Erdos577.WeightedFourteen

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def alternatePaw (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern14 p q) : Paw G where
  vertices := (⟨![7, 2, 1, 3], by decide +kernel⟩ : Fin 4 ↪ Fin 8).trans
    (PawEncoding.labeling p q hd)
  pendant := by
    change G.Adj (q 3) (p.vertices 2)
    exact ((h.2.2.1 3).mpr (by decide)).symm
  edge12 := by
    change G.Adj (p.vertices 2) (p.vertices 1)
    exact p.edge12.symm
  edge13 := by
    change G.Adj (p.vertices 2) (p.vertices 3)
    exact p.edge23
  edge23 := by
    change G.Adj (p.vertices 1) (p.vertices 3)
    exact p.edge13

lemma alternatePaw_triangle (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern14 p q) : (alternatePaw p q hd h).triangle = p.triangle := by
  change {p.vertices 2, p.vertices 1, p.vertices 3} = {p.vertices 1, p.vertices 2, p.vertices 3}
  exact insert_comm _ _ _

lemma alternatePaw_support (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern14 p q) :
    (alternatePaw p q hd h).support = insert (q 3) p.triangle := by
  rw [Paw.support_eq, alternatePaw_triangle]
  rfl

variable [DecidableRel G.Adj]

lemma alternatePaw_contacts (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern14 p q) (a : Finset V) :
    contacts G (alternatePaw p q hd h).support a =
      degreeIn G (q 3) a + contacts G p.triangle a := by
  rw [Paw.contacts_support, alternatePaw_triangle]
  rfl

variable [Fintype V]

theorem exists_alternate_strong_chain {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern14 p q) :
    ∃ d : TriangleChain G, d.Strong ∧ d.terminal = q 3 ∧ d.triangle = p.triangle ∧
      (alternatePaw p q hd h).support = d.remainder ∧
      ∀ a ∈ c.blocks, a ≠ b → a ∈ d.blocks := by
  obtain ⟨d, hdF, hdx, hdt, hkeep⟩ := exists_odd_terminal_chain hc p hp hb q hq hd h 3 (Or.inr rfl)
  let p' := alternatePaw p q hd h
  have hp' : p'.support = d.remainder := by
    rw [alternatePaw_support]
    change insert (q 3) p.triangle = insert d.terminal d.triangle
    rw [hdx, hdt]
  refine ⟨d.presentPaw p' hp', hdF.presentPaw_strong hcard hn p' hp', rfl,
    alternatePaw_triangle p q hd h, p'.support_eq, ?_⟩
  exact fun a ha hab ↦ hkeep a ha hab

end Erdos577.WeightedFourteen
