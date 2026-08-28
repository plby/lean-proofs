import ErdosProblems.Erdos577.WeightedPawPatterns
import ErdosProblems.Erdos577.PawPartialCopy
import ErdosProblems.Erdos577.StrictExchange
import ErdosProblems.Erdos577.ScoredExchange
import ErdosProblems.Erdos577.QuadScores

/-! Positive core copies and the four forbidden center contacts in weighted pattern (19). -/

namespace Erdos577.WeightedNineteen

open Finset

def graph : SimpleGraph (Fin 8) := PawModel.graph 0 38659

instance : DecidableRel graph.Adj := inferInstanceAs (DecidableRel (PawModel.graph 0 38659).Adj)

def centerMask (j : Fin 4) : Fin 65536 :=
  ⟨38659 + 2 ^ (4 + j.val), by fin_cases j <;> decide +kernel⟩

lemma center_exchange (j : Fin 4) :
    ScoredExchange (PawModel.graph 0 (centerMask j).val) univ 5 := by
  fin_cases j
  · exact Or.inl ⟨{0, 1, 4, 5}, subset_univ _,
      QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel),
      QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)⟩
  · exact Or.inl ⟨{0, 1, 4, 5}, subset_univ _,
      QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel),
      QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)⟩
  · exact Or.inl ⟨{0, 1, 6, 5}, subset_univ _,
      QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel),
      QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)⟩
  · refine Or.inr ⟨{
      terminal := 6
      triangle := {0, 4, 5}
      block := {1, 2, 3, 7}
      triangle_clique := by decide +kernel
      terminal_not_mem := by decide +kernel
      quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
      disjoint := by decide +kernel
      cover := by decide +kernel }, ?_⟩
    decide +kernel

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma base_rows (p : Paw G) (q : Quadrilateral G) (h : WeightedPawBlock.Pattern19 p q)
    (i j : Fin 4) (hb : (38659 : ℕ).testBit (4 * i.val + j.val) = true) :
    G.Adj (p.vertices i) (q j) := by
  have hbits : ∀ i j : Fin 4, (38659 : ℕ).testBit (4 * i.val + j.val) =
      ((![3, 0, 7, 9] : Fin 4 → ℕ) i).testBit j.val := by decide +kernel
  rw [hbits] at hb
  fin_cases i
  · exact (h.2.2.1 j).mpr hb
  · change (0 : ℕ).testBit j.val = true at hb
    simp at hb
  · exact (h.2.2.2.1 j).mpr hb
  · exact (h.2.2.2.2 j).mpr hb

def coreCopy (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern19 p q) : graph.Copy G :=
  PawEncoding.copyOfRows p q hd 38659 (base_rows p q h)

lemma coreCopy_image (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern19 p q) :
    univ.image (coreCopy p q hd h) = p.support ∪ q.support :=
  PawEncoding.copyOfRows_image p q hd 38659 (base_rows p q h)

lemma old_edgeCount (p : Paw G) (q : Quadrilateral G) (h : WeightedPawBlock.Pattern19 p q) :
    edgeCount G q.support = 4 := by
  rw [q.edgeCount_eq, if_neg h.1, if_neg h.2.1]

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma center_rows (p : Paw G) (q : Quadrilateral G) (h : WeightedPawBlock.Pattern19 p q)
    (j : Fin 4) (hc : G.Adj p.center (q j)) (i l : Fin 4)
    (hb : (centerMask j).val.testBit (4 * i.val + l.val) = true) :
    G.Adj (p.vertices i) (q l) := by
  have hbits : ∀ i j l : Fin 4, (centerMask j).val.testBit (4 * i.val + l.val) = true →
      (38659 : ℕ).testBit (4 * i.val + l.val) = true ∨ (i = 1 ∧ l = j) := by decide +kernel
  rcases hbits i j l hb with hb | ⟨rfl, rfl⟩
  · exact base_rows p q h i l hb
  · exact hc

variable [Fintype V]

lemma center_absent {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern19 p q) :
    ∀ j : Fin 4, ¬G.Adj p.center (q j) := by
  intro j hj
  let f := PawEncoding.copyOfRows p q hd (centerMask j) (center_rows p q h j hj)
  have he : univ.image f = c.remainder ∪ b := by
    rw [PawEncoding.copyOfRows_image, hp, hq]
  have hx := (center_exchange j).image f
  rw [he] at hx
  rcases hx with hf | ⟨d, hg⟩
  · exact c.no_local_factor hcard hn hb hf
  · apply hc.no_strict_improvement hb
    refine ⟨d, ?_⟩
    have ho : edgeCount G b = 4 := by rw [← hq]; exact old_edgeCount p q h
    omega

end Erdos577.WeightedNineteen
