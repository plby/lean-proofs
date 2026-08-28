import ErdosProblems.Erdos577.WeightedPawPatterns
import ErdosProblems.Erdos577.PawDiagonalCopy
import ErdosProblems.Erdos577.StrictExchange
import ErdosProblems.Erdos577.ScoredExchange
import ErdosProblems.Erdos577.QuadScores

/-! The positive and upper cores of pattern (15), and its three forbidden center contacts. -/

namespace Erdos577.WeightedFifteen

open Finset

def graph : SimpleGraph (Fin 8) := PawModel.graph 1 28417

def upperGraph : SimpleGraph (Fin 8) := PawModel.graph 1 28481

instance : DecidableRel graph.Adj := inferInstanceAs (DecidableRel (PawModel.graph 1 28417).Adj)

instance : DecidableRel upperGraph.Adj :=
  inferInstanceAs (DecidableRel (PawModel.graph 1 28481).Adj)

def centerColumn : Fin 3 → Fin 4 := ![0, 1, 3]

def centerMask (t : Fin 3) : Fin 65536 :=
  ⟨28417 + 2 ^ (4 + (centerColumn t).val), by fin_cases t <;> decide +kernel⟩

lemma center_exchange (t : Fin 3) :
    ScoredExchange (PawModel.graph 1 (centerMask t).val) univ 6 := by
  fin_cases t
  · refine Or.inr ⟨{
      terminal := 7
      triangle := {0, 1, 4}
      block := {2, 3, 5, 6}
      triangle_clique := by decide +kernel
      terminal_not_mem := by decide +kernel
      quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
      disjoint := by decide +kernel
      cover := by decide +kernel }, ?_⟩
    decide +kernel
  · exact Or.inl ⟨{0, 1, 5, 4}, subset_univ _,
      QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel),
      QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)⟩
  · exact Or.inl ⟨{0, 1, 7, 4}, subset_univ _,
      QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel),
      QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)⟩

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma base_rows (p : Paw G) (q : Quadrilateral G) (h : WeightedPawBlock.Pattern15 p q)
    (i j : Fin 4) (hb : (28417 : ℕ).testBit (4 * i.val + j.val) = true) :
    G.Adj (p.vertices i) (q j) := by
  have hbits : ∀ i j : Fin 4, (28417 : ℕ).testBit (4 * i.val + j.val) =
      ((![1, 0, 15, 6] : Fin 4 → ℕ) i).testBit j.val := by decide +kernel
  rw [hbits] at hb
  fin_cases i
  · exact (h.2.1 j).mpr hb
  · change (0 : ℕ).testBit j.val = true at hb
    simp at hb
  · exact (h.2.2.1 j).mpr hb
  · exact (h.2.2.2 j).mpr hb

def coreCopy (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern15 p q) : graph.Copy G :=
  PawEncoding.copyWithDiagonalOfRows p q hd 1
    (PawEncoding.first_diagonal_submask q h.1.1) 28417 (base_rows p q h)

lemma coreCopy_image (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern15 p q) :
    univ.image (coreCopy p q hd h) = p.support ∪ q.support :=
  PawEncoding.copyWithDiagonalOfRows_image p q hd 1
    (PawEncoding.first_diagonal_submask q h.1.1) 28417 (base_rows p q h)

lemma old_edgeCount (p : Paw G) (q : Quadrilateral G) (h : WeightedPawBlock.Pattern15 p q) :
    edgeCount G q.support = 5 := by
  rw [q.edgeCount_eq, if_pos h.1.1, if_neg h.1.2]

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma center_rows (p : Paw G) (q : Quadrilateral G) (h : WeightedPawBlock.Pattern15 p q)
    (t : Fin 3) (hc : G.Adj p.center (q (centerColumn t))) (i j : Fin 4)
    (hb : (centerMask t).val.testBit (4 * i.val + j.val) = true) :
    G.Adj (p.vertices i) (q j) := by
  have hbits : ∀ i j : Fin 4, ∀ t : Fin 3,
      (centerMask t).val.testBit (4 * i.val + j.val) = true →
      (28417 : ℕ).testBit (4 * i.val + j.val) = true ∨ (i = 1 ∧ j = centerColumn t) := by
    decide +kernel
  rcases hbits i j t hb with hb | ⟨rfl, rfl⟩
  · exact base_rows p q h i j hb
  · exact hc

variable [Fintype V]

lemma center_absent {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern15 p q) :
    ∀ j : Fin 4, j ≠ 2 → ¬G.Adj p.center (q j) := by
  intro j hj hjedge
  have hcolumns : ∀ j : Fin 4, j ≠ 2 → ∃ t : Fin 3, centerColumn t = j := by decide +kernel
  obtain ⟨t, rfl⟩ := hcolumns j hj
  let f := PawEncoding.copyWithDiagonalOfRows p q hd 1
    (PawEncoding.first_diagonal_submask q h.1.1) (centerMask t) (center_rows p q h t hjedge)
  have he : univ.image f = c.remainder ∪ b := by
    rw [PawEncoding.copyWithDiagonalOfRows_image, hp, hq]
  have hx := (center_exchange t).image f
  rw [he] at hx
  rcases hx with hf | ⟨d, hg⟩
  · exact c.no_local_factor hcard hn hb hf
  · apply hc.no_strict_improvement hb
    refine ⟨d, ?_⟩
    have ho : edgeCount G b = 5 := by rw [← hq]; exact old_edgeCount p q h
    omega

end Erdos577.WeightedFifteen
