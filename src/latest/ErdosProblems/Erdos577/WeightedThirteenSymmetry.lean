import ErdosProblems.Erdos577.WeightedThirteenPaths
import ErdosProblems.Erdos577.CycleLabels

/-! The simultaneous paw swap and cycle reflection preserve pattern (13) and exchange its paths. -/

namespace Erdos577.WeightedThirteen

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma swapped_pattern (p : Paw G) (q : Quadrilateral G) (h : WeightedPawBlock.Pattern13 p q) :
    WeightedPawBlock.Pattern13 (FirstPaw.normalizedPaw p true) q.reverse := by
  have hbits : ∀ j : Fin 4,
      (1 : ℕ).testBit (-j).val = (1 : ℕ).testBit j.val ∧
      (7 : ℕ).testBit (-j).val = (13 : ℕ).testBit j.val ∧
      (13 : ℕ).testBit (-j).val = (7 : ℕ).testBit j.val := by decide +kernel
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro he
    change G.Adj (q 3) (q 1) at he
    exact h.1 he.symm
  · intro j
    change G.Adj (p.vertices 0) (q (-j)) ↔ (1 : ℕ).testBit j.val = true
    rw [h.2.1 (-j), (hbits j).1]
  · intro j
    change G.Adj (p.vertices 3) (q (-j)) ↔ (13 : ℕ).testBit j.val = true
    rw [h.2.2.2 (-j), (hbits j).2.1]
  · intro j
    change G.Adj (p.vertices 2) (q (-j)) ↔ (7 : ℕ).testBit j.val = true
    rw [h.2.2.1 (-j), (hbits j).2.2]

omit [DecidableRel G.Adj] in
lemma swapped_disjoint (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support) :
    Disjoint (FirstPaw.normalizedPaw p true).support q.reverse.support := by
  rw [FirstPaw.normalizedPaw_support, q.reverse_support]
  exact hd

lemma path_swapped_support (second : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern13 p q) :
    (path second (FirstPaw.normalizedPaw p true) q.reverse (swapped_disjoint p q hd)
      (swapped_pattern p q h)).support = (path (!second) p q hd h).support := by
  cases second <;> rw [FourPath.support_eq, FourPath.support_eq] <;> rfl

variable [Fintype V]

theorem oriented_heavy_block {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern13 p q) :
    ∃ swap : Bool, ∃ q' : Quadrilateral G, ∃ hd' :
      Disjoint (FirstPaw.normalizedPaw p swap).support q'.support,
      ∃ h' : WeightedPawBlock.Pattern13 (FirstPaw.normalizedPaw p swap) q',
      q'.support = q.support ∧ ∃ a ∈ c.blocks, a ≠ b ∧
      9 ≤ contacts G (path true (FirstPaw.normalizedPaw p swap) q' hd' h').support a ∧
      17 ≤ contacts G (path false (FirstPaw.normalizedPaw p swap) q' hd' h').support a +
        contacts G (path true (FirstPaw.normalizedPaw p swap) q' hd' h').support a := by
  obtain ⟨a, ha, hab, hpair⟩ := heavy_block hcard hdeg hn p hp hb q hq hd h
  by_cases h9 : 9 ≤ contacts G (path true p q hd h).support a
  · exact ⟨false, q, hd, h, rfl, a, ha, hab, h9, hpair⟩
  · refine ⟨true, q.reverse, swapped_disjoint p q hd, swapped_pattern p q h,
      q.reverse_support, a, ha, hab, ?_, ?_⟩
    · rw [path_swapped_support]
      change 9 ≤ contacts G (path false p q hd h).support a
      omega
    · rw [path_swapped_support, path_swapped_support]
      change 17 ≤ contacts G (path true p q hd h).support a +
        contacts G (path false p q hd h).support a
      omega

end Erdos577.WeightedThirteen
