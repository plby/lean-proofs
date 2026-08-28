import ErdosProblems.Erdos577.ClaimTwoFour

/-! The exact first-block rows in weighted pattern12, including its forced zero center row. -/

namespace Erdos577.WeightedTwelve

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma counts (p : Paw G) (q : Quadrilateral G) (h : WeightedPawBlock.Pattern12 p q) :
    degreeIn G p.leaf q.support = 3 ∧ degreeIn G (p.vertices 2) q.support = 3 ∧
      degreeIn G (p.vertices 3) q.support = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · change degreeIn G (p.vertices 0) q.support = 3
    rw [h.2.1.degree p q 0 7]
    decide +kernel
  · rw [h.2.2.1.degree p q 2 7]
    decide +kernel
  · rw [h.2.2.2.degree p q 3 8]
    decide +kernel

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma first_rows (p : Paw G) (q : Quadrilateral G) (h : WeightedPawBlock.Pattern12 p q) :
    (∀ i : Fin 4, i ≠ 3 → G.Adj p.leaf (q i)) ∧ G.Adj (p.vertices 3) (q 3) := by
  have hbits : ∀ i : Fin 4, (7 : ℕ).testBit i.val = true ↔ i ≠ 3 := by decide +kernel
  exact ⟨fun i hi ↦ (h.2.1 i).mpr ((hbits i).mpr hi), (h.2.2.2 3).mpr (by decide)⟩

variable [Fintype V]

theorem center_zero {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks)
    (q : Quadrilateral G) (hq : q.support = s) (h : WeightedPawBlock.Pattern12 p q) :
    degreeIn G p.center q.support = 0 := by
  have hx : 3 ≤ degreeIn G p.leaf s := by rw [← hq, (counts p q h).1]
  have hrb := JointClaims.triangle_rows_disjoint hc hcard hn p hp hs hx
    p.center (p.vertices 2) p.center_mem_triangle (by simp [Paw.triangle])
    (p.vertices.injective.ne (by decide : (1 : Fin 4) ≠ 2))
  have hrc := JointClaims.triangle_rows_disjoint hc hcard hn p hp hs hx
    p.center (p.vertices 3) p.center_mem_triangle (by simp [Paw.triangle])
    (p.vertices.injective.ne (by decide : (1 : Fin 4) ≠ 3))
  apply (degreeIn_eq_zero_iff (G := G) p.center q.support).mpr
  intro u hu hru
  obtain ⟨i, rfl⟩ := (q.mem_support u).mp hu
  have hm : q i ∈ s := hq ▸ (q.mem_support _).mpr ⟨i, rfl⟩
  by_cases hi : i = 3
  · subst i
    exact disjoint_left.mp hrc (mem_filter.mpr ⟨hm, hru⟩)
      (mem_filter.mpr ⟨hm, (h.2.2.2 3).mpr (by decide)⟩)
  · have hbi : G.Adj (p.vertices 2) (q i) := by
      have hbits : ∀ i : Fin 4, i ≠ 3 → (7 : ℕ).testBit i.val = true := by decide +kernel
      exact (h.2.2.1 i).mpr (hbits i hi)
    exact disjoint_left.mp hrb (mem_filter.mpr ⟨hm, hru⟩) (mem_filter.mpr ⟨hm, hbi⟩)

end Erdos577.WeightedTwelve
