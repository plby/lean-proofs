import ErdosProblems.Erdos577.PathMiddleReplacements

/-! A row attaining the allowed column bound contains every allowed column. -/

namespace Erdos577.PathBlock

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma PatternB.full_middle_adj (p : FourPath G) (q : Quadrilateral G) (h : PatternB p q)
    (i : Fin 4) (hrow : degreeIn G (p.vertices i) q.support = 3)
    (j : Fin 4) (hj : j ≠ 3) : G.Adj (p.vertices i) (q j) := by
  have hsub : q.support.filter (G.Adj (p.vertices i)) ⊆ q.support.erase (q 3) := by
    intro v hv
    obtain ⟨hvq, hcv⟩ := mem_filter.mp hv
    refine mem_erase.mpr ⟨?_, hvq⟩
    intro he
    rw [he] at hcv
    exact h.column_ne_three p q i 3 hcv rfl
  have hcard : (q.support.erase (q 3)).card = 3 := by
    rw [card_erase_of_mem ((q.mem_support _).mpr ⟨3, rfl⟩), q.card_support]
  have he := eq_of_subset_of_card_le hsub (by
    change (q.support.erase (q 3)).card ≤ degreeIn G (p.vertices i) q.support
    rw [hcard, hrow])
  have hmem : q j ∈ q.support.erase (q 3) :=
    mem_erase.mpr ⟨fun hh ↦ hj (q.injective hh), (q.mem_support _).mpr ⟨j, rfl⟩⟩
  exact (mem_filter.mp (he.symm ▸ hmem)).2

lemma PatternB.full_endpoint_adj (p : FourPath G) (q : Quadrilateral G) (h : PatternB p q)
    (i : Fin 4) (hi : i = 0 ∨ i = 3) (hrow : degreeIn G (p.vertices i) q.support = 2)
    (j : Fin 4) (hj : j = 0 ∨ j = 1) : G.Adj (p.vertices i) (q j) := by
  have hsub : q.support.filter (G.Adj (p.vertices i)) ⊆ {q 0, q 1} := by
    intro v hv
    obtain ⟨hvq, hvrow⟩ := mem_filter.mp hv
    obtain ⟨l, rfl⟩ := (q.mem_support v).mp hvq
    have hl : l = 0 ∨ l = 1 := by
      rcases hi with rfl | rfl
      · exact h.1 l (Or.inl hvrow)
      · exact h.1 l (Or.inr hvrow)
    rcases hl with rfl | rfl <;> simp
  have hinj : Function.Injective (q : Fin 4 → V) := q.injective
  have hcard : ({q 0, q 1} : Finset V).card = 2 := by simp [hinj.eq_iff]
  have he := eq_of_subset_of_card_le hsub (by
    change ({q 0, q 1} : Finset V).card ≤ degreeIn G (p.vertices i) q.support
    rw [hcard, hrow])
  have hmem : q j ∈ ({q 0, q 1} : Finset V) := by rcases hj with rfl | rfl <;> simp
  exact (mem_filter.mp (he.symm ▸ hmem)).2

lemma PatternB.full_endpoint_contains (p : FourPath G) (q : Quadrilateral G) (h : PatternB p q)
    (i l : Fin 4) (hi : i = 0 ∨ i = 3) (hl : l = 0 ∨ l = 3)
    (hrow : degreeIn G (p.vertices i) q.support = 2)
    (u : V) (hu : u ∈ q.support) (hlu : G.Adj (p.vertices l) u) :
    G.Adj (p.vertices i) u := by
  obtain ⟨j, rfl⟩ := (q.mem_support u).mp hu
  have hj : j = 0 ∨ j = 1 := by
    rcases hl with rfl | rfl
    · exact h.1 j (Or.inl hlu)
    · exact h.1 j (Or.inr hlu)
  exact h.full_endpoint_adj p q i hi hrow j hj

end Erdos577.PathBlock
