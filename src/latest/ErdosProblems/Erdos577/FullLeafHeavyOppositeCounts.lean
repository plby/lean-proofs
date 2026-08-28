import ErdosProblems.Erdos577.FullLeafHeavyHighCase

/-! The exact opposite-pair bounds in the low first-row branch of TeX9.72. -/

namespace Erdos577.FullLeafHeavy

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma columns_sum (q : Quadrilateral G) (t : Finset V) :
    contacts G t q.support = degreeIn G (q 0) t + degreeIn G (q 1) t +
      degreeIn G (q 2) t + degreeIn G (q 3) t := by
  have hinj : Function.Injective (q : Fin 4 → V) := q.injective
  rw [contacts_comm, Quadrilateral.support, contacts_image_left G _ q hinj, Fin.sum_univ_four]

end Erdos577.FullLeafHeavy

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

theorem Configuration.opposite_preparation (h : Configuration c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (q : Quadrilateral G) (hj : q.support ∈ c.blocks) (hjs : q.support ≠ s)
    (hja : q.support ≠ a)
    (hheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) q.support)
    (hrows : ∀ x ∈ insert p.leaf s, degreeIn G x q.support ≤ 2)
    {x : V} (hx : x ∈ insert p.leaf s) (h0 : G.Adj x (q 0)) (h2 : G.Adj x (q 2)) :
    (∀ i : Fin 4, i = 1 ∨ i = 3 → degreeIn G (q i) (p.triangle ∪ a) ≤ 1) ∧
      11 ≤ contacts G (insert (p.vertices 3) a) q.support ∧
      contacts G (insert (p.vertices 3) a) q.support ≤ 12 ∧
      9 ≤ degreeIn G (q 0) (insert (p.vertices 3) a) +
        degreeIn G (q 2) (insert (p.vertices 3) a) ∧
      9 ≤ contacts G (insert p.leaf s) q.support ∧
      5 ≤ contacts G (s.erase y) q.support := by
  have hout : x ∉ q.support := fun hh ↦ disjoint_left.mp (h.five_disjoint_block hj hjs) hx hh
  have hlow (i : Fin 4) (hi : i = 1 ∨ i = 3) : degreeIn G (q i) (p.triangle ∪ a) ≤ 1 :=
    h.core_degree_of_first_replacement hcard hn hx hj hjs hja
      ((q.mem_support _).mpr ⟨i, rfl⟩) (JointFinal.opposite_replace q x hout h0 h2 i hi)
  have h1 := (degreeIn_mono G (q 1) h.second_five_subset).trans (hlow 1 (Or.inl rfl))
  have h3 := (degreeIn_mono G (q 3) h.second_five_subset).trans (hlow 3 (Or.inr rfl))
  have h0b := degreeIn_le_card G (q 0) (insert (p.vertices 3) a)
  have h2b := degreeIn_le_card G (q 2) (insert (p.vertices 3) a)
  rw [h.second_five_card] at h0b h2b
  have hcols := FullLeafHeavy.columns_sum q (insert (p.vertices 3) a)
  have hs : contacts G (insert p.leaf s) q.support ≤ 10 := by
    calc
      contacts G (insert p.leaf s) q.support ≤ ∑ _ ∈ insert p.leaf s, (2 : ℕ) :=
        sum_le_sum hrows
      _ = 10 := by simp only [sum_const, smul_eq_mul, h.first_five_clique.card_eq]
  rw [h.combined_contacts] at hheavy
  have hX := hrows p.leaf (mem_insert_self _ _)
  have hY := hrows y (mem_insert_of_mem h.exposed)
  have hsplit := h.first_contacts q.support
  exact ⟨hlow, by omega, by omega, by omega, by omega, by omega⟩

end Erdos577.FullLeafCore
