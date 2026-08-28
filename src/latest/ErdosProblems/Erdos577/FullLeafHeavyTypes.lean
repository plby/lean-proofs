import ErdosProblems.Erdos577.FullLeafHeavyLowCase

/-! The two disjoint types of every twenty-one-contact full-leaf block, TeX9.72. -/

namespace Erdos577.FullLeafHeavy

open Finset

variable {V : Type*} [DecidableEq V]

def Type40 (G : SimpleGraph V) [DecidableRel G.Adj] (p : Paw G)
    (s : Finset V) (y : V) (j : Finset V) : Prop :=
  degreeIn G p.leaf j = 0 ∧ degreeIn G y j = 0 ∧
    (∀ x ∈ s.erase y, degreeIn G x j ≤ 1) ∧ ∀ v ∈ j, degreeIn G v (s.erase y) ≤ 1

def Type41 (G : SimpleGraph V) [DecidableRel G.Adj] (p : Paw G)
    (a j : Finset V) : Prop :=
  (∀ u ∈ insert (p.vertices 3) a, degreeIn G u j ≤ 1) ∧
    ∀ v ∈ j, degreeIn G v (insert (p.vertices 3) a) ≤ 1

variable {G : SimpleGraph V} [DecidableRel G.Adj]

lemma Type41.contacts_le_four {p : Paw G} {a j : Finset V} (h : Type41 G p a j)
    (hj : j.card = 4) : contacts G (insert (p.vertices 3) a) j ≤ 4 := by
  calc
    contacts G (insert (p.vertices 3) a) j = contacts G j (insert (p.vertices 3) a) :=
      contacts_comm G _ _
    _ ≤ ∑ _ ∈ j, (1 : ℕ) := sum_le_sum h.2
    _ = 4 := by simp only [sum_const, smul_eq_mul, mul_one, hj]

end Erdos577.FullLeafHeavy

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}
variable (h : Configuration c p s a y)

include h

lemma Configuration.type40_first_contacts {j : Finset V} (htype : FullLeafHeavy.Type40 G p s y j) :
    contacts G (insert p.leaf s) j ≤ 3 := by
  obtain ⟨hX, hY, hrows, _⟩ := htype
  have htriple : contacts G (s.erase y) j ≤ 3 := by
    calc
      contacts G (s.erase y) j ≤ ∑ _ ∈ s.erase y, (1 : ℕ) := sum_le_sum hrows
      _ = 3 := by simp only [sum_const, smul_eq_mul, mul_one, h.first_triple_clique.card_eq]
  have hsplit := h.first_contacts j
  omega

lemma Configuration.type40_second_contacts {j : Finset V}
    (hheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j)
    (htype : FullLeafHeavy.Type40 G p s y j) :
    18 ≤ contacts G (insert (p.vertices 3) a) j := by
  have hfirst := h.type40_first_contacts htype
  rw [h.combined_contacts] at hheavy
  omega

theorem Configuration.heavy_types {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    (hheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j) :
    FullLeafHeavy.Type40 G p s y j ∨ FullLeafHeavy.Type41 G p a j := by
  by_cases hhigh : ∃ x ∈ insert p.leaf s, 3 ≤ degreeIn G x j
  · obtain ⟨x, hx, hrow⟩ := hhigh
    exact Or.inr (h.high_first_matching hcard hn hj hjs hja hheavy hx hrow)
  · have hrows : ∀ x ∈ insert p.leaf s, degreeIn G x j ≤ 2 := by
      intro x hx
      have hnot : ¬3 ≤ degreeIn G x j := fun hh ↦ hhigh ⟨x, hx, hh⟩
      omega
    obtain ⟨q, hq⟩ := c.property.blocks_quad j hj
    have hone := h.first_rows_le_one hcard hdeg hn q (by rwa [hq]) (by rwa [hq]) (by rwa [hq])
      (by rwa [hq]) (by simpa only [hq] using hrows)
    have htype := h.low_first_matching hcard hn q (by rwa [hq]) (by rwa [hq]) (by rwa [hq])
      (by rwa [hq]) hone
    exact Or.inl (by simpa only [FullLeafHeavy.Type40, hq] using htype)

theorem Configuration.heavy_types_disjoint {j : Finset V} (hj : j ∈ c.blocks)
    (hheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j) :
    ¬(FullLeafHeavy.Type40 G p s y j ∧ FullLeafHeavy.Type41 G p a j) := by
  rintro ⟨h40, h41⟩
  have hlow := h.type40_second_contacts hheavy h40
  have hhigh := h41.contacts_le_four (c.property.blocks_quad j hj).card
  omega

end Erdos577.FullLeafCore
