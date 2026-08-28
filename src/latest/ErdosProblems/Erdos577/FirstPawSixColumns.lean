import ErdosProblems.Erdos577.FirstPawLeafTwo
import ErdosProblems.Erdos577.RowSaturation

/-! The exact triangle columns in case (6), once its second column has at most one contact. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma Paw.triangle_column (p : Paw G) (u : V) :
    degreeIn G u p.triangle = (if G.Adj (p.vertices 1) u then 1 else 0) +
      (if G.Adj (p.vertices 2) u then 1 else 0) + (if G.Adj (p.vertices 3) u then 1 else 0) := by
  have h1 : p.vertices 1 ∉ ({p.vertices 2, p.vertices 3} : Finset V) := by
    simp only [mem_insert, mem_singleton, p.vertices.injective.eq_iff]
    decide
  have h2 : p.vertices 2 ∉ ({p.vertices 3} : Finset V) := by
    simp only [mem_singleton, p.vertices.injective.eq_iff]
    decide
  rw [Paw.triangle, degreeIn_insert G _ _ h1, degreeIn_insert G _ _ h2, degreeIn_singleton]
  have he (i : Fin 4) : (if G.Adj u (p.vertices i) then 1 else 0) =
      (if G.Adj (p.vertices i) u then 1 else 0) := by
    by_cases hh : G.Adj (p.vertices i) u
    · simp only [hh, hh.symm, if_true]
    · have hh' : ¬G.Adj u (p.vertices i) := fun h' ↦ hh h'.symm
      simp only [hh, hh', if_false]
  rw [he 1, he 2, he 3]
  omega

lemma Paw.triangle_columns_sum (p : Paw G) (q : Quadrilateral G) :
    contacts G p.triangle q.support = degreeIn G (q 0) p.triangle +
      degreeIn G (q 1) p.triangle + degreeIn G (q 2) p.triangle +
      degreeIn G (q 3) p.triangle := by
  have hinj : Function.Injective (q : Fin 4 → V) := q.injective
  rw [contacts_comm, Quadrilateral.support, contacts_image_left G _ q hinj,
    Fin.sum_univ_four]

namespace PawBlock

lemma Pattern6.leaf_exact (p : Paw G) (q : Quadrilateral G) (h : Pattern6 p q)
    (hleaf : degreeIn G p.leaf q.support = 2) : WeightedPawBlock.Row p q 0 3 := by
  apply q.row_saturated (p.vertices 0) 3
  · intro j hj
    rcases h.2.1 j hj with rfl | rfl <;> decide
  · change _ ≤ degreeIn G p.leaf q.support
    rw [hleaf]
    decide +kernel

lemma Pattern6.columns_exact (p : Paw G) (q : Quadrilateral G) (h : Pattern6 p q)
    (hleaf : degreeIn G p.leaf q.support = 2) (hheavy : 9 ≤ contacts G p.support q.support)
    (hcolumn : degreeIn G (q 1) p.triangle ≤ 1) :
    contacts G p.support q.support = 9 ∧
      (ExactRows p q ![3, 13, 7, 1] ∨ ExactRows p q ![3, 15, 5, 1]) := by
  have hnotc (j : Fin 4) (hj : j ≠ 0) : ¬G.Adj (p.vertices 3) (q j) :=
    fun he ↦ hj (h.2.2.2 j he)
  have hnotb3 : ¬G.Adj (p.vertices 2) (q 3) := fun he ↦ h.2.2.1 3 he rfl
  have h0le := degreeIn_le_card G (q 0) p.triangle
  rw [p.triangle_clique.card_eq] at h0le
  have hf2 := p.triangle_column (q 2)
  have hf3 := p.triangle_column (q 3)
  rw [if_neg (hnotc 2 (by decide))] at hf2
  rw [if_neg (hnotc 3 (by decide)), if_neg hnotb3] at hf3
  have h2le : degreeIn G (q 2) p.triangle ≤ 2 := by split_ifs at hf2 <;> omega
  have h3le : degreeIn G (q 3) p.triangle ≤ 1 := by split_ifs at hf3 <;> omega
  have hs := p.triangle_columns_sum q
  have htotal := p.contacts_support q.support
  have h0 : degreeIn G (q 0) p.triangle = 3 := by omega
  have h1 : degreeIn G (q 1) p.triangle = 1 := by omega
  have h2 : degreeIn G (q 2) p.triangle = 2 := by omega
  have h3 : degreeIn G (q 3) p.triangle = 1 := by omega
  have he : contacts G p.support q.support = 9 := by omega
  have hfull0 : ∀ u ∈ p.triangle, G.Adj u (q 0) := by
    have hall := (degreeIn_eq_card_iff (q 0) p.triangle).mp
      (h0.trans p.triangle_clique.card_eq.symm)
    exact fun u hu ↦ (hall u hu).symm
  have hr0 := hfull0 (p.vertices 1) (by simp [Paw.triangle])
  have hb0 := hfull0 (p.vertices 2) (by simp [Paw.triangle])
  have hc0 := hfull0 (p.vertices 3) (by simp [Paw.triangle])
  have hr2 : G.Adj (p.vertices 1) (q 2) := by
    by_contra hh
    rw [if_neg hh] at hf2
    split_ifs at hf2 <;> omega
  have hb2 : G.Adj (p.vertices 2) (q 2) := by
    by_contra hh
    rw [if_pos hr2, if_neg hh] at hf2
    omega
  have hr3 : G.Adj (p.vertices 1) (q 3) := by
    by_contra hh
    rw [if_neg hh] at hf3
    omega
  have hx := h.leaf_exact p q hleaf
  have hrow3 : WeightedPawBlock.Row p q 3 1 := by
    intro j
    have hmask : ∀ j : Fin 4, (1 : ℕ).testBit j.val = true ↔ j = 0 := by decide +kernel
    rw [hmask j]
    exact ⟨h.2.2.2 j, fun he ↦ he ▸ hc0⟩
  have hf1 := p.triangle_column (q 1)
  rw [if_neg (hnotc 1 (by decide))] at hf1
  refine ⟨he, ?_⟩
  by_cases hr1 : G.Adj (p.vertices 1) (q 1)
  · have hb1 : ¬G.Adj (p.vertices 2) (q 1) := by
      intro hh
      rw [if_pos hr1, if_pos hh] at hf1
      omega
    right
    intro i j
    fin_cases i
    · exact hx j
    · change G.Adj (p.vertices 1) (q j) ↔ (15 : ℕ).testBit j.val = true
      fin_cases j
      · exact ⟨fun _ ↦ by decide, fun _ ↦ hr0⟩
      · exact ⟨fun _ ↦ by decide, fun _ ↦ hr1⟩
      · exact ⟨fun _ ↦ by decide, fun _ ↦ hr2⟩
      · exact ⟨fun _ ↦ by decide, fun _ ↦ hr3⟩
    · change G.Adj (p.vertices 2) (q j) ↔ (5 : ℕ).testBit j.val = true
      fin_cases j
      · exact ⟨fun _ ↦ by decide, fun _ ↦ hb0⟩
      · exact ⟨fun hh ↦ False.elim (hb1 hh), fun hh ↦ by contradiction⟩
      · exact ⟨fun _ ↦ by decide, fun _ ↦ hb2⟩
      · exact ⟨fun hh ↦ False.elim (hnotb3 hh), fun hh ↦ by contradiction⟩
    · exact hrow3 j
  · have hb1 : G.Adj (p.vertices 2) (q 1) := by
      by_contra hh
      rw [if_neg hr1, if_neg hh] at hf1
      omega
    left
    intro i j
    fin_cases i
    · exact hx j
    · change G.Adj (p.vertices 1) (q j) ↔ (13 : ℕ).testBit j.val = true
      fin_cases j
      · exact ⟨fun _ ↦ by decide, fun _ ↦ hr0⟩
      · exact ⟨fun hh ↦ False.elim (hr1 hh), fun hh ↦ by contradiction⟩
      · exact ⟨fun _ ↦ by decide, fun _ ↦ hr2⟩
      · exact ⟨fun _ ↦ by decide, fun _ ↦ hr3⟩
    · change G.Adj (p.vertices 2) (q j) ↔ (7 : ℕ).testBit j.val = true
      fin_cases j
      · exact ⟨fun _ ↦ by decide, fun _ ↦ hb0⟩
      · exact ⟨fun _ ↦ by decide, fun _ ↦ hb1⟩
      · exact ⟨fun _ ↦ by decide, fun _ ↦ hb2⟩
      · exact ⟨fun hh ↦ False.elim (hnotb3 hh), fun hh ↦ by contradiction⟩
    · exact hrow3 j

end PawBlock

end Erdos577
