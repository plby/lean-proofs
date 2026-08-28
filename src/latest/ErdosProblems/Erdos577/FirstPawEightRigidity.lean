import ErdosProblems.Erdos577.FirstPawEightColumns

/-! Equality in the six-contact count forces both high contacts in the remaining old low row. -/

namespace Erdos577.FirstPawEight

open Finset

lemma six_contact_rigidity (x y z : Fin 4 → ℕ)
    (hx : x 0 + x 2 ≤ 1) (hy : y 0 + y 2 ≤ 1) (hz0 : z 0 ≤ 1) (hz2 : z 2 ≤ 1)
    (h1 : x 1 + y 1 + z 1 ≤ 1) (h3 : x 3 + y 3 + z 3 ≤ 1)
    (hs : 6 ≤ x 0 + y 0 + z 0 + (x 1 + y 1 + z 1) +
      (x 2 + y 2 + z 2) + (x 3 + y 3 + z 3)) :
    x 0 + x 2 = 1 ∧ y 0 + y 2 = 1 ∧ z 0 = 1 ∧ z 2 = 1 ∧
      x 1 + y 1 + z 1 = 1 ∧ x 3 + y 3 + z 3 = 1 := by omega

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
private lemma high_indicator_le_one (d : Quadrilateral G) (u : V)
    (h : ¬(G.Adj u (d 0) ∧ G.Adj u (d 2))) :
    (if G.Adj u (d 0) then 1 else 0) + (if G.Adj u (d 2) then 1 else 0) ≤ (1 : ℕ) := by
  by_cases h0 : G.Adj u (d 0) <;> by_cases h2 : G.Adj u (d 2) <;> simp_all

omit [DecidableEq V] in
private lemma adj_of_indicator_one (u v : V)
    (h : (if G.Adj u v then 1 else 0) = (1 : ℕ)) : G.Adj u v := by
  by_contra hn
  simp only [if_neg hn] at h
  contradiction

omit [DecidableEq V] in
private lemma high_contact_of_sum_one (d : Quadrilateral G) (u : V)
    (h : (if G.Adj u (d 0) then 1 else 0) + (if G.Adj u (d 2) then 1 else 0) = (1 : ℕ)) :
    G.Adj u (d 0) ∨ G.Adj u (d 2) := by
  by_contra! hn
  simp only [if_neg hn.1, if_neg hn.2] at h
  omega

variable [Fintype V]

theorem high_columns_rigid {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern8 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (hheavy : 9 ≤ contacts G (rows p q hd) a)
    (d : Quadrilateral G) (hdA : d.support = a)
    (h0 : G.Adj (q 1) (d 0)) (h2 : G.Adj (q 1) (d 2))
    (hx : ¬(G.Adj p.leaf (d 0) ∧ G.Adj p.leaf (d 2)))
    (hy : ¬(G.Adj (p.vertices 3) (d 0) ∧ G.Adj (p.vertices 3) (d 2))) :
    G.Adj (q 3) (d 0) ∧ G.Adj (q 3) (d 2) ∧
      (G.Adj p.leaf (d 0) ∨ G.Adj p.leaf (d 2)) ∧
      (G.Adj (p.vertices 3) (d 0) ∨ G.Adj (p.vertices 3) (d 2)) ∧
      degreeIn G (d 1) (otherRows p q hd) = 1 ∧
      degreeIn G (d 3) (otherRows p q hd) = 1 := by
  let x : Fin 4 → ℕ := fun j ↦ if G.Adj p.leaf (d j) then 1 else 0
  let y : Fin 4 → ℕ := fun j ↦ if G.Adj (p.vertices 3) (d j) then 1 else 0
  let z : Fin 4 → ℕ := fun j ↦ if G.Adj (q 3) (d j) then 1 else 0
  have h1 := low_column_bound hcard hn p hp hb q hq hd h ha hab d hdA h0 h2 1 (Or.inl rfl)
  have h3 := low_column_bound hcard hn p hp hb q hq hd h ha hab d hdA h0 h2 3 (Or.inr rfl)
  have hs := other_contacts_ge_six hcard hn p hp hb q hq hd h ha hab hheavy
  rw [← hdA, other_columns_sum] at hs
  simp only [other_column] at h1 h3 hs
  have hz0 : z 0 ≤ 1 := by dsimp only [z]; split_ifs <;> omega
  have hz2 : z 2 ≤ 1 := by dsimp only [z]; split_ifs <;> omega
  obtain ⟨hex, hey, hez0, hez2, he1, he3⟩ := six_contact_rigidity x y z
    (high_indicator_le_one d p.leaf hx) (high_indicator_le_one d (p.vertices 3) hy)
    hz0 hz2 h1 h3 hs
  refine ⟨adj_of_indicator_one _ _ hez0, adj_of_indicator_one _ _ hez2,
    high_contact_of_sum_one d p.leaf hex, high_contact_of_sum_one d (p.vertices 3) hey, ?_, ?_⟩
  · exact (other_column p q hd (d 1)).trans he1
  · exact (other_column p q hd (d 3)).trans he3

omit [DecidableRel G.Adj] in
theorem terminal_first_low_absent {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern8 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (d : Quadrilateral G) (hdA : d.support = a)
    (h1 : G.Adj (q 1) (d 1)) (hw0 : G.Adj (q 3) (d 0)) (hw2 : G.Adj (q 3) (d 2)) :
    ¬G.Adj p.leaf (d 1) ∧ ¬G.Adj (p.vertices 3) (d 1) := by
  have hout : q 3 ∉ d.support := by
    rw [hdA]
    exact fun hh ↦ disjoint_left.mp (c.property.blocks_disjoint hb ha hab.symm)
      (hq ▸ (q.mem_support _).mpr ⟨3, rfl⟩) hh
  have hr := d.low_replace_of_highs (q 3) hout hw0 hw2 1 (Or.inl rfl)
  rw [hdA] at hr
  have hmem : d 1 ∈ a := hdA ▸ (d.mem_support _).mpr ⟨1, rfl⟩
  constructor
  · intro hx
    exact no_common_pair hcard hn p hp hb q hq hd h ha hab 7 0 5
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
      ⟨d 1, hmem, hx, h1, hr⟩
  · intro hy
    exact no_common_pair hcard hn p hp hb q hq hd h ha hab 7 3 5
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
      ⟨d 1, hmem, hy, h1, hr⟩

theorem no_terminal_high_pair_shape {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern8 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (hheavy : 9 ≤ contacts G (rows p q hd) a)
    (d : Quadrilateral G) (hdA : d.support = a)
    (hrow : ∀ j : Fin 4, G.Adj (q 1) (d j) ↔ j ≠ 3)
    (hx : ¬(G.Adj p.leaf (d 0) ∧ G.Adj p.leaf (d 2)))
    (hy : ¬(G.Adj (p.vertices 3) (d 0) ∧ G.Adj (p.vertices 3) (d 2))) :
    (∀ j : Fin 4, G.Adj (q 3) (d j) ↔ j ≠ 3) ∧
      ¬G.Adj p.leaf (d 1) ∧ ¬G.Adj (p.vertices 3) (d 1) ∧
      (G.Adj p.leaf (d 0) ∨ G.Adj p.leaf (d 2)) ∧
      (G.Adj (p.vertices 3) (d 0) ∨ G.Adj (p.vertices 3) (d 2)) ∧
      ((G.Adj p.leaf (d 3) ∧ ¬G.Adj (p.vertices 3) (d 3)) ∨
        (¬G.Adj p.leaf (d 3) ∧ G.Adj (p.vertices 3) (d 3))) := by
  obtain ⟨hw0, hw2, hxp, hyp, hc1, hc3⟩ := high_columns_rigid hcard hn p hp hb q hq hd h
    ha hab hheavy d hdA ((hrow 0).mpr (by decide)) ((hrow 2).mpr (by decide)) hx hy
  obtain ⟨hx1, hy1⟩ := terminal_first_low_absent hcard hn p hp hb q hq hd h ha hab d hdA
    ((hrow 1).mpr (by decide)) hw0 hw2
  simp only [other_column, if_neg hx1, if_neg hy1, zero_add] at hc1
  have hw1 : G.Adj (q 3) (d 1) := adj_of_indicator_one _ _ hc1
  have hbnd : degreeIn G (q 3) a ≤ 3 :=
    row_bound hcard hn p hp hb q hq hd h ha hab hheavy 7 (by decide +kernel)
  have hw3 : ¬G.Adj (q 3) (d 3) := by
    intro hh
    have hfull : degreeIn G (q 3) d.support = 4 := by
      apply Eq.trans ?_ d.card_support
      apply (degreeIn_eq_card_iff (q 3) d.support).mpr
      intro u hu
      obtain ⟨j, rfl⟩ := (d.mem_support u).mp hu
      fin_cases j
      · exact hw0
      · exact hw1
      · exact hw2
      · exact hh
    rw [hdA] at hfull
    omega
  refine ⟨?_, hx1, hy1, hxp, hyp, ?_⟩
  · intro j
    fin_cases j
    · exact ⟨fun _ ↦ by decide, fun _ ↦ hw0⟩
    · exact ⟨fun _ ↦ by decide, fun _ ↦ hw1⟩
    · exact ⟨fun _ ↦ by decide, fun _ ↦ hw2⟩
    · exact ⟨fun hh ↦ False.elim (hw3 hh), fun hh ↦ False.elim (hh rfl)⟩
  · rw [other_column, if_neg hw3, add_zero] at hc3
    by_cases hx3 : G.Adj p.leaf (d 3) <;>
      by_cases hy3 : G.Adj (p.vertices 3) (d 3) <;> simp_all

end Erdos577.FirstPawEight
