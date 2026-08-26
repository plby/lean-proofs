/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Tactic

/-! # The local coloring extension for the triangular prism exception -/

open SimpleGraph

namespace Erdos1091.Voss

/-- A triangle whose only external neighbours are three matched vertices
of another triangle is reducible for three-coloring. -/
theorem colorable_of_matched_triangle
    {V : Type*} {G : SimpleGraph V} (inner outer : Fin 3 → V)
    (hinj : Function.Injective inner)
    (hdisjoint : ∀ i j, outer i ≠ inner j)
    (houter : Pairwise (fun i j => G.Adj (outer i) (outer j)))
    (hneighbors : ∀ i v, G.Adj (inner i) v → (∃ j, v = inner j) ∨ v = outer i)
    (hcol : (G.induce {v | ∀ i, v ≠ inner i}).Colorable 3) : G.Colorable 3 := by
  classical
  obtain ⟨c⟩ := hcol
  let o : Fin 3 → {v : V // ∀ i, v ≠ inner i} := fun i => ⟨outer i, hdisjoint i⟩
  let f : V → Fin 3 := fun v =>
    if h : ∃ i, v = inner i then c (o (h.choose + 1))
    else c ⟨v, fun i heq => h ⟨i, heq⟩⟩
  have hfinner : ∀ i, f (inner i) = c (o (i + 1)) := by
    intro i
    have hex : ∃ j, inner i = inner j := ⟨i, rfl⟩
    have hchoose : hex.choose = i := (hinj hex.choose_spec).symm
    simp only [f, dif_pos hex, hchoose]
  have hfoutside : ∀ v (hv : ∀ i, v ≠ inner i), f v = c ⟨v, hv⟩ := by
    intro v hv
    have hn : ¬ ∃ i, v = inner i := fun ⟨i, hi⟩ => hv i hi
    simp only [f, dif_neg hn]
  have hshift : ∀ i : Fin 3, i + 1 ≠ i := by
    intro i
    fin_cases i <;> decide
  refine ⟨Coloring.mk f ?_⟩
  intro v w hvw
  by_cases hv : ∃ i, v = inner i
  · obtain ⟨i, rfl⟩ := hv
    by_cases hw : ∃ j, w = inner j
    · obtain ⟨j, rfl⟩ := hw
      rw [hfinner, hfinner]
      apply c.valid
      apply houter
      intro heq
      have hij : i = j := add_right_cancel heq
      exact hvw.ne (congrArg inner hij)
    · have hwout : ∀ j, w ≠ inner j := fun j heq => hw ⟨j, heq⟩
      have hwEq := (hneighbors i w hvw).resolve_left hw
      subst w
      rw [hfinner, hfoutside _ (hdisjoint i)]
      exact c.valid (houter (hshift i))
  · have hvout : ∀ i, v ≠ inner i := fun i heq => hv ⟨i, heq⟩
    by_cases hw : ∃ j, w = inner j
    · obtain ⟨j, rfl⟩ := hw
      have hvEq := (hneighbors j v hvw.symm).resolve_left hv
      subst v
      rw [hfoutside _ (hdisjoint j), hfinner]
      exact (c.valid (v := o (j + 1)) (w := o j) (houter (hshift j))).symm
    · have hwout : ∀ j, w ≠ inner j := fun j heq => hw ⟨j, heq⟩
      rw [hfoutside _ hvout, hfoutside _ hwout]
      exact c.valid hvw

/-- The same reduction from a coloring after deleting just one of the
inner vertices, as supplied by vertex criticality. -/
theorem colorable_of_matched_triangle_vertex_deletion
    {V : Type*} {G : SimpleGraph V} (inner outer : Fin 3 → V)
    (hinj : Function.Injective inner)
    (hdisjoint : ∀ i j, outer i ≠ inner j)
    (houter : Pairwise (fun i j => G.Adj (outer i) (outer j)))
    (hneighbors : ∀ i v, G.Adj (inner i) v → (∃ j, v = inner j) ∨ v = outer i)
    (hcol : (G.induce ({inner 0}ᶜ : Set V)).Colorable 3) : G.Colorable 3 := by
  obtain ⟨c⟩ := hcol
  have hsub : {v : V | ∀ i, v ≠ inner i} ⊆ ({inner 0}ᶜ : Set V) := by
    intro v hv
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hv 0
  exact colorable_of_matched_triangle inner outer hinj hdisjoint houter hneighbors
    ⟨c.comap (G.induceHomOfLE hsub).toHom⟩

/-- Three exhibited, distinct neighbours exhaust a degree-three bound. -/
theorem adj_cases_of_degree_le_three
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {v a b c w : V} (hdegree : G.degree v ≤ 3)
    (ha : G.Adj v a) (hb : G.Adj v b) (hc : G.Adj v c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hw : G.Adj v w) :
    w = a ∨ w = b ∨ w = c := by
  classical
  have hsub : ({a, b, c} : Finset V) ⊆ G.neighborFinset v := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> simpa
  have hcard : ({a, b, c} : Finset V).card = 3 := by simp [hab, hac, hbc]
  have heq : ({a, b, c} : Finset V) = G.neighborFinset v :=
    Finset.eq_of_subset_of_card_le hsub (by
      rw [SimpleGraph.card_neighborFinset_eq_degree, hcard]
      exact hdegree)
  have hm : w ∈ ({a, b, c} : Finset V) := by
    rw [heq]
    simpa using hw
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hm

#print axioms colorable_of_matched_triangle
#print axioms colorable_of_matched_triangle_vertex_deletion

end Erdos1091.Voss
