/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos735.CyclicSkeleton

/-!
# Three edges exhaust a finite cyclic line

The graph of cyclic successors on a finite line is a cycle.  Consequently,
if three distinct vertices are joined by all three possible cyclic edges,
there are no further vertices on the line.  This elementary order lemma is
the finite core of the local failed-Fano recognition arguments.
-/

open Classical

namespace Erdos735.ChartOrder

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem cyclicConsecutive_of_pair_eq
    (coord : V → ℝ) (S : Finset V)
    {a b u v : V} (hab : a ≠ b)
    (huv : CyclicConsecutive coord S u v)
    (hp : ({u, v} : Finset V) = {a, b}) :
    CyclicConsecutive coord S a b ∨ CyclicConsecutive coord S b a := by
  have huvne : u ≠ v := by
    intro huv
    subst v
    have hc := congrArg Finset.card hp
    simp [hab] at hc
  have hu : u = a ∨ u = b := by
    have : u ∈ ({a, b} : Finset V) := by
      rw [← hp]
      simp
    simpa using this
  have hv : v = a ∨ v = b := by
    have : v ∈ ({a, b} : Finset V) := by
      rw [← hp]
      simp
    simpa using this
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact False.elim (huvne (hu.trans hv.symm))
  · subst u; subst v; exact Or.inl huv
  · subst u; subst v; exact Or.inr huv
  · exact False.elim (huvne (hu.trans hv.symm))

private theorem subset_three_of_ordered
    (coord : V → ℝ) (S : Finset V)
    (hinj : Set.InjOn coord (S : Set V))
    {a b x : V} (ha : a ∈ S) (hb : b ∈ S) (hx : x ∈ S)
    (hab : coord a < coord b) (hbx : coord b < coord x)
    (hAB : CyclicConsecutive coord S a b ∨
      CyclicConsecutive coord S b a)
    (hBX : CyclicConsecutive coord S b x ∨
      CyclicConsecutive coord S x b)
    (hXA : CyclicConsecutive coord S x a ∨
      CyclicConsecutive coord S a x) :
    S ⊆ {a, b, x} := by
  have hAB' : CyclicConsecutive coord S a b := by
    rcases hAB with h | h
    · exact h
    · exfalso
      rcases h with h | h
      · exact (not_lt_of_ge hab.le) h.lt
      · exact (not_lt_of_ge (h.2.2.1 x hx)) hbx
  have hBX' : CyclicConsecutive coord S b x := by
    rcases hBX with h | h
    · exact h
    · exfalso
      rcases h with h | h
      · exact (not_lt_of_ge hbx.le) h.lt
      · exact (not_lt_of_ge (h.2.2.2 a ha)) hab
  have hXA' : CyclicConsecutive coord S x a := by
    rcases hXA with h | h
    · exact h
    · exact False.elim (h.no_between hb ⟨hab, hbx⟩)
  have hwrap : x ∈ S ∧ a ∈ S ∧
      (∀ y ∈ S, coord y ≤ coord x) ∧
      ∀ y ∈ S, coord a ≤ coord y := by
    rcases hXA' with h | h
    · exact False.elim ((not_lt_of_ge (hab.le.trans hbx.le)) h.lt)
    · exact h
  intro y hy
  have hay : coord a ≤ coord y := hwrap.2.2.2 y hy
  have hyx : coord y ≤ coord x := hwrap.2.2.1 y hy
  have hcases : coord y = coord a ∨ coord y = coord b ∨ coord y = coord x := by
    rcases lt_trichotomy (coord y) (coord b) with hyb | hyb | hby
    · rcases lt_or_eq_of_le hay with hay | hay
      · exact False.elim (hAB'.no_between hy ⟨hay, hyb⟩)
      · exact Or.inl hay.symm
    · exact Or.inr (Or.inl hyb)
    · rcases lt_or_eq_of_le hyx with hyx | hyx
      · exact False.elim (hBX'.no_between hy ⟨hby, hyx⟩)
      · exact Or.inr (Or.inr hyx)
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases hcases with h | h | h
  · exact Or.inl (hinj hy ha h)
  · exact Or.inr (Or.inl (hinj hy hb h))
  · exact Or.inr (Or.inr (hinj hy hx h))

/-- If all three unordered pairs among `a,b,x` occur as cyclic edges of
`S`, then `S` consists exactly of those three vertices. -/
theorem eq_triple_of_three_cyclic_pairs
    (coord : V → ℝ) (S : Finset V)
    (hinj : Set.InjOn coord (S : Set V))
    {a b x : V} (ha : a ∈ S) (hb : b ∈ S) (hx : x ∈ S)
    (hab : a ≠ b) (hax : a ≠ x) (hbx : b ≠ x)
    (hAB : CyclicConsecutive coord S a b ∨
      CyclicConsecutive coord S b a)
    (hBX : CyclicConsecutive coord S b x ∨
      CyclicConsecutive coord S x b)
    (hXA : CyclicConsecutive coord S x a ∨
      CyclicConsecutive coord S a x) :
    S = {a, b, x} := by
  apply Finset.Subset.antisymm
  · have habc : coord a ≠ coord b := fun h ↦ hab (hinj ha hb h)
    have haxc : coord a ≠ coord x := fun h ↦ hax (hinj ha hx h)
    have hbxc : coord b ≠ coord x := fun h ↦ hbx (hinj hb hx h)
    rcases lt_or_gt_of_ne habc with hablt | hbalt
    · rcases lt_or_gt_of_ne hbxc with hbxlt | hxb_lt
      · exact subset_three_of_ordered coord S hinj ha hb hx hablt hbxlt
          hAB hBX hXA
      · rcases lt_or_gt_of_ne haxc with haxlt | hxa_lt
        · intro y hy
          have hmem := subset_three_of_ordered coord S hinj ha hx hb haxlt hxb_lt
            hXA.symm hBX.symm hAB.symm hy
          simpa only [Finset.mem_insert, Finset.mem_singleton, or_assoc,
            or_left_comm, or_comm] using hmem
        · intro y hy
          have hmem := subset_three_of_ordered coord S hinj hx ha hb hxa_lt hablt
            hXA hAB hBX hy
          simpa only [Finset.mem_insert, Finset.mem_singleton, or_assoc,
            or_left_comm, or_comm] using hmem
    · rcases lt_or_gt_of_ne haxc with haxlt | hxa_lt
      · intro y hy
        have hmem := subset_three_of_ordered coord S hinj hb ha hx hbalt haxlt
          hAB.symm hXA.symm hBX.symm hy
        simpa only [Finset.mem_insert, Finset.mem_singleton, or_assoc,
          or_left_comm, or_comm] using hmem
      · rcases lt_or_gt_of_ne hbxc with hbxlt | hxb_lt
        · intro y hy
          have hmem := subset_three_of_ordered coord S hinj hb hx ha hbxlt hxa_lt
            hBX hXA hAB hy
          simpa only [Finset.mem_insert, Finset.mem_singleton, or_assoc,
            or_left_comm, or_comm] using hmem
        · intro y hy
          have hmem := subset_three_of_ordered coord S hinj hx hb ha hxb_lt hbalt
            hBX.symm hAB.symm hXA.symm hy
          simpa only [Finset.mem_insert, Finset.mem_singleton, or_assoc,
            or_left_comm, or_comm] using hmem
  · intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
    rcases hy with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hx

/-- Cyclic-edge form of `eq_triple_of_three_cyclic_pairs`. -/
theorem verticesOn_eq_triple_of_three_edges
    {L : Type*} [Fintype L] [DecidableEq L]
    (vertices : Finset V) (onLine : V → L → Prop) [DecidableRel onLine]
    (coord : V → ℝ) (hinj : Set.InjOn coord (vertices : Set V))
    {l : L} {a b x : V}
    (hab : a ≠ b) (hax : a ≠ x) (hbx : b ≠ x)
    (eAB eBX eXA : CyclicSkeletonEdge vertices onLine)
    (hlAB : cyclicEdgeLine eAB = l)
    (hlBX : cyclicEdgeLine eBX = l)
    (hlXA : cyclicEdgeLine eXA = l)
    (hAB : cyclicEdgeVertices vertices onLine coord eAB = {a, b})
    (hBX : cyclicEdgeVertices vertices onLine coord eBX = {b, x})
    (hXA : cyclicEdgeVertices vertices onLine coord eXA = {x, a}) :
    verticesOn vertices onLine l = {a, b, x} := by
  let S := verticesOn vertices onLine l
  have hconAB := cyclicEdgeFinish_spec vertices onLine coord eAB
  have hconBX := cyclicEdgeFinish_spec vertices onLine coord eBX
  have hconXA := cyclicEdgeFinish_spec vertices onLine coord eXA
  change eAB.1 = l at hlAB
  change eBX.1 = l at hlBX
  change eXA.1 = l at hlXA
  rw [hlAB] at hconAB
  rw [hlBX] at hconBX
  rw [hlXA] at hconXA
  have hAB' : CyclicConsecutive coord S a b ∨
      CyclicConsecutive coord S b a :=
    cyclicConsecutive_of_pair_eq coord S hab hconAB (by
      simpa [cyclicEdgeVertices] using hAB)
  have hBX' : CyclicConsecutive coord S b x ∨
      CyclicConsecutive coord S x b :=
    cyclicConsecutive_of_pair_eq coord S hbx hconBX (by
      simpa [cyclicEdgeVertices] using hBX)
  have hXA' : CyclicConsecutive coord S x a ∨
      CyclicConsecutive coord S a x :=
    cyclicConsecutive_of_pair_eq coord S hax.symm hconXA (by
      simpa [cyclicEdgeVertices] using hXA)
  apply eq_triple_of_three_cyclic_pairs coord S
    (hinj.mono (Finset.filter_subset _ _))
  · exact hAB'.elim CyclicConsecutive.left_mem CyclicConsecutive.right_mem
  · exact hAB'.elim CyclicConsecutive.right_mem CyclicConsecutive.left_mem
  · exact hBX'.elim CyclicConsecutive.right_mem CyclicConsecutive.left_mem
  · exact hab
  · exact hax
  · exact hbx
  · exact hAB'
  · exact hBX'
  · exact hXA'

end Erdos735.ChartOrder
