/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos76.PentagonTwoBlobMatchingGeneral

/-!
# Exceptional two-blob weights in Proposition 7.2(d)

For blob sizes `(3,5)` and two disjoint missing cross edges, Appendix A
uses the weights `1/2`, `1/3`, `0`, and `1/6`.  This file records those
families without choosing labels for the eight vertices.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Triples with one vertex in each of three displayed parts. -/
def threePartTriangleFamily (X Y Z : Finset α) : Finset (Finset α) :=
  X.biUnion fun x ↦ Y.biUnion fun y ↦ Z.image fun z ↦ {x, y, z}

lemma mem_threePartTriangleFamily_iff
    {X Y Z : Finset α} {t : Finset α} :
    t ∈ threePartTriangleFamily X Y Z ↔
      ∃ x ∈ X, ∃ y ∈ Y, ∃ z ∈ Z, t = {x, y, z} := by
  classical
  simp only [threePartTriangleFamily, mem_biUnion, mem_image]
  aesop

lemma threePartTriangleFamily_subset_powersetCard_union
    {X Y Z : Finset α} (hXY : Disjoint X Y) (hXZ : Disjoint X Z)
    (hYZ : Disjoint Y Z) :
    threePartTriangleFamily X Y Z ⊆ (X ∪ Y ∪ Z).powersetCard 3 := by
  classical
  intro t ht
  obtain ⟨x, hx, y, hy, z, hz, rfl⟩ :=
    mem_threePartTriangleFamily_iff.mp ht
  apply mem_powersetCard.mpr
  constructor
  · intro u hu
    simp only [mem_insert, mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · simp [hx]
    · simp [hy]
    · simp [hz]
  · have hxy : x ≠ y := fun h ↦
      Finset.disjoint_left.mp hXY hx (h ▸ hy)
    have hxz : x ≠ z := fun h ↦
      Finset.disjoint_left.mp hXZ hx (h ▸ hz)
    have hyz : y ≠ z := fun h ↦
      Finset.disjoint_left.mp hYZ hy (h ▸ hz)
    simp [hxy, hxz, hyz]

/-- The `1/3` family in Proposition 7.2(d): one matched left endpoint,
one non-partner matched right endpoint, and one unmatched right vertex. -/
def proposition72dThirdFamily
    (A' B' B₀ : Finset α) (f : A' ≃ B') : Finset (Finset α) :=
  (Finset.univ : Finset A').biUnion fun a ↦
    (B'.erase (f a).1).biUnion fun b ↦
      B₀.image fun c ↦ {a.1, b, c}

lemma mem_proposition72dThirdFamily_iff
    {A' B' B₀ : Finset α} {f : A' ≃ B'} {t : Finset α} :
    t ∈ proposition72dThirdFamily A' B' B₀ f ↔
      ∃ a : A', ∃ b ∈ B', b ≠ (f a).1 ∧
        ∃ c ∈ B₀, t = {a.1, b, c} := by
  classical
  constructor
  · intro ht
    obtain ⟨a, _ha, ht⟩ := mem_biUnion.mp ht
    obtain ⟨b, hb, ht⟩ := mem_biUnion.mp ht
    obtain ⟨c, hc, hct⟩ := mem_image.mp ht
    exact ⟨a, b, (mem_erase.mp hb).2, (mem_erase.mp hb).1,
      c, hc, hct.symm⟩
  · rintro ⟨a, b, hb, hba, c, hc, rfl⟩
    apply mem_biUnion.mpr
    refine ⟨a, mem_univ _, ?_⟩
    apply mem_biUnion.mpr
    refine ⟨b, mem_erase.mpr ⟨hba, hb⟩, ?_⟩
    exact mem_image.mpr ⟨c, hc, rfl⟩

/-- The union of the three families carrying weight `1/6` in the exceptional
`(3,5)` construction. -/
def proposition72dSixthFamily
    (A B A' B' : Finset α) : Finset (Finset α) :=
  let A₀ := A \ A'
  let B₀ := B \ B'
  twoOneTriangleFamily A B₀ ∪
    ((twoOneTriangleFamily B A₀) \ twoOneTriangleFamily B' A₀) ∪
      twoOneTriangleFamily B₀ A'

/-- The exact Appendix A weight for Proposition 7.2(d). -/
def proposition72dWeight
    (A B A' B' : Finset α) (f : A' ≃ B') : Finset α → ℝ :=
  addTriangleWeight
    (constantTriangleFamilyWeight
      (twoOneTriangleFamily B' (A \ A')) 2)
    (addTriangleWeight
      (constantTriangleFamilyWeight
        (proposition72dThirdFamily A' B' (B \ B') f) 3)
      (constantTriangleFamilyWeight
        (proposition72dSixthFamily A B A' B') 6))

end

end Erdos76
