/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

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

import ErdosProblems.Erdos223.Basic
import ErdosProblems.Erdos223.Stability

open scoped SimpleGraph

namespace Erdos223

noncomputable section

/-- Exact diameter-edge decomposition across a disjoint union. -/
theorem diameterPairCount_union_of_disjoint {d : ℕ}
    (B D : Finset (Point d)) (hdisj : Disjoint B D) :
    diameterPairCount (B ∪ D) = diameterPairCount B +
      ((B.product D).filter fun e ↦ dist e.1 e.2 = 1).card +
      diameterPairCount D := by
  classical
  let C := B ∪ D
  let V := {x : Point d // x ∈ C}
  let G : SimpleGraph V := diameterGraph C
  let S : Finset V := Finset.univ.filter fun x ↦ x.1 ∈ B
  have hdecomp := Stability.card_edgeFinset_decomp G S
  have hBC : C = B ∪ D := rfl
  let eB : {x : Point d // x ∈ B} ≃ {x : V // x ∈ S} :=
    { toFun := fun x ↦ ⟨⟨x.1, by simp [C, x.2]⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩⟩
      invFun := fun x ↦ ⟨x.1.1, (Finset.mem_filter.mp x.2).2⟩
      left_inv := fun x ↦ by ext; rfl
      right_inv := fun x ↦ by ext; rfl }
  let isoB : diameterGraph B ≃g G.induce (↑S : Set V) :=
    { toEquiv := eB
      map_rel_iff' := by
        intro x y
        rfl }
  have hinsideB : (G.induce (↑S : Set V)).edgeFinset.card = diameterPairCount B := by
    exact isoB.card_edgeFinset_eq.symm
  have hDnotB {x : Point d} (hxD : x ∈ D) : x ∉ B := by
    exact fun hxB ↦ Finset.disjoint_left.mp hdisj hxB hxD
  let eD : {x : Point d // x ∈ D} ≃ {x : V // x ∈ (Sᶜ : Finset V)} :=
    { toFun := fun x ↦ ⟨⟨x.1, by simp [C, x.2]⟩, by
          simp [S, hDnotB x.2]⟩
      invFun := fun x ↦ ⟨x.1.1, by
        have hxC : x.1.1 ∈ B ∪ D := by simpa [C] using x.1.2
        have hxNotB : x.1.1 ∉ B := by
          intro hxB
          have hxS : x.1 ∈ S := by simp [S, hxB]
          exact (Finset.mem_compl.mp x.2) hxS
        exact (Finset.mem_union.mp hxC).resolve_left hxNotB⟩
      left_inv := fun x ↦ by ext; rfl
      right_inv := fun x ↦ by ext; rfl }
  let isoD : diameterGraph D ≃g G.induce (↑(Sᶜ : Finset V) : Set V) :=
    { toEquiv := eD
      map_rel_iff' := by
        intro x y
        rfl }
  have hinsideD : (G.induce (↑(Sᶜ : Finset V) : Set V)).edgeFinset.card =
      diameterPairCount D := by
    exact isoD.card_edgeFinset_eq.symm
  let U := (B.product D).filter fun e ↦ dist e.1 e.2 = 1
  let T := (S.product Sᶜ).filter fun e ↦ G.Adj e.1 e.2
  have hcross : T.card = U.card := by
    symm
    refine Finset.card_bij (fun e he ↦
      let hp := Finset.mem_product.mp (Finset.mem_filter.mp he).1
      ((⟨e.1, by simp [C, hp.1]⟩ : V),
       (⟨e.2, by simp [C, hp.2]⟩ : V))) ?_ ?_ ?_
    · intro e he
      have he' := Finset.mem_filter.mp he
      have heprod := Finset.mem_product.mp he'.1
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
      · simp [S, heprod.1]
      · simp [S, hDnotB heprod.2]
      · exact he'.2
    · intro e he f hf hef
      apply Prod.ext
      · exact congrArg (fun q ↦ q.1.1) hef
      · exact congrArg (fun q ↦ q.2.1) hef
    · intro q hq
      have hq' := Finset.mem_filter.mp hq
      have hqprod := Finset.mem_product.mp hq'.1
      have hqB : q.1.1 ∈ B := by simpa [S] using hqprod.1
      have hqC : q.2.1 ∈ B ∪ D := by simpa [C] using q.2.2
      have hqNotB : q.2.1 ∉ B := by
        intro hB
        have : q.2 ∈ S := by simp [S, hB]
        exact (Finset.mem_compl.mp hqprod.2) this
      have hqD : q.2.1 ∈ D := (Finset.mem_union.mp hqC).resolve_left hqNotB
      let e : Point d × Point d := (q.1.1, q.2.1)
      refine ⟨e, ?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_product.mpr ⟨hqB, hqD⟩, hq'.2⟩
      · apply Prod.ext <;> apply Subtype.ext <;> rfl
  change G.edgeFinset.card = _ at hdecomp
  change diameterPairCount C = _
  change G.edgeFinset.card = _
  have hcross' : (((S ×ˢ Sᶜ).filter fun e ↦ G.Adj e.1 e.2).card) =
      ((B.product D).filter fun e ↦ dist e.1 e.2 = 1).card := by
    simpa [T, U] using hcross
  rw [hdecomp, hinsideB, hinsideD, hcross']

end

end Erdos223

#print axioms Erdos223.diameterPairCount_union_of_disjoint
