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
import ErdosProblems.Erdos76.PentagonSizeBounds
import ErdosProblems.Erdos76.PentagonTwoBlob

/-!
# Elementary structure of a five-blob pentagon blow-up

We use explicit successor and distance-two maps on `Fin 5`.  Thus the five
red inter-blob pairs and the five blue inter-blob pairs have canonical
orientations, avoiding quotient choices later in the packing construction.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Clockwise successor on the labelled pentagon. -/
def pentagonNext : Fin 5 → Fin 5 := ![1, 2, 3, 4, 0]

/-- The vertex two clockwise steps away on the labelled pentagon. -/
def pentagonSkip : Fin 5 → Fin 5 := ![2, 3, 4, 0, 1]

theorem cycleGraph5_adj_iff_next (i j : Fin 5) :
    (SimpleGraph.cycleGraph 5).Adj i j ↔
      j = pentagonNext i ∨ i = pentagonNext j := by
  fin_cases i <;> fin_cases j <;> decide

theorem cycleGraph5_compl_adj_iff_skip (i j : Fin 5) :
    (SimpleGraph.cycleGraph 5)ᶜ.Adj i j ↔
      j = pentagonSkip i ∨ i = pentagonSkip j := by
  fin_cases i <;> fin_cases j <;> decide

theorem pentagonNext_ne (i : Fin 5) : pentagonNext i ≠ i := by
  fin_cases i <;> decide

theorem pentagonSkip_ne (i : Fin 5) : pentagonSkip i ≠ i := by
  fin_cases i <;> decide

theorem pentagonNext_injective : Function.Injective pentagonNext := by
  decide

theorem pentagonSkip_injective : Function.Injective pentagonSkip := by
  decide

theorem pentagonNext_pair_unique (i j : Fin 5) :
    s(i, pentagonNext i) = s(j, pentagonNext j) ↔ i = j := by
  fin_cases i <;> fin_cases j <;> decide

theorem pentagonSkip_pair_unique (i j : Fin 5) :
    s(i, pentagonSkip i) = s(j, pentagonSkip j) ↔ i = j := by
  fin_cases i <;> fin_cases j <;> decide

theorem pentagonNext_skip_pairs_disjoint (i j : Fin 5) :
    s(i, pentagonNext i) ≠ s(j, pentagonSkip j) := by
  fin_cases i <;> fin_cases j <;> decide

/-- The finite vertex fiber with a specified pentagon label. -/
def pentagonBlobFinset {α : Type*} [Fintype α] [DecidableEq α]
    (blob : α → Fin 5) (i : Fin 5) : Finset α :=
  Finset.univ.filter fun v ↦ blob v = i

@[simp] theorem mem_pentagonBlobFinset
    {α : Type*} [Fintype α] [DecidableEq α]
    {blob : α → Fin 5} {i : Fin 5} {v : α} :
    v ∈ pentagonBlobFinset blob i ↔ blob v = i := by
  simp [pentagonBlobFinset]

theorem pentagonBlobFinset_disjoint
    {α : Type*} [Fintype α] [DecidableEq α]
    (blob : α → Fin 5) {i j : Fin 5} (hij : i ≠ j) :
    Disjoint (pentagonBlobFinset blob i) (pentagonBlobFinset blob j) := by
  apply Finset.disjoint_left.mpr
  intro v hvi hvj
  exact hij ((mem_pentagonBlobFinset.mp hvi).symm.trans
    (mem_pentagonBlobFinset.mp hvj))

theorem card_pentagonBlobFinset_pos_of_surjective
    {α : Type*} [Fintype α] [DecidableEq α]
    {blob : α → Fin 5} (hblob : Function.Surjective blob) (i : Fin 5) :
    0 < (pentagonBlobFinset blob i).card := by
  rw [Finset.card_pos]
  obtain ⟨v, rfl⟩ := hblob i
  exact ⟨v, mem_pentagonBlobFinset.mpr rfl⟩

/-- The five fibers partition the whole finite vertex type. -/
theorem sum_card_pentagonBlobFinset
    {α : Type*} [Fintype α] [DecidableEq α]
    (blob : α → Fin 5) :
    ∑ i, (pentagonBlobFinset blob i).card = Fintype.card α := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset α))
    (t := (Finset.univ : Finset (Fin 5)))
    (f := blob) (fun _ _ ↦ Finset.mem_univ _)
  simpa [pentagonBlobFinset] using h.symm

theorem fiveSizeSum_blobCard
    {α : Type*} [Fintype α] [DecidableEq α]
    (blob : α → Fin 5) :
    fiveSizeSum (fun i ↦ (pentagonBlobFinset blob i).card) =
      Fintype.card α := by
  simpa [fiveSizeSum] using sum_card_pentagonBlobFinset blob

theorem pentagonBlowup_cross_adj
    {α : Type*} [Fintype α] [DecidableEq α]
    {G : SimpleGraph α} {blob : α → Fin 5}
    (hG : IsPentagonBlowup G blob)
    {i j : Fin 5} (hij : i ≠ j)
    {u v : α} (hu : u ∈ pentagonBlobFinset blob i)
    (hv : v ∈ pentagonBlobFinset blob j) :
    G.Adj u v ↔ (SimpleGraph.cycleGraph 5).Adj i j := by
  rw [hG.2]
  · simp only [mem_pentagonBlobFinset] at hu hv
    simpa [hu, hv]
  · simp only [mem_pentagonBlobFinset] at hu hv
    simpa [hu, hv] using hij

theorem pentagonBlowup_next_cross
    {α : Type*} [Fintype α] [DecidableEq α]
    {G : SimpleGraph α} {blob : α → Fin 5}
    (hG : IsPentagonBlowup G blob) (i : Fin 5) :
    ∀ u ∈ pentagonBlobFinset blob i,
      ∀ v ∈ pentagonBlobFinset blob (pentagonNext i), G.Adj u v := by
  intro u hu v hv
  rw [pentagonBlowup_cross_adj hG (pentagonNext_ne i).symm hu hv,
    cycleGraph5_adj_iff_next]
  exact Or.inl rfl

theorem pentagonBlowup_skip_cross_compl
    {α : Type*} [Fintype α] [DecidableEq α]
    {G : SimpleGraph α} {blob : α → Fin 5}
    (hG : IsPentagonBlowup G blob) (i : Fin 5) :
    ∀ u ∈ pentagonBlobFinset blob i,
      ∀ v ∈ pentagonBlobFinset blob (pentagonSkip i), Gᶜ.Adj u v := by
  intro u hu v hv
  have hcross := pentagonBlowup_cross_adj hG (pentagonSkip_ne i).symm hu hv
  rw [SimpleGraph.compl_adj]
  constructor
  · intro huv
    subst v
    have hi : i = pentagonSkip i :=
      (mem_pentagonBlobFinset.mp hu).symm.trans
        (mem_pentagonBlobFinset.mp hv)
    exact (pentagonSkip_ne i) hi.symm
  · exact fun hadj ↦
      ((cycleGraph5_compl_adj_iff_skip i (pentagonSkip i)).mpr
        (Or.inl rfl)).2 (hcross.mp hadj)

end

end Erdos76
