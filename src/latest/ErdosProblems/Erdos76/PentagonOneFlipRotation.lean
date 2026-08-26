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
import ErdosProblems.Erdos76.PentagonOneFlipLower

/-!
# Rotating the oriented one-flip construction

The explicit construction in `PentagonOneFlipLower` uses labels `4,1,0`.
Here we prove that cyclic relabelling transports any distance-two pair to
that orientation.  No vertices or graph edges are relabelled: only the
five-valued blob map changes.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Cyclically rotate labels so that `i` becomes label `4`. -/
def pentagonRotateToFour (i j : Fin 5) : Fin 5 := j - i + 4

theorem pentagonRotateToFour_bijective (i : Fin 5) :
    Function.Bijective (pentagonRotateToFour i) := by
  fin_cases i <;> decide

/-- The cyclic label rotation as an equivalence. -/
def pentagonRotateToFourEquiv (i : Fin 5) : Fin 5 ≃ Fin 5 :=
  Equiv.ofBijective (pentagonRotateToFour i)
    (pentagonRotateToFour_bijective i)

@[simp] theorem pentagonRotateToFourEquiv_apply (i j : Fin 5) :
    pentagonRotateToFourEquiv i j = pentagonRotateToFour i j := rfl

@[simp] theorem pentagonRotateToFour_self (i : Fin 5) :
    pentagonRotateToFourEquiv i i = 4 := by
  fin_cases i <;> decide

@[simp] theorem pentagonRotateToFour_next (i : Fin 5) :
    pentagonRotateToFourEquiv i (pentagonNext i) = 0 := by
  fin_cases i <;> decide

@[simp] theorem pentagonRotateToFour_skip (i : Fin 5) :
    pentagonRotateToFourEquiv i (pentagonSkip i) = 1 := by
  fin_cases i <;> decide

theorem pentagonRotateToFour_cycle_adj_iff (i a b : Fin 5) :
    (SimpleGraph.cycleGraph 5).Adj
        (pentagonRotateToFourEquiv i a) (pentagonRotateToFourEquiv i b) ↔
      (SimpleGraph.cycleGraph 5).Adj a b := by
  fin_cases i <;> fin_cases a <;> fin_cases b <;> decide

/-- Relabelling the five blobs by an equivalence does not change their size
multiset. -/
theorem fiveSizeMultiset_comp_equiv (x : Fin 5 → ℕ) (σ : Fin 5 ≃ Fin 5) :
    fiveSizeMultiset (fun i ↦ x (σ i)) = fiveSizeMultiset x := by
  unfold fiveSizeMultiset
  change Multiset.map (x ∘ σ) Finset.univ.val = Multiset.map x Finset.univ.val
  rw [← Multiset.map_map]
  rw [Multiset.map_univ_val_equiv]

theorem pentagonB2Sizes_comp_equiv_iff
    (x : Fin 5 → ℕ) (σ : Fin 5 ≃ Fin 5) :
    PentagonB2Sizes (fun i ↦ x (σ i)) ↔ PentagonB2Sizes x := by
  unfold PentagonB2Sizes SameFiveSizes
  rw [fiveSizeMultiset_comp_equiv]

/-- Fibres after relabelling are the corresponding old fibres. -/
theorem pentagonBlobFinset_comp_equiv
    {α : Type*} [Fintype α] [DecidableEq α]
    (blob : α → Fin 5) (σ : Fin 5 ≃ Fin 5) (i : Fin 5) :
    pentagonBlobFinset (fun v ↦ σ (blob v)) i =
      pentagonBlobFinset blob (σ.symm i) := by
  ext v
  simp only [mem_pentagonBlobFinset]
  exact σ.apply_eq_iff_eq_symm_apply

/-- A cyclic rotation of the blob labels preserves the pentagon-blow-up
property. -/
theorem IsPentagonBlowup.rotateToFour
    {α : Type*} [Fintype α] [DecidableEq α]
    {H : SimpleGraph α} {blob : α → Fin 5}
    (hH : IsPentagonBlowup H blob) (i : Fin 5) :
    IsPentagonBlowup H
      (fun v ↦ pentagonRotateToFourEquiv i (blob v)) := by
  constructor
  · exact (pentagonRotateToFourEquiv i).surjective.comp hH.1
  · intro u v huv
    have huv' : blob u ≠ blob v := fun h ↦ huv (congrArg _ h)
    rw [hH.2 huv']
    exact (pentagonRotateToFour_cycle_adj_iff i (blob u) (blob v)).symm

/-- Exact Proposition 7.4(b) for an added edge joining labels `i` and
`i+2`; the original hard-coded orientation is recovered by cyclically
rotating labels. -/
theorem twoColorCoveredSize_sup_edge_skip_exact
    {α : Type*} [Fintype α] [DecidableEq α]
    {H : SimpleGraph α} {blob : α → Fin 5} {i : Fin 5} {x y : α}
    (hH : IsPentagonBlowup H blob)
    (hsizes : PentagonB2Sizes
      (fun j ↦ (pentagonBlobFinset blob j).card))
    (hx : x ∈ pentagonBlobFinset blob i)
    (hy : y ∈ pentagonBlobFinset blob (pentagonSkip i)) :
    (∃ wR wB : Finset α → ℝ,
      IsFractionalPacking (H ⊔ SimpleGraph.edge x y) wR ∧
      IsFractionalPacking (H ⊔ SimpleGraph.edge x y)ᶜ wB ∧
      fractionalCoveredSize (H ⊔ SimpleGraph.edge x y) wR +
          fractionalCoveredSize (H ⊔ SimpleGraph.edge x y)ᶜ wB =
        3 * ((∑ j : Fin 5,
          ((pentagonBlobFinset blob j).card.choose 2 : ℕ)) + 1)) ∧
    (∀ wR wB : Finset α → ℝ,
      IsFractionalPacking (H ⊔ SimpleGraph.edge x y) wR →
      IsFractionalPacking (H ⊔ SimpleGraph.edge x y)ᶜ wB →
      fractionalCoveredSize (H ⊔ SimpleGraph.edge x y) wR +
          fractionalCoveredSize (H ⊔ SimpleGraph.edge x y)ᶜ wB ≤
        3 * ((∑ j : Fin 5,
          ((pentagonBlobFinset blob j).card.choose 2 : ℕ)) + 1)) := by
  let σ := pentagonRotateToFourEquiv i
  let blob' : α → Fin 5 := fun v ↦ σ (blob v)
  obtain ⟨z, hz⟩ := hH.1 (pentagonNext i)
  have hH' : IsPentagonBlowup H blob' := hH.rotateToFour i
  have hblob (j : Fin 5) :
      pentagonBlobFinset blob' j = pentagonBlobFinset blob (σ.symm j) := by
    exact pentagonBlobFinset_comp_equiv blob σ j
  have hsizes' : PentagonB2Sizes
      (fun j ↦ (pentagonBlobFinset blob' j).card) := by
    have hcomp :
        (fun j ↦ (pentagonBlobFinset blob' j).card) =
          (fun j ↦ (pentagonBlobFinset blob (σ.symm j)).card) := by
      funext j
      rw [hblob]
    rw [hcomp]
    exact (pentagonB2Sizes_comp_equiv_iff
      (fun j ↦ (pentagonBlobFinset blob j).card) σ.symm).2 hsizes
  have hx' : x ∈ pentagonBlobFinset blob' 4 := by
    rw [mem_pentagonBlobFinset]
    change pentagonRotateToFourEquiv i (blob x) = 4
    rw [mem_pentagonBlobFinset] at hx
    rw [hx]
    exact pentagonRotateToFour_self i
  have hy' : y ∈ pentagonBlobFinset blob' 1 := by
    rw [mem_pentagonBlobFinset]
    change pentagonRotateToFourEquiv i (blob y) = 1
    rw [mem_pentagonBlobFinset] at hy
    rw [hy]
    exact pentagonRotateToFour_skip i
  have hz' : z ∈ pentagonBlobFinset blob' 0 := by
    rw [mem_pentagonBlobFinset]
    change pentagonRotateToFourEquiv i (blob z) = 0
    rw [hz]
    exact pentagonRotateToFour_next i
  have hsum :
      (∑ j : Fin 5, ((pentagonBlobFinset blob' j).card.choose 2 : ℕ)) =
        ∑ j : Fin 5, ((pentagonBlobFinset blob j).card.choose 2 : ℕ) := by
    simp_rw [hblob]
    exact Equiv.sum_comp σ.symm
      (fun j ↦ ((pentagonBlobFinset blob j).card.choose 2 : ℕ))
  simpa only [hsum] using
    (twoColorCoveredSize_sup_edge_oriented_exact
      hH' hsizes' hx' hy' hz')

/-- Exact Proposition 7.4(b) for an added edge between any two distinct
blobs.  Since the edge was absent in the pentagon blow-up, its labels form a
distance-two pair; one of the two cyclic orientations therefore feeds
`twoColorCoveredSize_sup_edge_skip_exact`. -/
theorem twoColorCoveredSize_sup_edge_cross_exact
    {α : Type*} [Fintype α] [DecidableEq α]
    {H : SimpleGraph α} {blob : α → Fin 5} {x y : α}
    (hH : IsPentagonBlowup H blob)
    (hsizes : PentagonB2Sizes
      (fun j ↦ (pentagonBlobFinset blob j).card))
    (hblob : blob x ≠ blob y) (hxyH : ¬H.Adj x y) :
    (∃ wR wB : Finset α → ℝ,
      IsFractionalPacking (H ⊔ SimpleGraph.edge x y) wR ∧
      IsFractionalPacking (H ⊔ SimpleGraph.edge x y)ᶜ wB ∧
      fractionalCoveredSize (H ⊔ SimpleGraph.edge x y) wR +
          fractionalCoveredSize (H ⊔ SimpleGraph.edge x y)ᶜ wB =
        3 * ((∑ j : Fin 5,
          ((pentagonBlobFinset blob j).card.choose 2 : ℕ)) + 1)) ∧
    (∀ wR wB : Finset α → ℝ,
      IsFractionalPacking (H ⊔ SimpleGraph.edge x y) wR →
      IsFractionalPacking (H ⊔ SimpleGraph.edge x y)ᶜ wB →
      fractionalCoveredSize (H ⊔ SimpleGraph.edge x y) wR +
          fractionalCoveredSize (H ⊔ SimpleGraph.edge x y)ᶜ wB ≤
        3 * ((∑ j : Fin 5,
          ((pentagonBlobFinset blob j).card.choose 2 : ℕ)) + 1)) := by
  have hcycle : ¬(SimpleGraph.cycleGraph 5).Adj (blob x) (blob y) := by
    intro h
    exact hxyH ((hH.2 hblob).2 h)
  have hcomp : (SimpleGraph.cycleGraph 5)ᶜ.Adj (blob x) (blob y) := by
    rw [SimpleGraph.compl_adj]
    exact ⟨hblob, hcycle⟩
  rcases (cycleGraph5_compl_adj_iff_skip (blob x) (blob y)).mp hcomp with
    hskip | hskip
  · apply twoColorCoveredSize_sup_edge_skip_exact hH hsizes
    · exact mem_pentagonBlobFinset.mpr rfl
    · exact mem_pentagonBlobFinset.mpr hskip
  · have h := twoColorCoveredSize_sup_edge_skip_exact
      (i := blob y) (x := y) (y := x) hH hsizes
      (mem_pentagonBlobFinset.mpr rfl)
      (mem_pentagonBlobFinset.mpr hskip)
    simpa only [SimpleGraph.edge_comm y x] using h

end

end Erdos76
