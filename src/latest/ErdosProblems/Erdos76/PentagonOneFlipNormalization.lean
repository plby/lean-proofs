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
import ErdosProblems.Erdos76.PentagonOneFlipRotation

/-!
# Normalizing a one-edge flip

The `edgeFlipDistance` definition is phrased using graph edge finsets.  Its
generic graph arguments use the generic finite-edge-set instance, whereas a
syntactically visible supremum may select a more specialized instance.  The
small wrapper `stableEdgeFinset` fixes the generic representation and makes
the usual symmetric-difference argument propositionally stable.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The generic edge-finset representation used by `edgeFlipDistance`. -/
def stableEdgeFinset (G : SimpleGraph α) : Finset (Sym2 α) := G.edgeFinset

@[simp] theorem mem_stableEdgeFinset {G : SimpleGraph α} {e : Sym2 α} :
    e ∈ stableEdgeFinset G ↔ e ∈ G.edgeSet := by
  simp [stableEdgeFinset]

theorem edgeFlipDistance_eq_stableEdgeFinset (G H : SimpleGraph α) :
    edgeFlipDistance G H =
      ((stableEdgeFinset G \ stableEdgeFinset H).card +
        (stableEdgeFinset H \ stableEdgeFinset G).card) := by
  rfl

private theorem exists_eq_sup_edge_of_stableEdgeFinset_diffs
    (G H : SimpleGraph α)
    (hnew : (stableEdgeFinset G \ stableEdgeFinset H).card = 1)
    (hold : (stableEdgeFinset H \ stableEdgeFinset G).card = 0) :
    ∃ x y : α, x ≠ y ∧ ¬H.Adj x y ∧
      G = H ⊔ SimpleGraph.edge x y := by
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hnew
  have hsub : stableEdgeFinset H ⊆ stableEdgeFinset G :=
    Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hold)
  have hdecomp :
      stableEdgeFinset G = stableEdgeFinset H ∪ {e} := by
    have h := Finset.sdiff_union_of_subset hsub
    rw [he] at h
    calc
      stableEdgeFinset G = {e} ∪ stableEdgeFinset H := h.symm
      _ = stableEdgeFinset H ∪ {e} := Finset.union_comm _ _
  have heDiff : e ∈ stableEdgeFinset G \ stableEdgeFinset H := by
    rw [he]
    simp
  have heG : e ∈ stableEdgeFinset G := (Finset.mem_sdiff.mp heDiff).1
  have heH : e ∉ stableEdgeFinset H := (Finset.mem_sdiff.mp heDiff).2
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hGxy : G.Adj x y := by
        simpa [SimpleGraph.mem_edgeSet] using heG
      have hxy : x ≠ y := G.ne_of_adj hGxy
      have hHxy : ¬H.Adj x y := by
        simpa [SimpleGraph.mem_edgeSet] using heH
      refine ⟨x, y, hxy, hHxy, ?_⟩
      apply SimpleGraph.edgeSet_inj.mp
      ext q
      have hq := Finset.ext_iff.mp hdecomp q
      simpa [SimpleGraph.edgeSet_sup,
        SimpleGraph.edgeSet_edge_of_ne hxy] using hq

/-- A graph pair at flip distance one is obtained by adjoining one absent
non-loop edge, in exactly one of the two directions. -/
theorem edgeFlipDistance_eq_one_iff_add_edge
    (G H : SimpleGraph α) (hflip : edgeFlipDistance G H = 1) :
    (∃ x y : α, x ≠ y ∧ ¬H.Adj x y ∧
      G = H ⊔ SimpleGraph.edge x y) ∨
    (∃ x y : α, x ≠ y ∧ ¬G.Adj x y ∧
      H = G ⊔ SimpleGraph.edge x y) := by
  rw [edgeFlipDistance_eq_stableEdgeFinset] at hflip
  have hcases :
      ((stableEdgeFinset G \ stableEdgeFinset H).card = 1 ∧
        (stableEdgeFinset H \ stableEdgeFinset G).card = 0) ∨
      ((stableEdgeFinset G \ stableEdgeFinset H).card = 0 ∧
        (stableEdgeFinset H \ stableEdgeFinset G).card = 1) := by
    omega
  rcases hcases with h | h
  · exact Or.inl
      (exists_eq_sup_edge_of_stableEdgeFinset_diffs G H h.1 h.2)
  · exact Or.inr
      (exists_eq_sup_edge_of_stableEdgeFinset_diffs H G h.2 h.1)

/-- Adding an edge inside one blob preserves the pentagon-blow-up
structure, since colours inside blobs are unrestricted. -/
theorem IsPentagonBlowup.sup_edge_same_blob
    {H : SimpleGraph α} {blob : α → Fin 5} {x y : α}
    (hH : IsPentagonBlowup H blob) (hxy : blob x = blob y) :
    IsPentagonBlowup (H ⊔ SimpleGraph.edge x y) blob := by
  refine ⟨hH.1, ?_⟩
  intro u v huv
  have hedge : ¬(SimpleGraph.edge x y).Adj u v := by
    intro he
    rcases Sym2.eq_iff.mp ((SimpleGraph.adj_edge x y).mp he).1 with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact huv hxy
    · exact huv hxy.symm
  rw [SimpleGraph.sup_adj, or_iff_left hedge]
  exact hH.2 huv

/-- Conversely, removing an edge inside a blob preserves all prescribed
cross-blob colours. -/
theorem IsPentagonBlowup.of_sup_edge_same_blob
    {G : SimpleGraph α} {blob : α → Fin 5} {x y : α}
    (hH : IsPentagonBlowup (G ⊔ SimpleGraph.edge x y) blob)
    (hxy : blob x = blob y) :
    IsPentagonBlowup G blob := by
  refine ⟨hH.1, ?_⟩
  intro u v huv
  have hedge : ¬(SimpleGraph.edge x y).Adj u v := by
    intro he
    rcases Sym2.eq_iff.mp ((SimpleGraph.adj_edge x y).mp he).1 with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact huv hxy
    · exact huv hxy.symm
  simpa only [SimpleGraph.sup_adj, or_iff_left hedge] using hH.2 huv

/-- Normalize the broad one-flip predicate into the three cases used by the
Section 7 proof: an internal flip (which is still a blow-up), an added cross
edge, or a removed cross edge. -/
theorem IsOneEdgeFlipFromPentagonBlowup.normalize
    (G : SimpleGraph α) (hflip : IsOneEdgeFlipFromPentagonBlowup G) :
    (∃ blob : α → Fin 5, IsPentagonBlowup G blob) ∨
    (∃ H : SimpleGraph α, ∃ blob : α → Fin 5, ∃ x y : α,
      IsPentagonBlowup H blob ∧ blob x ≠ blob y ∧ ¬H.Adj x y ∧
        G = H ⊔ SimpleGraph.edge x y) ∨
    (∃ H : SimpleGraph α, ∃ blob : α → Fin 5, ∃ x y : α,
      IsPentagonBlowup H blob ∧ blob x ≠ blob y ∧ ¬G.Adj x y ∧
        H = G ⊔ SimpleGraph.edge x y) := by
  obtain ⟨H, blob, hH, hdist⟩ := hflip
  rcases edgeFlipDistance_eq_one_iff_add_edge G H hdist with
    ⟨x, y, hxy, hxyH, hGH⟩ | ⟨x, y, hxy, hxyG, hHG⟩
  · by_cases hblob : blob x = blob y
    · left
      refine ⟨blob, ?_⟩
      rw [hGH]
      exact hH.sup_edge_same_blob hblob
    · right
      left
      exact ⟨H, blob, x, y, hH, hblob, hxyH, hGH⟩
  · by_cases hblob : blob x = blob y
    · left
      refine ⟨blob, ?_⟩
      rw [hHG] at hH
      exact hH.of_sup_edge_same_blob hblob
    · right
      right
      exact ⟨H, blob, x, y, hH, hblob, hxyG, hHG⟩

/-! ## Colour complementation -/

/-- Multiplication by two identifies the complement of the five-cycle with
the five-cycle itself. -/
def pentagonComplementLabel (i : Fin 5) : Fin 5 := i + i

theorem pentagonComplementLabel_bijective :
    Function.Bijective pentagonComplementLabel := by
  decide

def pentagonComplementEquiv : Fin 5 ≃ Fin 5 :=
  Equiv.ofBijective pentagonComplementLabel
    pentagonComplementLabel_bijective

@[simp] theorem pentagonComplementEquiv_apply (i : Fin 5) :
    pentagonComplementEquiv i = pentagonComplementLabel i := rfl

theorem pentagonComplementEquiv_cycle_adj_iff (i j : Fin 5) :
    (SimpleGraph.cycleGraph 5).Adj
        (pentagonComplementEquiv i) (pentagonComplementEquiv j) ↔
      (SimpleGraph.cycleGraph 5)ᶜ.Adj i j := by
  fin_cases i <;> fin_cases j <;> decide

/-- Swapping red and blue preserves the class of pentagon blow-ups after
multiplying all labels by two. -/
theorem IsPentagonBlowup.compl
    {H : SimpleGraph α} {blob : α → Fin 5}
    (hH : IsPentagonBlowup H blob) :
    IsPentagonBlowup Hᶜ (fun v ↦ pentagonComplementEquiv (blob v)) := by
  constructor
  · exact pentagonComplementEquiv.surjective.comp hH.1
  · intro u v huv
    have hblob : blob u ≠ blob v := fun h ↦ huv (congrArg _ h)
    have huv' : u ≠ v := fun h ↦ hblob (congrArg blob h)
    rw [SimpleGraph.compl_adj, and_iff_right huv', hH.2 hblob]
    have hcomp := pentagonComplementEquiv_cycle_adj_iff (blob u) (blob v)
    rw [SimpleGraph.compl_adj, and_iff_right hblob] at hcomp
    exact hcomp.symm

/-- Complementing a graph obtained by adjoining an absent edge turns the
operation around: the old complement is obtained by adjoining that edge to
the new complement. -/
theorem compl_eq_compl_sup_edge_of_eq_sup_edge
    {G H : SimpleGraph α} {x y : α}
    (hxyG : ¬G.Adj x y) (hHG : H = G ⊔ SimpleGraph.edge x y) :
    Gᶜ = Hᶜ ⊔ SimpleGraph.edge x y := by
  have hdis : Disjoint G (SimpleGraph.edge x y) :=
    (SimpleGraph.disjoint_edge G).2 hxyG
  have hedge : SimpleGraph.edge x y ≤ Gᶜ :=
    le_compl_iff_disjoint_left.mpr hdis
  rw [hHG, compl_sup]
  calc
    Gᶜ = Gᶜ ⊔ SimpleGraph.edge x y :=
      (sup_eq_left.mpr hedge).symm
    _ = (Gᶜ ⊓ (SimpleGraph.edge x y)ᶜ) ⊔
        SimpleGraph.edge x y := by
      rw [sup_inf_right]
      simp [sup_eq_left.mpr hedge]

/-- Exact Proposition 7.4(b) for removing a cross-blob edge.  After
complementing the two colours, removal becomes the addition of an absent
cross-blob edge; `twoColorCoveredSize_sup_edge_cross_exact` applies and the
two resulting fractional packings are swapped back. -/
theorem twoColorCoveredSize_removed_cross_edge_exact
    {G H : SimpleGraph α} {blob : α → Fin 5} {x y : α}
    (hH : IsPentagonBlowup H blob)
    (hsizes : PentagonB2Sizes
      (fun j ↦ (pentagonBlobFinset blob j).card))
    (hblob : blob x ≠ blob y) (hxyG : ¬G.Adj x y)
    (hHG : H = G ⊔ SimpleGraph.edge x y) :
    (∃ wR wB : Finset α → ℝ,
      IsFractionalPacking G wR ∧
      IsFractionalPacking Gᶜ wB ∧
      fractionalCoveredSize G wR + fractionalCoveredSize Gᶜ wB =
        3 * ((∑ j : Fin 5,
          ((pentagonBlobFinset blob j).card.choose 2 : ℕ)) + 1)) ∧
    (∀ wR wB : Finset α → ℝ,
      IsFractionalPacking G wR →
      IsFractionalPacking Gᶜ wB →
      fractionalCoveredSize G wR + fractionalCoveredSize Gᶜ wB ≤
        3 * ((∑ j : Fin 5,
          ((pentagonBlobFinset blob j).card.choose 2 : ℕ)) + 1)) := by
  let σ := pentagonComplementEquiv
  let blob' : α → Fin 5 := fun v ↦ σ (blob v)
  have hxy : x ≠ y := by
    intro h
    exact hblob (congrArg blob h)
  have hHxy : H.Adj x y := by
    rw [hHG, SimpleGraph.sup_adj, SimpleGraph.adj_edge]
    exact Or.inr ⟨rfl, hxy⟩
  have hHc : IsPentagonBlowup Hᶜ blob' := hH.compl
  have hblob' : blob' x ≠ blob' y := by
    exact σ.injective.ne hblob
  have hxyHc : ¬Hᶜ.Adj x y := by
    rw [SimpleGraph.compl_adj]
    exact fun h ↦ h.2 hHxy
  have hblobFinset (j : Fin 5) :
      pentagonBlobFinset blob' j =
        pentagonBlobFinset blob (σ.symm j) := by
    exact pentagonBlobFinset_comp_equiv blob σ j
  have hsizes' : PentagonB2Sizes
      (fun j ↦ (pentagonBlobFinset blob' j).card) := by
    have hcomp :
        (fun j ↦ (pentagonBlobFinset blob' j).card) =
          (fun j ↦ (pentagonBlobFinset blob (σ.symm j)).card) := by
      funext j
      rw [hblobFinset]
    rw [hcomp]
    exact (pentagonB2Sizes_comp_equiv_iff
      (fun j ↦ (pentagonBlobFinset blob j).card) σ.symm).2 hsizes
  have hsum :
      (∑ j : Fin 5,
          ((pentagonBlobFinset blob' j).card.choose 2 : ℕ)) =
        ∑ j : Fin 5,
          ((pentagonBlobFinset blob j).card.choose 2 : ℕ) := by
    simp_rw [hblobFinset]
    exact Equiv.sum_comp σ.symm
      (fun j ↦ ((pentagonBlobFinset blob j).card.choose 2 : ℕ))
  have hcompGraph : Gᶜ = Hᶜ ⊔ SimpleGraph.edge x y :=
    compl_eq_compl_sup_edge_of_eq_sup_edge hxyG hHG
  have h := twoColorCoveredSize_sup_edge_cross_exact
    hHc hsizes' hblob' hxyHc
  rw [← hcompGraph] at h
  simp only [compl_compl] at h
  rcases h with ⟨⟨wC, wG, hwC, hwG, hsize⟩, hupper⟩
  constructor
  · refine ⟨wG, wC, hwG, hwC, ?_⟩
    rw [add_comm]
    simpa only [hsum] using hsize
  · intro wR wB hwR hwB
    have hle := hupper wB wR hwB hwR
    rw [add_comm] at hle
    simpa only [hsum] using hle

/-- A distance-one perturbation of a `B₂` pentagon blow-up has exactly the
paper's one-flip two-colour optimum, unless the changed edge lies inside one
blob.  In that exceptional orientation the perturbed graph is itself still a
pentagon blow-up, which is the other branch used by Section 7. -/
theorem twoColorCoveredSize_oneFlip_exact_or_blowup
    {G H : SimpleGraph α} {blob : α → Fin 5}
    (hH : IsPentagonBlowup H blob)
    (hsizes : PentagonB2Sizes
      (fun j ↦ (pentagonBlobFinset blob j).card))
    (hflip : edgeFlipDistance G H = 1) :
    IsPentagonBlowup G blob ∨
      ((∃ wR wB : Finset α → ℝ,
        IsFractionalPacking G wR ∧
        IsFractionalPacking Gᶜ wB ∧
        fractionalCoveredSize G wR + fractionalCoveredSize Gᶜ wB =
          3 * ((∑ j : Fin 5,
            ((pentagonBlobFinset blob j).card.choose 2 : ℕ)) + 1)) ∧
      (∀ wR wB : Finset α → ℝ,
        IsFractionalPacking G wR →
        IsFractionalPacking Gᶜ wB →
        fractionalCoveredSize G wR + fractionalCoveredSize Gᶜ wB ≤
          3 * ((∑ j : Fin 5,
            ((pentagonBlobFinset blob j).card.choose 2 : ℕ)) + 1))) := by
  rcases edgeFlipDistance_eq_one_iff_add_edge G H hflip with
    ⟨x, y, _hxy, hxyH, hGH⟩ | ⟨x, y, _hxy, hxyG, hHG⟩
  · by_cases hblob : blob x = blob y
    · left
      rw [hGH]
      exact hH.sup_edge_same_blob hblob
    · right
      rw [hGH]
      exact twoColorCoveredSize_sup_edge_cross_exact
        hH hsizes hblob hxyH
  · by_cases hblob : blob x = blob y
    · left
      rw [hHG] at hH
      exact hH.of_sup_edge_same_blob hblob
    · right
      exact twoColorCoveredSize_removed_cross_edge_exact
        hH hsizes hblob hxyG hHG

end

end Erdos76
