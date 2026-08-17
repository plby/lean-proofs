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
module

public import Mathlib.Data.Fintype.Powerset
public import ErdosProblems.Erdos565.Hypergraph

/-!
# Structural invariants for the Campos--Samotij update

The deterministic container algorithm repeatedly replaces a finite family
`H` by

`(H \ F.upClosure) ∪ F`.

Thus all old edges containing a new edge are deleted before the new family is
inserted.  This file proves the finite structural facts used by the algorithm:
the generated up-set grows, antichains and input-independence are preserved,
and the link of a uniform layer has the expected rank.  No quantitative weight
assumption is used here.
-/

@[expose] public section

namespace Erdos565
namespace Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- No two edges of `H` properly contain one another. -/
def IsAntichain (H : Hypergraph V) : Prop :=
  ∀ ⦃A⦄, A ∈ H → ∀ ⦃B⦄, B ∈ H → A ⊆ B → A = B

/-- Every edge in `H` is nonempty. -/
def HasNonemptyEdges (H : Hypergraph V) : Prop :=
  ∀ ⦃A⦄, A ∈ H → A.Nonempty

/-- The vertices which are not forbidden by a singleton edge. -/
def containerVertices (H : Hypergraph V) : Finset V :=
  Finset.univ.filter fun v => ({v} : Finset V) ∉ H

/-- The layer consisting of edges with at least two vertices. -/
def aboveOne (H : Hypergraph V) : Hypergraph V :=
  H.filter fun e => 2 ≤ e.card

/-- Delete all old edges containing a member of `F`, then insert `F`. -/
def update (H F : Hypergraph V) : Hypergraph V :=
  (H \ F.upClosure) ∪ F

/-- The finite rank used to prove termination of the update algorithm. -/
def upRank (H : Hypergraph V) : ℕ :=
  H.upClosure.card

@[simp] theorem mem_containerVertices {H : Hypergraph V} {v : V} :
    v ∈ H.containerVertices ↔ ({v} : Finset V) ∉ H := by
  simp [containerVertices]

@[simp] theorem mem_aboveOne {H : Hypergraph V} {e : Finset V} :
    e ∈ H.aboveOne ↔ e ∈ H ∧ 2 ≤ e.card := by
  simp [aboveOne]

@[simp] theorem mem_update {H F : Hypergraph V} {e : Finset V} :
    e ∈ H.update F ↔ (e ∈ H ∧ e ∉ F.upClosure) ∨ e ∈ F := by
  simp [update]

/-- Filter presentation used by the executable container state machine. -/
theorem update_eq_filter_union (H F : Hypergraph V) :
    H.update F = (H.filter fun E => ¬ ∃ A ∈ F, A ⊆ E) ∪ F := by
  ext E
  simp [update]

theorem IsUniform.isAntichain {H : Hypergraph V} {s : ℕ}
    (hH : H.IsUniform s) : H.IsAntichain := by
  intro A hAH B hBH hAB
  exact hH.subset_card_eq hAH hBH hAB

theorem IsAntichain.subset_card_eq {H : Hypergraph V} (hH : H.IsAntichain)
    {A B : Finset V} (hAH : A ∈ H) (hBH : B ∈ H) (hAB : A ⊆ B) : A = B :=
  hH hAH hBH hAB

/-- A proper subset of an edge of an antichain lies outside its generated
up-set. -/
theorem IsAntichain.ssubset_not_mem_upClosure {H : Hypergraph V}
    (hH : H.IsAntichain) {A E : Finset V} (hEH : E ∈ H) (hAE : A ⊂ E) :
    A ∉ H.upClosure := by
  intro hA
  obtain ⟨D, hDH, hDA⟩ := mem_upClosure.mp hA
  have hDE : D ⊆ E := hDA.trans hAE.1
  have hEq : D = E := hH hDH hEH hDE
  exact hAE.2 (hEq ▸ hDA)

/-- An update never loses any set in the old generated up-set. -/
theorem upClosure_subset_update (H F : Hypergraph V) :
    H.upClosure ⊆ (H.update F).upClosure := by
  intro A hA
  obtain ⟨E, hEH, hEA⟩ := mem_upClosure.mp hA
  by_cases hEF : E ∈ F.upClosure
  · obtain ⟨B, hBF, hBE⟩ := mem_upClosure.mp hEF
    exact mem_upClosure.mpr ⟨B, mem_update.mpr (Or.inr hBF), hBE.trans hEA⟩
  · exact mem_upClosure.mpr ⟨E, mem_update.mpr (Or.inl ⟨hEH, hEF⟩), hEA⟩

theorem mem_upClosure_update_of_mem {H F : Hypergraph V} {A : Finset V}
    (hAF : A ∈ F) : A ∈ (H.update F).upClosure := by
  exact mem_upClosure.mpr ⟨A, mem_update.mpr (Or.inr hAF), Finset.Subset.rfl⟩

/-- Inserting one edge outside the old up-set makes the generated up-set
strictly larger. -/
theorem upClosure_ssubset_update {H F : Hypergraph V}
    (hnew : ∃ A ∈ F, A ∉ H.upClosure) :
    H.upClosure ⊂ (H.update F).upClosure := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨upClosure_subset_update H F, ?_⟩
  obtain ⟨A, hAF, hAold⟩ := hnew
  intro heq
  exact hAold (heq ▸ mem_upClosure_update_of_mem hAF)

theorem upRank_lt_update {H F : Hypergraph V}
    (hnew : ∃ A ∈ F, A ∉ H.upClosure) :
    H.upRank < (H.update F).upRank := by
  exact Finset.card_lt_card (upClosure_ssubset_update hnew)

theorem upRank_le_two_pow (H : Hypergraph V) :
    H.upRank ≤ 2 ^ Fintype.card V := by
  simpa [upRank, Fintype.card_finset] using
    (Finset.card_le_card (Finset.subset_univ H.upClosure))

/-- The exact antichain invariant for a replacement step.  The hypothesis
`houtside` is essential in the old-edge/new-edge orientation. -/
theorem IsAntichain.update {H F : Hypergraph V}
    (hH : H.IsAntichain) (hF : F.IsAntichain)
    (houtside : ∀ ⦃A⦄, A ∈ F → A ∉ H.upClosure) :
    (H.update F).IsAntichain := by
  intro A hA B hB hAB
  rw [mem_update] at hA hB
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · exact hH hA.1 hB.1 hAB
  · exfalso
    exact (houtside hB) (mem_upClosure.mpr ⟨A, hA.1, hAB⟩)
  · exfalso
    exact hB.2 (mem_upClosure.mpr ⟨A, hA, hAB⟩)
  · exact hF hA hB hAB

theorem HasNonemptyEdges.update {H F : Hypergraph V}
    (hH : H.HasNonemptyEdges) (hF : F.HasNonemptyEdges) :
    (H.update F).HasNonemptyEdges := by
  intro E hE
  rw [mem_update] at hE
  exact hE.elim (fun h => hH h.1) (fun h => hF h)

theorem IsBounded.update {H F : Hypergraph V} {s : ℕ}
    (hH : H.IsBounded s) (hF : F.IsBounded s) :
    (H.update F).IsBounded s := by
  intro E hE
  rw [mem_update] at hE
  exact hE.elim (fun h => hH E h.1) (fun h => hF E h)

theorem IsIndependent.update {H F : Hypergraph V} {I : Finset V}
    (hH : H.IsIndependent I) (hF : F.IsIndependent I) :
    (H.update F).IsIndependent I := by
  intro E hE
  rw [mem_update] at hE
  exact hE.elim (fun h => hH E h.1) (fun h => hF E h)

theorem isIndependent_singleton {L I : Finset V} (hLI : ¬ L ⊆ I) :
    (singleton L : Hypergraph V).IsIndependent I := by
  intro E hE
  have hEL : E = L := by simpa using hE
  subst E
  exact hLI

/-- If the seed is contained in an independent input, then the corresponding
link is independent as well. -/
theorem IsIndependent.link_of_subset {H : Hypergraph V} {I L : Finset V}
    (hI : H.IsIndependent I) (hLI : L ⊆ I) :
    (H.link L).IsIndependent I := by
  intro F hF hFI
  obtain ⟨E, hEH, hLE, rfl⟩ := mem_link.mp hF
  apply hI E hEH
  intro x hxE
  by_cases hxL : x ∈ L
  · exact hLI hxL
  · exact hFI (Finset.mem_sdiff.mpr ⟨hxE, hxL⟩)

/-- Every independent input is contained in the current container vertex
set. -/
theorem IsIndependent.subset_containerVertices {H : Hypergraph V} {I : Finset V}
    (hI : H.IsIndependent I) : I ⊆ H.containerVertices := by
  intro v hvI
  rw [mem_containerVertices]
  intro hsv
  exact hI {v} hsv (by simpa using hvI)

/-- Every edge of size at least two in an antichain is supported on the
container vertices. -/
theorem IsAntichain.aboveOne_subset_containerVertices {H : Hypergraph V}
    (hH : H.IsAntichain) :
    ∀ ⦃E⦄, E ∈ H.aboveOne → E ⊆ H.containerVertices := by
  intro E hE v hvE
  obtain ⟨hEH, hcard⟩ := mem_aboveOne.mp hE
  rw [mem_containerVertices]
  intro hsv
  have heq : ({v} : Finset V) = E := hH hsv hEH (by simpa using hvE)
  have : E.card = 1 := by simpa [← heq]
  omega

/-- If the generated up-set of `H₀` is contained in that of `H`, then the
non-singleton edges of `H` cover every old edge supported on the current
container. -/
theorem cover_restrict_by_aboveOne {H₀ H : Hypergraph V}
    (hup : H₀.upClosure ⊆ H.upClosure) (hne : H.HasNonemptyEdges) :
    H.aboveOne.Covers (H₀.restrict H.containerVertices) := by
  intro E hE
  have hEH₀ : E ∈ H₀ := (mem_restrict.mp hE).1
  have hEC : E ⊆ H.containerVertices := (mem_restrict.mp hE).2
  have hEup₀ : E ∈ H₀.upClosure :=
    mem_upClosure.mpr ⟨E, hEH₀, Finset.Subset.rfl⟩
  obtain ⟨L, hLH, hLE⟩ := mem_upClosure.mp (hup hEup₀)
  have hLcard : 2 ≤ L.card := by
    have hpos : 0 < L.card := Finset.card_pos.mpr (hne hLH)
    have hneone : L.card ≠ 1 := by
      intro hcard
      obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hcard
      have hvE : v ∈ E := hLE (by simp)
      exact (mem_containerVertices.mp (hEC hvE)) hLH
    omega
  exact ⟨L, mem_aboveOne.mpr ⟨hLH, hLcard⟩, hLE⟩

/-! ## Uniform layers and links -/

theorem link_layer_isUniform (H : Hypergraph V) (a : ℕ) (L : Finset V) :
    (H.layer a).link L |>.IsUniform (a - L.card) := by
  intro F hF
  obtain ⟨E, hE, hLE, rfl⟩ := mem_link.mp hF
  rw [Finset.card_sdiff_of_subset hLE, (mem_layer.mp hE).2]

theorem link_layer_isAntichain (H : Hypergraph V) (a : ℕ) (L : Finset V) :
    ((H.layer a).link L).IsAntichain :=
  (link_layer_isUniform H a L).isAntichain

theorem link_layer_hasNonemptyEdges {H : Hypergraph V} {a : ℕ} {L : Finset V}
    (hLnot : L ∉ H) : ((H.layer a).link L).HasNonemptyEdges := by
  intro F hF
  obtain ⟨E, hE, hLE, rfl⟩ := mem_link.mp hF
  rw [Finset.sdiff_nonempty]
  intro hEL
  have hEq : E = L := Finset.Subset.antisymm hEL hLE
  exact hLnot (hEq ▸ (mem_layer.mp hE).1)

/-- A link edge at a nonempty seed is a proper subset of the old edge which
generated it. -/
theorem link_layer_edge_ssubset {H : Hypergraph V} {a : ℕ} {L F : Finset V}
    (hL : L.Nonempty) (hF : F ∈ (H.layer a).link L) :
    ∃ E ∈ H, F ⊂ E := by
  obtain ⟨E, hE, hLE, rfl⟩ := mem_link.mp hF
  refine ⟨E, (mem_layer.mp hE).1,
    Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, ?_⟩⟩
  intro hEq
  obtain ⟨v, hvL⟩ := hL
  have hvE : v ∈ E := hLE hvL
  have hvDiff : v ∈ E \ L := hEq.symm ▸ hvE
  exact (Finset.mem_sdiff.mp hvDiff).2 hvL

theorem IsAntichain.link_layer_outside_upClosure {H : Hypergraph V} {a : ℕ}
    {L : Finset V} (hH : H.IsAntichain) (hL : L.Nonempty) :
    ∀ ⦃F⦄, F ∈ (H.layer a).link L → F ∉ H.upClosure := by
  intro F hF
  obtain ⟨E, hEH, hFE⟩ := link_layer_edge_ssubset hL hF
  exact hH.ssubset_not_mem_upClosure hEH hFE

/-- The seed itself lies outside the current up-set whenever it extends to a
current edge but is not itself a current edge. -/
theorem IsAntichain.seed_outside_upClosure {H : Hypergraph V} {a : ℕ}
    {L : Finset V} (hH : H.IsAntichain) (hLnot : L ∉ H)
    (hext : ∃ E ∈ H.layer a, L ⊆ E) : L ∉ H.upClosure := by
  obtain ⟨E, hE, hLE⟩ := hext
  have hne : L ≠ E := by
    intro hEq
    exact hLnot (hEq ▸ (mem_layer.mp hE).1)
  exact hH.ssubset_not_mem_upClosure (mem_layer.mp hE).1
    (Finset.ssubset_iff_subset_ne.mpr ⟨hLE, hne⟩)

theorem seed_card_lt_layer {H : Hypergraph V} {a : ℕ} {L : Finset V}
    (hext : ∃ E ∈ H.layer a, L ⊆ E) (hLnot : L ∉ H) : L.card < a := by
  obtain ⟨E, hE, hLE⟩ := hext
  have hproper : L ⊂ E := Finset.ssubset_iff_subset_ne.mpr ⟨hLE, by
    intro hEq
    exact hLnot (hEq ▸ (mem_layer.mp hE).1)⟩
  simpa [(mem_layer.mp hE).2] using Finset.card_lt_card hproper

/-- Links compose by taking the union of disjoint seeds.  This is the exact
identity used in the maximal-seed proof for a positive update. -/
theorem link_link_of_disjoint (H : Hypergraph V) {A B : Finset V}
    (hAB : Disjoint A B) :
    (H.link A).link B = H.link (A ∪ B) := by
  ext t
  constructor
  · intro ht
    obtain ⟨g, hg, hBg, hgt⟩ := mem_link.mp ht
    obtain ⟨e, he, hAe, heg⟩ := mem_link.mp hg
    refine mem_link.mpr ⟨e, he, ?_, ?_⟩
    · exact Finset.union_subset hAe (hBg.trans (heg ▸ Finset.sdiff_subset))
    · subst g
      simpa only [sdiff_sdiff, Finset.sup_eq_union] using hgt
  · intro ht
    obtain ⟨e, he, hABe, het⟩ := mem_link.mp ht
    have hAe : A ⊆ e := Finset.subset_union_left.trans hABe
    have hBe : B ⊆ e := Finset.subset_union_right.trans hABe
    have hBdiff : B ⊆ e \ A := by
      intro x hxB
      exact Finset.mem_sdiff.mpr
        ⟨hBe hxB, fun hxA => (Finset.disjoint_left.mp hAB) hxA hxB⟩
    refine mem_link.mpr ⟨e \ A, mem_link.mpr ⟨e, he, hAe, rfl⟩, hBdiff, ?_⟩
    simpa only [sdiff_sdiff, Finset.sup_eq_union] using het

theorem link_singleton_of_subset {E L : Finset V} (hLE : L ⊆ E) :
    (({E} : Hypergraph V).link L) = {E \ L} := by
  ext t
  simp only [mem_link, Finset.mem_singleton]
  constructor
  · rintro ⟨D, rfl, _, rfl⟩
    rfl
  · rintro rfl
    exact ⟨E, rfl, hLE, rfl⟩

theorem link_singleton_of_not_subset {E L : Finset V} (hLE : ¬ L ⊆ E) :
    (({E} : Hypergraph V).link L) = ∅ := by
  ext t
  simp [mem_link, hLE]

/-- The number of strict update rounds is bounded by the number of subsets of
the vertex type. -/
theorem strict_upRank_chain_length_le {f : ℕ → Hypergraph V} {k : ℕ}
    (hstep : ∀ i < k, (f i).upRank < (f (i + 1)).upRank) :
    k ≤ 2 ^ Fintype.card V := by
  have hsum : (f 0).upRank + k ≤ (f k).upRank := by
    induction k with
    | zero => simp
    | succ k ih =>
        have ih' : (f 0).upRank + k ≤ (f k).upRank :=
          ih (fun i hi => hstep i (hi.trans (Nat.lt_succ_self k)))
        have hk : (f k).upRank < (f (k + 1)).upRank :=
          hstep k (Nat.lt_succ_self k)
        omega
  have hbound := upRank_le_two_pow (f k)
  omega

end Hypergraph
end Erdos565
