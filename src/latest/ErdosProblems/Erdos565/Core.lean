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
import Mathlib.Combinatorics.SimpleGraph.Triangle.Basic
import Mathlib.Data.Real.Basic

/-! Finite packing definitions for Erdős Problem 76. -/

open Finset

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The finite set of all red or blue triangles in a two-colouring represented
by its red graph `G`. -/
def monochromaticTriangles (G : SimpleGraph α) : Finset (Finset α) :=
  G.cliqueFinset 3 ∪ Gᶜ.cliqueFinset 3

/-- Two distinct three-vertex sets are edge-disjoint exactly when they have at
most one common vertex. -/
def EdgeDisjoint (P : Finset (Finset α)) : Prop :=
  ∀ ⦃s⦄, s ∈ P → ∀ ⦃t⦄, t ∈ P → s ≠ t → #(s ∩ t) ≤ 1

/-- A selected family of pairwise edge-disjoint monochromatic triangles. -/
def IsMonochromaticPacking (G : SimpleGraph α) (P : Finset (Finset α)) : Prop :=
  P ⊆ monochromaticTriangles G ∧ EdgeDisjoint P

/-- The finite set of all monochromatic triangle packings in `G`. -/
def monochromaticPackings (G : SimpleGraph α) : Finset (Finset (Finset α)) :=
  (monochromaticTriangles G).powerset.filter (IsMonochromaticPacking G)

/-- The maximum number of pairwise edge-disjoint monochromatic triangles in
the two-colouring represented by `G`. -/
def monoPackingNumber (G : SimpleGraph α) : ℕ :=
  (monochromaticPackings G).sup Finset.card

@[simp] lemma mem_monochromaticTriangles {G : SimpleGraph α} {t : Finset α} :
    t ∈ monochromaticTriangles G ↔ G.IsNClique 3 t ∨ Gᶜ.IsNClique 3 t := by
  simp [monochromaticTriangles]

omit [Fintype α] in
lemma edgeDisjoint_iff_pairwise {P : Finset (Finset α)} :
    EdgeDisjoint P ↔
      (P : Set (Finset α)).Pairwise fun s t ↦ (s ∩ t : Set α).Subsingleton := by
  simp only [EdgeDisjoint, Set.Pairwise, Finset.card_le_one, ← Finset.coe_inter]
  rfl

lemma empty_isMonochromaticPacking (G : SimpleGraph α) :
    IsMonochromaticPacking G ∅ := by
  simp [IsMonochromaticPacking, EdgeDisjoint]

lemma monochromaticPackings_nonempty (G : SimpleGraph α) :
    (monochromaticPackings G).Nonempty := by
  refine ⟨∅, ?_⟩
  simp [monochromaticPackings, empty_isMonochromaticPacking]

lemma mem_monochromaticPackings {G : SimpleGraph α} {P : Finset (Finset α)} :
    P ∈ monochromaticPackings G ↔ IsMonochromaticPacking G P := by
  simp [monochromaticPackings, IsMonochromaticPacking]

lemma card_le_monoPackingNumber {G : SimpleGraph α} {P : Finset (Finset α)}
    (hP : IsMonochromaticPacking G P) : P.card ≤ monoPackingNumber G := by
  exact Finset.le_sup (f := Finset.card) (mem_monochromaticPackings.mpr hP)

lemma exists_max_monochromaticPacking (G : SimpleGraph α) :
    ∃ P : Finset (Finset α),
      IsMonochromaticPacking G P ∧ P.card = monoPackingNumber G := by
  obtain ⟨P, hP, hmax⟩ :=
    Finset.exists_max_image (monochromaticPackings G) Finset.card
      (monochromaticPackings_nonempty G)
  exact ⟨P, mem_monochromaticPackings.mp hP, Nat.le_antisymm
    (Finset.le_sup (f := Finset.card) hP) (Finset.sup_le fun Q hQ ↦ hmax Q hQ)⟩

omit [Fintype α] in
lemma red_blue_triangle_inter_card_le_one {G : SimpleGraph α} {s t : Finset α}
    (hs : G.IsNClique 3 s) (ht : Gᶜ.IsNClique 3 t) : #(s ∩ t) ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  rcases Finset.mem_inter.mp hx with ⟨hxs, hxt⟩
  rcases Finset.mem_inter.mp hy with ⟨hys, hyt⟩
  by_contra hxy
  have hr : G.Adj x y := hs.isClique hxs hys hxy
  have hb : Gᶜ.Adj x y := ht.isClique hxt hyt hxy
  exact ((SimpleGraph.compl_adj G x y).mp hb).2 hr

lemma red_blue_packing_disjoint {G : SimpleGraph α} {P Q : Finset (Finset α)}
    (hP : P ⊆ G.cliqueFinset 3) (hQ : Q ⊆ Gᶜ.cliqueFinset 3) :
    Disjoint P Q := by
  rw [Finset.disjoint_left]
  intro t htP htQ
  have hle := red_blue_triangle_inter_card_le_one
    (SimpleGraph.mem_cliqueFinset_iff.mp (hP htP))
    (SimpleGraph.mem_cliqueFinset_iff.mp (hQ htQ))
  have hcard : #(t ∩ t) = 3 := by
    simpa using (SimpleGraph.mem_cliqueFinset_iff.mp (hP htP)).card_eq
  omega

lemma edgeDisjoint_union_of_colors {G : SimpleGraph α} {P Q : Finset (Finset α)}
    (hPsub : P ⊆ G.cliqueFinset 3) (hQsub : Q ⊆ Gᶜ.cliqueFinset 3)
    (hPed : EdgeDisjoint P) (hQed : EdgeDisjoint Q) : EdgeDisjoint (P ∪ Q) := by
  intro s hs t ht hst
  simp only [mem_union] at hs ht
  rcases hs with hsP | hsQ <;> rcases ht with htP | htQ
  · exact hPed hsP htP hst
  · exact red_blue_triangle_inter_card_le_one
      (SimpleGraph.mem_cliqueFinset_iff.mp (hPsub hsP))
      (SimpleGraph.mem_cliqueFinset_iff.mp (hQsub htQ))
  · simpa [Finset.inter_comm] using red_blue_triangle_inter_card_le_one
      (SimpleGraph.mem_cliqueFinset_iff.mp (hPsub htP))
      (SimpleGraph.mem_cliqueFinset_iff.mp (hQsub hsQ))
  · exact hQed hsQ htQ hst

lemma union_isMonochromaticPacking {G : SimpleGraph α} {P Q : Finset (Finset α)}
    (hPsub : P ⊆ G.cliqueFinset 3) (hQsub : Q ⊆ Gᶜ.cliqueFinset 3)
    (hPed : EdgeDisjoint P) (hQed : EdgeDisjoint Q) :
    IsMonochromaticPacking G (P ∪ Q) := by
  constructor
  · intro t ht
    rcases mem_union.mp ht with htP | htQ
    · exact mem_union_left _ (hPsub htP)
    · exact mem_union_right _ (hQsub htQ)
  · exact edgeDisjoint_union_of_colors hPsub hQsub hPed hQed

lemma add_card_le_monoPackingNumber {G : SimpleGraph α} {P Q : Finset (Finset α)}
    (hPsub : P ⊆ G.cliqueFinset 3) (hQsub : Q ⊆ Gᶜ.cliqueFinset 3)
    (hPed : EdgeDisjoint P) (hQed : EdgeDisjoint Q) :
    P.card + Q.card ≤ monoPackingNumber G := by
  rw [← card_union_of_disjoint (red_blue_packing_disjoint hPsub hQsub)]
  exact card_le_monoPackingNumber
    (union_isMonochromaticPacking hPsub hQsub hPed hQed)

/-- Proposition-level variant of `add_card_le_monoPackingNumber`.  This form is
the interface used by the asymptotic rounding theorem: unlike a literal
subset of `cliqueFinset`, it does not expose the implementation's classical
decidability witness in the theorem type. -/
lemma add_card_le_monoPackingNumber_of_isNClique
    {G : SimpleGraph α} {P Q : Finset (Finset α)}
    (hP : ∀ t ∈ P, G.IsNClique 3 t)
    (hQ : ∀ t ∈ Q, Gᶜ.IsNClique 3 t)
    (hPed : EdgeDisjoint P) (hQed : EdgeDisjoint Q) :
    P.card + Q.card ≤ monoPackingNumber G := by
  apply add_card_le_monoPackingNumber (hPed := hPed) (hQed := hQed)
  · intro t ht
    exact SimpleGraph.mem_cliqueFinset_iff.mpr (hP t ht)
  · intro t ht
    exact SimpleGraph.mem_cliqueFinset_iff.mpr (hQ t ht)

end

end Erdos76
