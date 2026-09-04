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

import ErdosProblems.Erdos735.CyclicPacking
import ErdosProblems.Erdos735.Discharging3

/-!
# Point-level packing for the third ABKPR discharging step

This file replaces the numerical donation and pentagon assumptions by an
explicit injection of donations into free boundary edges and vertices.  All
cardinality estimates and all four pentagon clauses are then finite cyclic
consequences.  The only remaining triangle input is the geometric
one-bad-quadrangle lemma.
-/

namespace Erdos735
namespace ABKPR

open scoped BigOperators

theorem exists_cyclic_predecessor {n : ℕ} (hn : 0 < n) (v : Fin n) :
    ∃ i, cyclicSucc hn i = v := by
  by_cases hv : v.val = 0
  · let i : Fin n := ⟨n - 1, by omega⟩
    refine ⟨i, ?_⟩
    apply Fin.ext
    simp only [cyclicSucc, i]
    have hi : n - 1 + 1 = n := by omega
    rw [hi, Nat.mod_self, hv]
  · let i : Fin n := ⟨v.val - 1, by omega⟩
    refine ⟨i, ?_⟩
    apply Fin.ext
    simp only [cyclicSucc, i]
    rw [Nat.mod_eq_of_lt]
    · omega
    · omega

theorem fin_five_nonadjacent_freeEdges_card
    (a b : Fin 5) (hab : a ≠ b)
    (hba : b ≠ cyclicSucc (by decide) a)
    (hab' : a ≠ cyclicSucc (by decide) b) :
    (Finset.univ.filter fun i : Fin 5 ↦
      i ∉ ({a, b} : Finset (Fin 5)) ∧
        cyclicSucc (by decide) i ∉ ({a, b} : Finset (Fin 5))).card = 1 := by
  fin_cases a <;> fin_cases b
  all_goals norm_num [cyclicSucc] at *
  all_goals decide

theorem fin_five_independent_card_le_two (S : Finset (Fin 5))
    (hind : ∀ i, i ∈ S → cyclicSucc (by decide) i ∉ S) :
    S.card ≤ 2 := by
  have hsubset_two (a b : Fin 5) (hsub : S ⊆ {a, b}) : S.card ≤ 2 := by
    have h := Finset.card_le_card hsub
    have hab := Finset.card_insert_le a ({b} : Finset (Fin 5))
    simp only [Finset.card_singleton] at hab
    omega
  by_cases h0 : (0 : Fin 5) ∈ S
  · have h1 : (1 : Fin 5) ∉ S := by simpa [cyclicSucc] using hind 0 h0
    have h4 : (4 : Fin 5) ∉ S := by
      intro h4
      apply hind 4 h4
      simpa [cyclicSucc] using h0
    by_cases h2 : (2 : Fin 5) ∈ S
    · have h3 : (3 : Fin 5) ∉ S := by simpa [cyclicSucc] using hind 2 h2
      apply hsubset_two 0 2
      intro i hi
      fin_cases i <;> simp_all
    · apply hsubset_two 0 3
      intro i hi
      fin_cases i <;> simp_all
  · by_cases h1 : (1 : Fin 5) ∈ S
    · have h2 : (2 : Fin 5) ∉ S := by simpa [cyclicSucc] using hind 1 h1
      by_cases h3 : (3 : Fin 5) ∈ S
      · have h4 : (4 : Fin 5) ∉ S := by simpa [cyclicSucc] using hind 3 h3
        apply hsubset_two 1 3
        intro i hi
        fin_cases i <;> simp_all
      · apply hsubset_two 1 4
        intro i hi
        fin_cases i <;> simp_all
    · by_cases h2 : (2 : Fin 5) ∈ S
      · have h3 : (3 : Fin 5) ∉ S := by simpa [cyclicSucc] using hind 2 h2
        apply hsubset_two 2 4
        intro i hi
        fin_cases i <;> simp_all
      · by_cases h3 : (3 : Fin 5) ∈ S
        · have h4 : (4 : Fin 5) ∉ S := by simpa [cyclicSucc] using hind 3 h3
          apply hsubset_two 3 3
          intro i hi
          fin_cases i <;> simp_all
        · apply hsubset_two 4 4
          intro i hi
          fin_cases i <;> simp_all

namespace Data

universe uV uE uF

variable {Vertex : Type uV} {Edge : Type uE} {Face : Type uF}
variable [Fintype Vertex] [Fintype Edge] [Fintype Face]
variable [DecidableEq Vertex] [DecidableEq Edge] [DecidableEq Face]
variable {C : BlueCellulation Vertex Edge Face}
variable (A : ABKPR.Data C)

def freeEdgeIndices (f : Face) : Finset (Fin (C.faceDegree f)) :=
  Finset.univ.filter fun i ↦
    i ∉ A.redEndpoints f ∧ faceSucc C f i ∉ A.redEndpoints f

lemma badNeighborIndices_subset_freeEdgeIndices
    (hrest : A.EndpointRestriction) (f : Face) :
    A.badNeighborIndices f ⊆ A.freeEdgeIndices f := by
  intro i hi
  have hbad := (Finset.mem_filter.mp hi).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrest f i hbad⟩

lemma freeEdgeIndices_card_le_freeVertices (f : Face) :
    (A.freeEdgeIndices f).card ≤
      (Finset.univ \ A.redEndpoints f).card := by
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2.1⟩

/-- Point-level geometric input for Stage 3.  Donations are represented by
distinct free boundary edges and distinct boundary vertices.  The last
field is the local consequence of the one-bad-quadrangle-per-triangle
lemma at a donation vertex. -/
structure DonationPacking where
  donationEdge : ∀ f, A.donationRecipients f → Fin (C.faceDegree f)
  donationEdge_injective : ∀ f, Function.Injective (donationEdge f)
  donationEdge_free : ∀ f d, donationEdge f d ∈ A.freeEdgeIndices f
  donationVertex : ∀ f, A.donationRecipients f → Fin (C.faceDegree f)
  donationVertex_injective : ∀ f, Function.Injective (donationVertex f)
  no_two_bad_at_donation : ∀ f d i,
    donationVertex f d = faceSucc C f i →
      i ∈ A.badNeighborIndices f →
      faceSucc C f i ∈ A.badNeighborIndices f → False

namespace DonationPacking

variable (P : A.DonationPacking)

include P

lemma donationRecipients_card_le_freeEdgeIndices (f : Face) :
    (A.donationRecipients f).card ≤ (A.freeEdgeIndices f).card := by
  let map : A.donationRecipients f → A.freeEdgeIndices f :=
    fun d ↦ ⟨P.donationEdge f d, P.donationEdge_free f d⟩
  have hinj : Function.Injective map := by
    intro d e h
    apply P.donationEdge_injective f
    exact congrArg Subtype.val h
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective map hinj

lemma donation_count_bound (f : Face) :
    (A.donationRecipients f).card + 2 * (A.redChords f).card ≤
      C.faceDegree f := by
  have hd := donationRecipients_card_le_freeEdgeIndices A P f
  have hf := A.freeEdgeIndices_card_le_freeVertices f
  have hpartition := Finset.card_sdiff_add_card
    (Finset.univ : Finset (Fin (C.faceDegree f))) (A.redEndpoints f)
  have hunion : (Finset.univ : Finset (Fin (C.faceDegree f))) ∪
      A.redEndpoints f = Finset.univ :=
    Finset.union_eq_left.mpr (Finset.subset_univ _)
  rw [hunion] at hpartition
  have hpartition' :
      (Finset.univ \ A.redEndpoints f).card + (A.redEndpoints f).card =
        C.faceDegree f := by
    simpa [Fintype.card_fin] using hpartition
  rw [A.redEndpoints_card] at hpartition'
  omega

omit P in
lemma freeEdgeIndices_card_eq_one_of_pentagon_oneChord {f : Face}
    (hf : C.faceDegree f = 5) (hr : (A.redChords f).card = 1) :
    (A.freeEdgeIndices f).card = 1 := by
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hr
  have hpmem : p ∈ A.redChords f := by rw [hp]; simp
  have hend : A.redEndpoints f = {p.1, p.2} := by
    ext x
    simp [A.redEndpoint_iff, hp]
  let cast : Fin (C.faceDegree f) → Fin 5 := Fin.cast hf
  have cast_injective : Function.Injective cast := Fin.cast_injective hf
  have cast_succ (j : Fin (C.faceDegree f)) :
      cast (faceSucc C f j) = cyclicSucc (by decide) (cast j) := by
    apply Fin.ext
    simp [cast, faceSucc, cyclicSucc, hf]
  let S : Finset (Fin 5) := Finset.univ.filter fun i ↦
    i ∉ ({cast p.1, cast p.2} : Finset (Fin 5)) ∧
      cyclicSucc (by decide) i ∉ ({cast p.1, cast p.2} : Finset (Fin 5))
  have hmem (i : Fin (C.faceDegree f)) :
      i ∈ A.freeEdgeIndices f ↔ cast i ∈ S := by
    simp only [freeEdgeIndices, Finset.mem_filter, Finset.mem_univ, true_and, S]
    rw [hend]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · rintro ⟨⟨hi1, hi2⟩, hs1, hs2⟩
      exact ⟨⟨fun h ↦ hi1 (cast_injective h),
        fun h ↦ hi2 (cast_injective h)⟩,
        fun h ↦ hs1 (cast_injective ((cast_succ i).trans h)),
        fun h ↦ hs2 (cast_injective ((cast_succ i).trans h))⟩
    · rintro ⟨⟨hi1, hi2⟩, hs1, hs2⟩
      exact ⟨⟨fun h ↦ hi1 (congrArg cast h),
        fun h ↦ hi2 (congrArg cast h)⟩,
        fun h ↦ hs1 ((cast_succ i).symm.trans (congrArg cast h)),
        fun h ↦ hs2 ((cast_succ i).symm.trans (congrArg cast h))⟩
  let E : A.freeEdgeIndices f ≃ S :=
    Equiv.subtypeEquiv (finCongr hf) hmem
  have hS : S.card = 1 := by
    apply fin_five_nonadjacent_freeEdges_card
    · exact fun h ↦ A.redChord_distinct f p hpmem (cast_injective h)
    · intro h
      apply (A.redChord_nonadjacent f p hpmem).1
      apply cast_injective
      rw [cast_succ]
      exact h
    · intro h
      apply (A.redChord_nonadjacent f p hpmem).2
      apply cast_injective
      rw [cast_succ]
      exact h
  calc
    (A.freeEdgeIndices f).card = S.card := by
      simpa only [Fintype.card_coe] using Fintype.card_congr E
    _ = 1 := hS

omit P in
lemma freeEdgeIndices_eq_empty_of_pentagon_twoChords {f : Face}
    (hf : C.faceDegree f = 5) (hr : (A.redChords f).card = 2) :
    A.freeEdgeIndices f = ∅ := by
  have hfreecard : (Finset.univ \ A.redEndpoints f).card = 1 := by
    rw [Finset.card_sdiff]
    simp only [Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hf,
      A.redEndpoints_card, hr]
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨i, hi⟩
  have hparts := (Finset.mem_filter.mp hi).2
  have hsucc_ne : faceSucc C f i ≠ i := by
    intro h
    have hval := congrArg Fin.val h
    simp only [faceSucc, cyclicSucc] at hval
    simp only [hf] at hval
    omega
  have hpair : ({i, faceSucc C f i} : Finset (Fin (C.faceDegree f))).card = 2 := by
    simp [hsucc_ne.symm]
  have hsub : ({i, faceSucc C f i} : Finset (Fin (C.faceDegree f))) ⊆
      Finset.univ \ A.redEndpoints f := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hparts.1⟩
    · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hparts.2⟩
  have hc := Finset.card_le_card hsub
  rw [hpair, hfreecard] at hc
  omega

lemma pentagon_twoChords
    (hrest : A.EndpointRestriction) {f : Face}
    (hf : C.faceDegree f = 5) (hr : (A.redChords f).card = 2) :
    A.badNeighborCount f = 0 ∧ (A.donationRecipients f).card = 0 := by
  have hfree := freeEdgeIndices_eq_empty_of_pentagon_twoChords A hf hr
  constructor
  · apply Finset.card_eq_zero.mpr
    apply Finset.Subset.antisymm
    · simpa [hfree] using A.badNeighborIndices_subset_freeEdgeIndices hrest f
    · exact Finset.empty_subset _
  · have hd := donationRecipients_card_le_freeEdgeIndices A P f
    rw [hfree] at hd
    simpa using hd

lemma pentagon_oneChord
    (hrest : A.EndpointRestriction) {f : Face}
    (hf : C.faceDegree f = 5) (hr : (A.redChords f).card = 1) :
    A.badNeighborCount f ≤ 1 ∧ (A.donationRecipients f).card ≤ 1 := by
  have hfree := freeEdgeIndices_card_eq_one_of_pentagon_oneChord A hf hr
  constructor
  · have hb := Finset.card_le_card
      (A.badNeighborIndices_subset_freeEdgeIndices hrest f)
    simpa [badNeighborCount, hfree] using hb
  · have hd := donationRecipients_card_le_freeEdgeIndices A P f
    simpa [hfree] using hd

lemma pentagon_noChord_allBad
    (_hrest : A.EndpointRestriction) {f : Face}
    (hf : C.faceDegree f = 5) (_hr : (A.redChords f).card = 0)
    (hbad : A.badNeighborCount f = 5) :
    (A.donationRecipients f).card = 0 := by
  have hbad_univ : A.badNeighborIndices f = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simpa [badNeighborCount, Fintype.card_fin, hf] using hbad.symm.le
  apply Finset.card_eq_zero.mpr
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨t, ht⟩
  let d : A.donationRecipients f := ⟨t, ht⟩
  obtain ⟨i, hi⟩ := exists_cyclic_predecessor
    (ABKPR.faceDegree_pos C f) (P.donationVertex f d)
  apply P.no_two_bad_at_donation f d i hi.symm
  · rw [hbad_univ]
    exact Finset.mem_univ _
  · rw [hbad_univ]
    exact Finset.mem_univ _

lemma pentagon_noChord_allDonate
    {f : Face} (hf : C.faceDegree f = 5)
    (_hr : (A.redChords f).card = 0)
    (hdonate : (A.donationRecipients f).card = 5) :
    A.badNeighborCount f ≤ 2 := by
  have hcard : Fintype.card (A.donationRecipients f) =
      Fintype.card (Fin (C.faceDegree f)) := by
    simpa only [Fintype.card_coe, Fintype.card_fin, hf] using hdonate
  have hsurj : Function.Surjective (P.donationVertex f) :=
    ((Fintype.bijective_iff_injective_and_card (P.donationVertex f)).mpr
      ⟨P.donationVertex_injective f, hcard⟩).2
  have hind : ∀ i, i ∈ A.badNeighborIndices f →
      faceSucc C f i ∉ A.badNeighborIndices f := by
    intro i hi hsucc
    obtain ⟨d, hd⟩ := hsurj (faceSucc C f i)
    exact P.no_two_bad_at_donation f d i hd hi hsucc
  let cast : Fin (C.faceDegree f) → Fin 5 := Fin.cast hf
  have cast_injective : Function.Injective cast := Fin.cast_injective hf
  have cast_succ (j : Fin (C.faceDegree f)) :
      cast (faceSucc C f j) = cyclicSucc (by decide) (cast j) := by
    apply Fin.ext
    simp [cast, faceSucc, cyclicSucc, hf]
  let S : Finset (Fin 5) :=
    (A.badNeighborIndices f).map (finCongr hf).toEmbedding
  have hScard : S.card = (A.badNeighborIndices f).card := by
    simp [S]
  have hSind : ∀ j, j ∈ S → cyclicSucc (by decide) j ∉ S := by
    intro j hj hsj
    rcases Finset.mem_map.mp hj with ⟨i, hi, hij⟩
    rcases Finset.mem_map.mp hsj with ⟨k, hk, hkj⟩
    have hik : faceSucc C f i = k := by
      apply cast_injective
      calc
        cast (faceSucc C f i) = cyclicSucc (by decide) (cast i) := cast_succ i
        _ = cyclicSucc (by decide) j := congrArg (cyclicSucc (by decide)) hij
        _ = cast k := hkj.symm
    exact hind i hi (hik ▸ hk)
  have hSle := fin_five_independent_card_le_two S hSind
  simpa [badNeighborCount, hScard] using hSle

end DonationPacking

/-- Exact residual geometric input after all finite cyclic packing and
pentagon arithmetic have been discharged. -/
structure ReducedStage3Geometry where
  oneBadQuadranglePerTriangle : ∀ t,
    C.faceDegree t = 3 → A.badNeighborCount t ≤ 1
  donationPacking : A.DonationPacking

namespace ReducedStage3Geometry

/-- The reduced point-level geometry implies every field of the original
Stage-3 hypothesis package. -/
theorem toStage3Hypotheses (G : A.ReducedStage3Geometry)
    (hrest : A.EndpointRestriction) : A.Stage3Hypotheses where
  oneBadQuadranglePerTriangle := G.oneBadQuadranglePerTriangle
  donation_count_bound := DonationPacking.donation_count_bound A G.donationPacking
  pentagon_twoChords := by
    intro f hf hr
    exact DonationPacking.pentagon_twoChords A G.donationPacking hrest hf hr
  pentagon_oneChord := by
    intro f hf hr
    exact DonationPacking.pentagon_oneChord A G.donationPacking hrest hf hr
  pentagon_noChord_allBad := by
    intro f hf hr hb
    exact DonationPacking.pentagon_noChord_allBad A G.donationPacking hrest hf hr hb
  pentagon_noChord_allDonate := by
    intro f hf hr hd
    exact DonationPacking.pentagon_noChord_allDonate A G.donationPacking hf hr hd

end ReducedStage3Geometry

end Data
end ABKPR
end Erdos735
