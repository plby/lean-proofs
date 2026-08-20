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

import ErdosProblems.Erdos735.Discharging12
import Mathlib.Tactic.FinCases

/-!
# Cyclic packing around blue faces

The endpoint restriction already implies every clause of
`ABKPR.Data.NeighborPacking`.  This file proves the finite-cycle lemma,
including the exceptional four-cycle with one nonadjacent red chord, and
eliminates `NeighborPacking` as an independent geometric assumption.
-/

namespace Erdos735

open scoped BigOperators

namespace ABKPR

/-- A nontrivial marked subset of a finite cycle has a transition from an
unmarked index to a marked successor. -/
theorem exists_cyclic_free_to_marked {n : ℕ} (hn : 0 < n)
    (R : Finset (Fin n)) (hR : R.Nonempty)
    (hfree : (Finset.univ \ R).Nonempty) :
    ∃ i : Fin n, i ∉ R ∧ cyclicSucc hn i ∈ R := by
  classical
  let F : Finset (Fin n) := Finset.univ \ R
  let zero : Fin n := ⟨0, hn⟩
  by_cases hzero : zero ∈ R
  · let i : Fin n := F.max' hfree
    have hiF : i ∈ F := Finset.max'_mem F hfree
    have hiR : i ∉ R := (Finset.mem_sdiff.mp hiF).2
    refine ⟨i, hiR, ?_⟩
    by_contra hsuccR
    have hsuccF : cyclicSucc hn i ∈ F :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hsuccR⟩
    have hle : cyclicSucc hn i ≤ i := Finset.le_max' F _ hsuccF
    by_cases hnowrap : i.val + 1 < n
    · have hlt : i < cyclicSucc hn i := by
        apply Fin.mk_lt_mk.mpr
        change i.val < (i.val + 1) % n
        rw [Nat.mod_eq_of_lt hnowrap]
        omega
      exact (not_lt_of_ge hle) hlt
    · have hilast : i.val + 1 = n := by omega
      have hsucczero : cyclicSucc hn i = zero := by
        apply Fin.ext
        change (i.val + 1) % n = 0
        simp [hilast]
      exact hsuccR (hsucczero.symm ▸ hzero)
  · let r : Fin n := R.min' hR
    have hrR : r ∈ R := Finset.min'_mem R hR
    have hrpos : 0 < r.val := by
      by_contra h
      have hrzero : r = zero := by
        apply Fin.ext
        change r.val = 0
        omega
      exact hzero (hrzero ▸ hrR)
    let i : Fin n := ⟨r.val - 1, by omega⟩
    have hiR : i ∉ R := by
      intro hi
      have hle : r ≤ i := Finset.min'_le R i hi
      have hleval : r.val ≤ i.val := hle
      simp only [i] at hleval
      omega
    refine ⟨i, hiR, ?_⟩
    have hsucc : cyclicSucc hn i = r := by
      apply Fin.ext
      simp only [cyclicSucc, i]
      rw [Nat.mod_eq_of_lt]
      · omega
      · omega
    exact hsucc.symm ▸ hrR

/-- In a four-cycle, the complement of a nonadjacent pair contains no
adjacent pair. -/
theorem fin_four_no_adjacent_complement
    (a b i : Fin 4) (hab : a ≠ b)
    (hba : b ≠ cyclicSucc (by decide) a)
    (hab' : a ≠ cyclicSucc (by decide) b)
    (hia : i ≠ a) (hib : i ≠ b)
    (hsa : cyclicSucc (by decide) i ≠ a)
    (hsb : cyclicSucc (by decide) i ≠ b) : False := by
  fin_cases a <;> fin_cases b <;> fin_cases i <;>
    simp [cyclicSucc] at hab hba hab' hia hib hsa hsb

namespace Data

universe uV uE uF

variable {Vertex : Type uV} {Edge : Type uE} {Face : Type uF}
variable [Fintype Vertex] [Fintype Edge] [Fintype Face]
variable [DecidableEq Vertex] [DecidableEq Edge] [DecidableEq Face]
variable {C : BlueCellulation Vertex Edge Face}
variable (A : ABKPR.Data C)

lemma badNeighborIndices_subset_free (hrest : A.EndpointRestriction) (f : Face) :
    A.badNeighborIndices f ⊆ Finset.univ \ A.redEndpoints f := by
  intro i hi
  have hbad : A.IsBadTwoQuadrangle (A.across ⟨f, i⟩).1 :=
    (Finset.mem_filter.mp hi).2
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (hrest f i hbad).1⟩

lemma badNeighborCount_add_endpoints_le (hrest : A.EndpointRestriction) (f : Face) :
    A.badNeighborCount f + (A.redEndpoints f).card ≤ C.faceDegree f := by
  have hsub := A.badNeighborIndices_subset_free hrest f
  have hcard := Finset.card_le_card hsub
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
  simp only [badNeighborCount]
  omega

lemma badNeighborCount_add_endpoints_lt (hrest : A.EndpointRestriction)
    (f : Face) (hend : (A.redEndpoints f).Nonempty)
    (hfree : (Finset.univ \ A.redEndpoints f).Nonempty) :
    A.badNeighborCount f + (A.redEndpoints f).card < C.faceDegree f := by
  let F : Finset (Fin (C.faceDegree f)) := Finset.univ \ A.redEndpoints f
  have hsub : A.badNeighborIndices f ⊆ F := A.badNeighborIndices_subset_free hrest f
  obtain ⟨i, hiR, hsuccR⟩ := exists_cyclic_free_to_marked
    (ABKPR.faceDegree_pos C f) (A.redEndpoints f) hend hfree
  have hiF : i ∈ F := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hiR⟩
  have hiNotBad : i ∉ A.badNeighborIndices f := by
    intro hi
    have hbad : A.IsBadTwoQuadrangle (A.across ⟨f, i⟩).1 :=
      (Finset.mem_filter.mp hi).2
    exact (hrest f i hbad).2 hsuccR
  have hcardne : (A.badNeighborIndices f).card ≠ F.card := by
    intro hcard
    have heq : A.badNeighborIndices f = F :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    exact hiNotBad (heq.symm ▸ hiF)
  have hcardle := Finset.card_le_card hsub
  have hpartition := Finset.card_sdiff_add_card
    (Finset.univ : Finset (Fin (C.faceDegree f))) (A.redEndpoints f)
  have hunion : (Finset.univ : Finset (Fin (C.faceDegree f))) ∪
      A.redEndpoints f = Finset.univ :=
    Finset.union_eq_left.mpr (Finset.subset_univ _)
  rw [hunion] at hpartition
  have hpartition' :
      F.card + (A.redEndpoints f).card = C.faceDegree f := by
    simpa [F, Fintype.card_fin] using hpartition
  simp only [badNeighborCount]
  omega

lemma badNeighborCount_eq_zero_four_oneChord
    (hrest : A.EndpointRestriction) {f : Face}
    (hf : C.faceDegree f = 4) (hr : (A.redChords f).card = 1) :
    A.badNeighborCount f = 0 := by
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hr
  have hpmem : p ∈ A.redChords f := by rw [hp]; simp
  have hend : A.redEndpoints f = {p.1, p.2} := by
    ext x
    simp [A.redEndpoint_iff, hp]
  have hpdiff := A.redChord_distinct f p hpmem
  have hpnon := A.redChord_nonadjacent f p hpmem
  apply Finset.card_eq_zero.mpr
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨i, hi⟩
  have hbad : A.IsBadTwoQuadrangle (A.across ⟨f, i⟩).1 :=
    (Finset.mem_filter.mp hi).2
  have hfree := hrest f i hbad
  simp only [hend, Finset.mem_insert, Finset.mem_singleton, not_or] at hfree
  let cast : Fin (C.faceDegree f) → Fin 4 := Fin.cast hf
  have cast_injective : Function.Injective cast := Fin.cast_injective hf
  have cast_succ (j : Fin (C.faceDegree f)) :
      cast (faceSucc C f j) = cyclicSucc (by decide) (cast j) := by
    apply Fin.ext
    simp [cast, faceSucc, cyclicSucc, hf]
  apply fin_four_no_adjacent_complement (cast p.1) (cast p.2) (cast i)
  · exact fun h ↦ hpdiff (cast_injective h)
  · intro h
    apply hpnon.1
    apply cast_injective
    rw [cast_succ]
    exact h
  · intro h
    apply hpnon.2
    apply cast_injective
    rw [cast_succ]
    exact h
  · exact fun h ↦ hfree.1.1 (cast_injective h)
  · exact fun h ↦ hfree.1.2 (cast_injective h)
  · intro h
    apply hfree.2.1
    apply cast_injective
    rw [cast_succ]
    exact h
  · intro h
    apply hfree.2.2
    apply cast_injective
    rw [cast_succ]
    exact h

/-- No independent neighbor-packing hypothesis is needed: the endpoint
restriction and the chord fields already present in `ABKPR.Data` imply it. -/
theorem neighborPacking_of_endpointRestriction
    (hrest : A.EndpointRestriction) : A.NeighborPacking := by
  refine ⟨?_, ?_, ?_⟩
  · intro f
    rw [← A.redEndpoints_card]
    exact A.badNeighborCount_add_endpoints_le hrest f
  · intro f hrpos hlt
    rw [← A.redEndpoints_card]
    apply A.badNeighborCount_add_endpoints_lt hrest f
    · apply Finset.card_pos.mp
      rw [A.redEndpoints_card]
      omega
    · rw [← Finset.card_pos, Finset.card_sdiff]
      simp only [Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
      rw [A.redEndpoints_card]
      omega
  · intro f hf hr
    exact A.badNeighborCount_eq_zero_four_oneChord hrest hf hr

end Data
end ABKPR
end Erdos735
