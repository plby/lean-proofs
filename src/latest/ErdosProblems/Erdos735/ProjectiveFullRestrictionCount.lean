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

import ErdosProblems.Erdos735.ProjectiveEnumerationCounts
import ErdosProblems.Erdos735.SignVectorIncidence

open scoped LinearAlgebra.Projectivization

namespace Erdos735.ProjectiveArrangement

open Classical SignVector
open ChartOrder
noncomputable section

def otherIndexEquivFin {I : Type*} [Fintype I] [DecidableEq I] (a : I) :
    Fin (Fintype.card {b : I // b ≠ a}) ≃ {b : I // b ≠ a} :=
  (Fintype.equivFin {b : I // b ≠ a}).symm

def selectedLastPoints {I : Type*} [Fintype I] [DecidableEq I]
    (q : I → Point) (a : I) : Fin (Fintype.card {b : I // b ≠ a} + 1) → Point :=
  Fin.lastCases (q a) (fun j ↦ q (otherIndexEquivFin a j).1)

def selectedLastIndexEquiv {I : Type*} [Fintype I] [DecidableEq I] (a : I) :
    Fin (Fintype.card {b : I // b ≠ a} + 1) ≃ I :=
  finSuccEquivLast |>.trans (Equiv.optionCongr (otherIndexEquivFin a)) |>.trans
    (Equiv.optionSubtypeNe a)

@[simp] theorem selectedLastIndexEquiv_last {I : Type*} [Fintype I] [DecidableEq I]
    (a : I) : selectedLastIndexEquiv a (Fin.last (Fintype.card {b : I // b ≠ a})) = a := by
  simp [selectedLastIndexEquiv]

@[simp] theorem selectedLastIndexEquiv_castSucc {I : Type*} [Fintype I] [DecidableEq I]
    (a : I) (j : Fin (Fintype.card {b : I // b ≠ a})) :
    selectedLastIndexEquiv a j.castSucc = (otherIndexEquivFin a j).1 := by
  simp [selectedLastIndexEquiv]

theorem selectedLastPoints_eq_comp_selectedLastIndexEquiv
    {I : Type*} [Fintype I] [DecidableEq I] (q : I → Point) (a : I) :
    selectedLastPoints q a = fun i ↦ q (selectedLastIndexEquiv a i) := by
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp [selectedLastPoints]

@[simp] theorem selectedLastPoints_last {I : Type*} [Fintype I] [DecidableEq I]
    (q : I → Point) (a : I) :
    selectedLastPoints q a (Fin.last (Fintype.card {b : I // b ≠ a})) = q a := by
  simp [selectedLastPoints]

@[simp] theorem selectedLastPoints_castSucc {I : Type*} [Fintype I] [DecidableEq I]
    (q : I → Point) (a : I) (j : Fin (Fintype.card {b : I // b ≠ a})) :
    selectedLastPoints q a j.castSucc = q (otherIndexEquivFin a j).1 := by
  simp [selectedLastPoints]

@[simp] theorem selectedLastPoints_priorIndex_last
    {I : Type*} [Fintype I] [DecidableEq I]
    (q : I → Point) (a : I) (j : Fin (Fintype.card {b : I // b ≠ a})) :
    selectedLastPoints q a (priorIndex (Fin.last (Fintype.card {b : I // b ≠ a})) j) =
      q (otherIndexEquivFin a j).1 := by
  rw [show priorIndex (Fin.last (Fintype.card {b : I // b ≠ a})) j = j.castSucc by
    apply Fin.ext
    rfl]
  exact selectedLastPoints_castSucc q a j

theorem selectedLastPoints_injective {I : Type*} [Fintype I] [DecidableEq I]
    (q : I → Point) (hq : Function.Injective q) (a : I) :
    Function.Injective (selectedLastPoints q a) := by
  intro x
  refine Fin.lastCases ?_ (fun i ↦ ?_) x
  · intro y
    refine Fin.lastCases ?_ (fun j hxy ↦ ?_) y
    · intro hxy
      rfl
    · exfalso
      have ha : a = (otherIndexEquivFin a j).1 :=
        hq (by simpa [selectedLastPoints] using hxy)
      exact (otherIndexEquivFin a j).2 ha.symm
  · intro y
    refine Fin.lastCases ?_ (fun j hxy ↦ ?_) y
    · intro hxy
      exfalso
      have ha : (otherIndexEquivFin a i).1 = a :=
        hq (by simpa [selectedLastPoints] using hxy)
      exact (otherIndexEquivFin a i).2 ha
    · rw [Fin.castSucc_inj]
      apply (otherIndexEquivFin a).injective
      apply Subtype.ext
      exact hq (by simpa [selectedLastPoints] using hxy)

def allIntersectionsAt {I : Type*} [Fintype I] [DecidableEq I]
    (q : I → Point) (hq : Function.Injective q) (a : I) :
    Finset (ℙ ℝ Vec3) :=
  Finset.univ.image fun b : {b : I // b ≠ a} ↦
    intersectionPoint (q a) (q b.1) (hq.ne b.2.symm)

theorem prefixIntersections_selectedLast_eq_allIntersectionsAt
    {I : Type*} [Fintype I] [DecidableEq I]
    (q : I → Point) (hq : Function.Injective q) (a : I) :
    prefixIntersections (selectedLastPoints q a) (selectedLastPoints_injective q hq a)
        (Fin.last (Fintype.card {b : I // b ≠ a})) =
      allIntersectionsAt q hq a := by
  classical
  ext x
  simp only [prefixIntersections, allIntersectionsAt, Finset.mem_image, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨otherIndexEquivFin a j, ?_⟩
    simp [prefixIntersection]
  · rintro ⟨b, rfl⟩
    refine ⟨(otherIndexEquivFin a).symm b, ?_⟩
    simp [prefixIntersection]

theorem restrictedFaceCount_otherNormals_eq_two_mul_allIntersectionsAt_card
    {I : Type*} [Fintype I] [DecidableEq I] [Nontrivial I]
    (q : I → Point) (hq : Function.Injective q) (a : I) :
    restrictedFaceCount (otherNormals (fun i ↦ normalVec (q i)) a) (normalVec (q a)) =
      2 * (allIntersectionsAt q hq a).card := by
  let m := Fintype.card {b : I // b ≠ a}
  let p := selectedLastPoints q a
  let hp := selectedLastPoints_injective q hq a
  have hm : 0 < m := by
    apply Fintype.card_pos_iff.mpr
    obtain ⟨b, hba⟩ := exists_ne a
    exact ⟨⟨b, hba⟩⟩
  have hcount := restrictedFaceCount_priorNormals_eq_two_mul_card p hp (Fin.last m) (by
    simpa using hm)
  have hreindex :
      restrictedFaceCount (priorNormals p (Fin.last m)) (normalVec (p (Fin.last m))) =
        restrictedFaceCount (otherNormals (fun i ↦ normalVec (q i)) a)
          (normalVec (q a)) := by
    rw [← restrictedFaceCount_reindex (otherIndexEquivFin a)
      (otherNormals (fun i ↦ normalVec (q i)) a) (normalVec (q a))]
    congr 1
    · funext j
      dsimp only [priorNormals, p, m, reindexNormals, otherNormals]
      rw [selectedLastPoints_priorIndex_last]
    · dsimp only [p, m]
      rw [selectedLastPoints_last]
  rw [hreindex] at hcount
  rw [prefixIntersections_selectedLast_eq_allIntersectionsAt q hq a] at hcount
  exact hcount

theorem allIntersectionsAt_subtype_eq_verticesOn (B : Finset Point)
    (a : {x // x ∈ B}) :
    allIntersectionsAt (fun b : {x // x ∈ B} ↦ b.1) Subtype.val_injective a =
      verticesOn (projectiveVertices B) Incident a.1 := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨b, hb, hbx⟩ := Finset.mem_image.mp hx
    let pair : DistinctPointPair B := ⟨(a, b.1), by
      intro hab
      exact b.2 hab.symm⟩
    have hxpair : x = indexedIntersection B pair := by
      simpa [allIntersectionsAt, pair, indexedIntersection] using hbx.symm
    apply (mem_verticesOn (projectiveVertices B) Incident).mpr
    refine ⟨?_, ?_⟩
    · rw [hxpair]
      exact indexedIntersection_mem_projectiveVertices B pair
    · rw [hxpair]
      exact indexedIntersection_incident_left B pair
  · intro hx
    obtain ⟨hxvert, hxa⟩ := (mem_verticesOn (projectiveVertices B) Incident).mp hx
    unfold projectiveVertices at hxvert
    obtain ⟨pq, hpq, hpqx⟩ := Finset.mem_image.mp hxvert
    by_cases hua : pq.1.1 = a
    · let b : {z : {x // x ∈ B} // z ≠ a} := ⟨pq.1.2, by
        intro hva
        apply pq.2
        exact hua.trans hva.symm⟩
      apply Finset.mem_image.mpr
      refine ⟨b, Finset.mem_univ _, ?_⟩
      apply eq_of_two_common_lines (show a.1 ≠ b.1.1 by
        intro hab
        exact b.2 (Subtype.ext hab.symm))
      · exact intersectionPoint_on_left _ _ _
      · exact intersectionPoint_on_right _ _ _
      · exact hxa
      · rw [← hpqx]
        exact indexedIntersection_incident_right B pq
    · let b : {z : {x // x ∈ B} // z ≠ a} := ⟨pq.1.1, hua⟩
      apply Finset.mem_image.mpr
      refine ⟨b, Finset.mem_univ _, ?_⟩
      apply eq_of_two_common_lines (show a.1 ≠ b.1.1 by
        intro hab
        exact b.2 (Subtype.ext hab.symm))
      · exact intersectionPoint_on_left _ _ _
      · exact intersectionPoint_on_right _ _ _
      · exact hxa
      · rw [← hpqx]
        exact indexedIntersection_incident_left B pq

theorem restrictedFaceCount_otherNormals_normalVec_eq_two_mul_verticesOn_card
    (B : Finset Point) [Nontrivial {x // x ∈ B}] (a : {x // x ∈ B}) :
    restrictedFaceCount
        (otherNormals (fun b : {x // x ∈ B} ↦ normalVec b.1) a)
        (normalVec a.1) =
      2 * (verticesOn (projectiveVertices B) Incident a.1).card := by
  rw [restrictedFaceCount_otherNormals_eq_two_mul_allIntersectionsAt_card
    (fun b : {x // x ∈ B} ↦ b.1) Subtype.val_injective a]
  rw [allIntersectionsAt_subtype_eq_verticesOn]

end

end Erdos735.ProjectiveArrangement
