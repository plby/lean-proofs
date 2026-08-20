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

import ErdosProblems.Erdos735.ProjectivePrefixFaceCount
import ErdosProblems.Erdos735.IncidenceInsertionCount

/-! # Global counts for an injectively enumerated projective arrangement -/

open scoped BigOperators LinearAlgebra.Projectivization

namespace Erdos735.ProjectiveArrangement

open Classical SignVector ChartOrder
noncomputable section

def enumeratedPointSet {k : ℕ} (p : Fin k → Point) : Finset Point :=
  Finset.univ.image p

abbrev EnumeratedVertex {k : ℕ} (p : Fin k → Point) :=
  {v // v ∈ projectiveVertices (enumeratedPointSet p)}

def EnumeratedOnLine {k : ℕ} (p : Fin k → Point)
    (v : EnumeratedVertex p) (i : Fin k) : Prop := Incident v.1 (p i)

noncomputable instance {k : ℕ} (p : Fin k → Point) :
    DecidableRel (EnumeratedOnLine p) := fun _ _ ↦ Classical.propDecidable _

def prefixIntersectionVertex {k : ℕ} (p : Fin k → Point)
    (hp : Function.Injective p) (i : Fin k) (j : Fin i) : EnumeratedVertex p := by
  let B := enumeratedPointSet p
  let pi : {x // x ∈ B} := ⟨p i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  let pj : {x // x ∈ B} := ⟨p (priorIndex i j),
    Finset.mem_image.mpr ⟨priorIndex i j, Finset.mem_univ _, rfl⟩⟩
  have hij : pi ≠ pj := by
    intro heq
    have hpq : p i = p (priorIndex i j) := congrArg Subtype.val heq
    have hiq := hp hpq
    have hval := congrArg Fin.val hiq
    simp only [priorIndex] at hval
    omega
  let pair : DistinctPointPair B := ⟨(pi, pj), hij⟩
  exact ⟨indexedIntersection B pair, indexedIntersection_mem_projectiveVertices B pair⟩

@[simp] theorem coe_prefixIntersectionVertex {k : ℕ} (p : Fin k → Point)
    (hp : Function.Injective p) (i : Fin k) (j : Fin i) :
    (prefixIntersectionVertex p hp i j : ℙ ℝ Vec3) = prefixIntersection p hp i j := by
  rfl

theorem prefixIntersections_card_eq_verticesEncounteredAt_card
    {k : ℕ} (p : Fin k → Point) (hp : Function.Injective p) (i : Fin k) :
    (prefixIntersections p hp i).card =
      (verticesEncounteredAt (Finset.univ : Finset (EnumeratedVertex p))
        (EnumeratedOnLine p) i).card := by
  classical
  apply Finset.card_bij (fun x _ ↦ ⟨x, by
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (show x ∈ prefixIntersections p hp i by assumption)
    exact (prefixIntersectionVertex p hp i j).2⟩)
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    simp only [verticesEncounteredAt, Finset.mem_filter, Finset.mem_univ, true_and,
      nonfirstIncidentLines, incidentLines, Finset.mem_filter]
    refine ⟨prefixIntersection_incident_outer p hp i j, ?_⟩
    exact ⟨priorIndex i j, prefixIntersection_incident_prior p hp i j, j.isLt⟩
  · intro x hx y hy hxy
    exact congrArg Subtype.val hxy
  · intro v hv
    simp only [verticesEncounteredAt, Finset.mem_filter, Finset.mem_univ, true_and,
      nonfirstIncidentLines, incidentLines, Finset.mem_filter] at hv
    obtain ⟨hvi, j, hvj, hji⟩ := hv
    let l : Fin i := ⟨j.1, hji⟩
    have hij : p i ≠ p j := hp.ne (ne_of_gt hji)
    have heq : v.1 = prefixIntersection p hp i l := by
      apply eq_of_two_common_lines hij
      · exact hvi
      · exact hvj
      · exact prefixIntersection_incident_outer p hp i l
      · simpa [l, priorIndex] using prefixIntersection_incident_prior p hp i l
    refine ⟨prefixIntersection p hp i l, Finset.mem_image.mpr ⟨l, Finset.mem_univ _, rfl⟩, ?_⟩
    apply Subtype.ext
    exact heq.symm

theorem incidentLines_enumeratedVertex_nonempty {k : ℕ}
    (p : Fin k → Point) (v : EnumeratedVertex p) :
    (incidentLines (EnumeratedOnLine p) v).Nonempty := by
  classical
  have hv := v.2
  unfold projectiveVertices at hv
  obtain ⟨pq, hpq, hpqv⟩ := Finset.mem_image.mp hv
  obtain ⟨i, hi, hip⟩ := Finset.mem_image.mp pq.1.1.2
  refine ⟨i, ?_⟩
  simp only [incidentLines, Finset.mem_filter, Finset.mem_univ, true_and]
  change Incident v.1 (p i)
  rw [← hpqv, hip]
  exact indexedIntersection_incident_left (enumeratedPointSet p) pq

theorem faceCount_normalVec_eq_two_add_sum_multiplicity
    (k : ℕ) (p : Fin (k + 1) → Point) (hp : Function.Injective p) :
    faceCount (fun i ↦ normalVec (p i)) =
      2 + ∑ v : EnumeratedVertex p,
        2 * (lineMultiplicity (EnumeratedOnLine p) v - 1) := by
  rw [faceCount_normalVec_eq_two_add_prefixIntersections k p hp]
  have hcards (i : Fin (k + 1)) :
      (prefixIntersections p hp i).card =
        (verticesEncounteredAt (Finset.univ : Finset (EnumeratedVertex p))
          (EnumeratedOnLine p) i).card :=
    prefixIntersections_card_eq_verticesEncounteredAt_card p hp i
  have htotal := sum_verticesEncounteredAt_card
    (Finset.univ : Finset (EnumeratedVertex p)) (EnumeratedOnLine p)
    (fun v hv ↦ incidentLines_enumeratedVertex_nonempty p v)
  have hprefix_total :
      (∑ i : Fin (k + 1), (prefixIntersections p hp i).card) =
        ∑ v : EnumeratedVertex p,
          (lineMultiplicity (EnumeratedOnLine p) v - 1) := by
    calc
      (∑ i : Fin (k + 1), (prefixIntersections p hp i).card) =
          ∑ i : Fin (k + 1),
            (verticesEncounteredAt (Finset.univ : Finset (EnumeratedVertex p))
              (EnumeratedOnLine p) i).card := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hcards i
      _ = ∑ v : EnumeratedVertex p,
          (lineMultiplicity (EnumeratedOnLine p) v - 1) := by simpa using htotal
  rw [Fin.sum_univ_succ] at hprefix_total
  have hzero : (prefixIntersections p hp (0 : Fin (k + 1))).card = 0 := by
    apply Finset.card_eq_zero.mpr
    change Finset.univ.image (prefixIntersection p hp (0 : Fin (k + 1))) = ∅
    rw [Finset.image_eq_empty]
    change (Finset.univ : Finset (Fin 0)) = (∅ : Finset (Fin 0))
    exact Finset.univ_eq_empty
  rw [hzero, zero_add] at hprefix_total
  rw [← Finset.mul_sum, ← Finset.mul_sum, hprefix_total]

theorem strictFace_card_normalVec_eq_two_add_sum_multiplicity
    (k : ℕ) (p : Fin (k + 1) → Point) (hp : Function.Injective p) :
    Fintype.card (StrictFace (fun i ↦ normalVec (p i))) =
      2 + ∑ v : EnumeratedVertex p,
        2 * (lineMultiplicity (EnumeratedOnLine p) v - 1) := by
  rw [card_strictFace]
  exact faceCount_normalVec_eq_two_add_sum_multiplicity k p hp

end

end Erdos735.ProjectiveArrangement
