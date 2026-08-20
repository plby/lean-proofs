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

import ErdosProblems.Erdos735.ProjectiveArrangement

/-!
# Novel vertices during ordered projective-line insertion

For an injectively indexed affine configuration, this file identifies the
new intersection of dual lines `i` and `j` with an earlier intersection on
line `i` exactly when an earlier normal vanishes on `n i × n j`.  This is
the geometric predicate used by the one-dimensional double-restriction
count.
-/

open scoped LinearAlgebra.Projectivization Matrix
open Matrix

namespace Erdos735.ProjectiveArrangement

noncomputable section

/-- Regard an index earlier than `i` as an index in the full enumeration. -/
def priorIndex {k : ℕ} (i : Fin k) (j : Fin i) : Fin k :=
  ⟨j.1, lt_trans j.2 i.2⟩

/-- Regard an index earlier than `j` as an index earlier than `i`. -/
def earlierPriorIndex {k : ℕ} {i : Fin k} (j : Fin i) (l : Fin j) : Fin i :=
  ⟨l.1, lt_trans l.2 j.2⟩

@[simp] theorem priorIndex_earlierPriorIndex {k : ℕ} (i : Fin k)
    (j : Fin i) (l : Fin j) :
    priorIndex i (earlierPriorIndex j l) = priorIndex (priorIndex i j) l := by
  apply Fin.ext
  rfl

/-- The projective intersection of dual line `i` with its earlier line `j`. -/
def prefixIntersection {k : ℕ} (p : Fin k → Point) (hp : Function.Injective p)
    (i : Fin k) (j : Fin i) : ℙ ℝ SignVector.Vec3 :=
  intersectionPoint (p i) (p (priorIndex i j)) <| hp.ne <| by
    intro hij
    have hval := congrArg Fin.val hij
    change i.1 = j.1 at hval
    omega

theorem prefixIntersection_incident_outer {k : ℕ}
    (p : Fin k → Point) (hp : Function.Injective p)
    (i : Fin k) (j : Fin i) :
    Incident (prefixIntersection p hp i j) (p i) := by
  exact intersectionPoint_on_left _ _ _

theorem prefixIntersection_incident_prior {k : ℕ}
    (p : Fin k → Point) (hp : Function.Injective p)
    (i : Fin k) (j : Fin i) :
    Incident (prefixIntersection p hp i j) (p (priorIndex i j)) := by
  exact intersectionPoint_on_right _ _ _

/-- Intersections of line `i` with lines strictly earlier than `j`. -/
def intersectionsBefore {k : ℕ} (p : Fin k → Point)
    (hp : Function.Injective p) (i : Fin k) (j : Fin i) :
    Finset (ℙ ℝ SignVector.Vec3) := by
  classical
  exact Finset.univ.image fun l : Fin j =>
    prefixIntersection p hp i (earlierPriorIndex j l)

/-- The intersection `(i,j)` has already occurred precisely when an earlier
line through the same projective point exists. -/
theorem prefixIntersection_mem_intersectionsBefore_iff {k : ℕ}
    (p : Fin k → Point) (hp : Function.Injective p)
    (i : Fin k) (j : Fin i) :
    prefixIntersection p hp i j ∈ intersectionsBefore p hp i j ↔
      ∃ l : Fin j,
        Incident (prefixIntersection p hp i j)
          (p (priorIndex i (earlierPriorIndex j l))) := by
  classical
  constructor
  · intro hmem
    rw [intersectionsBefore] at hmem
    obtain ⟨l, -, heq⟩ := Finset.mem_image.mp hmem
    refine ⟨l, ?_⟩
    rw [← heq]
    exact prefixIntersection_incident_prior p hp i (earlierPriorIndex j l)
  · rintro ⟨l, hl⟩
    rw [intersectionsBefore]
    apply Finset.mem_image.mpr
    refine ⟨l, Finset.mem_univ _, ?_⟩
    apply eq_of_two_common_lines
      (a := p i) (b := p (priorIndex i (earlierPriorIndex j l)))
      (hp.ne <| by
        intro hil
        have hval := congrArg Fin.val hil
        simp only [priorIndex, earlierPriorIndex] at hval
        omega)
    · exact prefixIntersection_incident_outer p hp i (earlierPriorIndex j l)
    · exact prefixIntersection_incident_prior p hp i (earlierPriorIndex j l)
    · exact prefixIntersection_incident_outer p hp i j
    · exact hl

/-- Incidence of the new intersection with an earlier dual line is exactly
vanishing of the corresponding scalar triple product. -/
theorem incident_prefixIntersection_iff_dot_cross_eq_zero {k : ℕ}
    (p : Fin k → Point) (hp : Function.Injective p)
    (i : Fin k) (j : Fin i) (l : Fin j) :
    Incident (prefixIntersection p hp i j)
        (p (priorIndex i (earlierPriorIndex j l))) ↔
      normalVec (p (priorIndex i (earlierPriorIndex j l))) ⬝ᵥ
        (normalVec (p i) ⨯₃ normalVec (p (priorIndex i j))) = 0 := by
  unfold prefixIntersection Incident intersectionPoint
  rw [onProjectiveLine_mk_iff]

/-- Concrete novelty criterion consumed by the double-restriction count:
`(i,j)` is new among the intersections already seen on line `i` iff every
still-earlier normal is nonzero on `n i × n j`. -/
theorem prefixIntersection_not_mem_intersectionsBefore_iff {k : ℕ}
    (p : Fin k → Point) (hp : Function.Injective p)
    (i : Fin k) (j : Fin i) :
    prefixIntersection p hp i j ∉ intersectionsBefore p hp i j ↔
      ∀ l : Fin j,
        normalVec (p (priorIndex i (earlierPriorIndex j l))) ⬝ᵥ
          (normalVec (p i) ⨯₃ normalVec (p (priorIndex i j))) ≠ 0 := by
  constructor
  · intro hnot l hzero
    apply hnot
    rw [prefixIntersection_mem_intersectionsBefore_iff p hp i j]
    exact ⟨l,
      (incident_prefixIntersection_iff_dot_cross_eq_zero p hp i j l).2 hzero⟩
  · intro hall hmem
    obtain ⟨l, hinc⟩ :=
      (prefixIntersection_mem_intersectionsBefore_iff p hp i j).1 hmem
    exact hall l
      ((incident_prefixIntersection_iff_dot_cross_eq_zero p hp i j l).1 hinc)

end

end Erdos735.ProjectiveArrangement
