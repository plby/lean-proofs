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

import ErdosProblems.Erdos735.CyclicSkeleton

/-!
# Counting projective vertices during ordered line insertion

Insert a finite family of lines in a fixed linear order. A final projective vertex is seen as a
new intersection on each incident line except the earliest incident line. Thus a vertex of
multiplicity `m` contributes exactly `m - 1` to the total insertion count.
-/

open Classical

namespace Erdos735.ChartOrder

noncomputable section

variable {V L : Type*} [Fintype V] [DecidableEq V]
variable [Fintype L] [DecidableEq L] [LinearOrder L]

def incidentLines (onLine : V → L → Prop) [DecidableRel onLine] (v : V) : Finset L :=
  Finset.univ.filter fun l ↦ onLine v l

def nonfirstIncidentLines (onLine : V → L → Prop) [DecidableRel onLine]
    (v : V) : Finset L :=
  (incidentLines onLine v).filter fun l ↦
    ∃ k ∈ incidentLines onLine v, k < l

theorem card_incidentLines (onLine : V → L → Prop) [DecidableRel onLine] (v : V) :
    (incidentLines onLine v).card = lineMultiplicity onLine v := by
  rfl

theorem nonfirstIncidentLines_eq_erase_min
    (onLine : V → L → Prop) [DecidableRel onLine]
    (v : V) (hne : (incidentLines onLine v).Nonempty) :
    nonfirstIncidentLines onLine v =
      (incidentLines onLine v).erase ((incidentLines onLine v).min' hne) := by
  ext l
  simp only [nonfirstIncidentLines, Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hl, k, hk, hkl⟩
    refine ⟨?_, hl⟩
    intro hmin
    subst l
    exact (not_lt_of_ge (Finset.min'_le _ _ hk)) hkl
  · rintro ⟨hlmin, hl⟩
    refine ⟨hl, (incidentLines onLine v).min' hne,
      Finset.min'_mem _ _, ?_⟩
    exact lt_of_le_of_ne (Finset.min'_le _ _ hl) fun h ↦ hlmin h.symm

theorem card_nonfirstIncidentLines
    (onLine : V → L → Prop) [DecidableRel onLine]
    (v : V) (hne : (incidentLines onLine v).Nonempty) :
    (nonfirstIncidentLines onLine v).card = lineMultiplicity onLine v - 1 := by
  rw [nonfirstIncidentLines_eq_erase_min onLine v hne,
    Finset.card_erase_of_mem (Finset.min'_mem _ _), card_incidentLines]

/-- Vertices newly encountered when line `l` is inserted: those incident with `l` which also have
an earlier incident line. -/
def verticesEncounteredAt
    (vertices : Finset V) (onLine : V → L → Prop) [DecidableRel onLine]
    (l : L) : Finset V :=
  vertices.filter fun v ↦ l ∈ nonfirstIncidentLines onLine v

/-- Ordered insertion double count: every vertex contributes its multiplicity minus one. -/
theorem sum_verticesEncounteredAt_card
    (vertices : Finset V) (onLine : V → L → Prop) [DecidableRel onLine]
    (hne : ∀ v ∈ vertices, (incidentLines onLine v).Nonempty) :
    (∑ l : L, (verticesEncounteredAt vertices onLine l).card) =
      ∑ v ∈ vertices, (lineMultiplicity onLine v - 1) := by
  classical
  simp only [verticesEncounteredAt, Finset.card_filter]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun v hv ↦ by
    have hcard := card_nonfirstIncidentLines onLine v (hne v hv)
    calc
      (∑ x : L, if x ∈ nonfirstIncidentLines onLine v then 1 else 0) =
          (nonfirstIncidentLines onLine v).card := by
        rw [← Finset.sum_filter]
        simp
      _ = lineMultiplicity onLine v - 1 := hcard

end

end Erdos735.ChartOrder
