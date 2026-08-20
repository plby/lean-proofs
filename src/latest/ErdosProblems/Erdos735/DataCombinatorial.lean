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

/-!
# Elementary cyclic consequences of the ABKPR data

These lemmas discharge fields which only depend on the already recorded
cyclic boundary and red-chord nonadjacency, rather than on any additional
geometry of real line arrangements.
-/

open Classical

namespace Erdos735.ABKPR.Data

variable {Vertex Edge Face : Type*}
variable [Fintype Vertex] [DecidableEq Vertex]
variable [Fintype Edge] [DecidableEq Edge]
variable [Fintype Face] [DecidableEq Face]
variable {C : BlueCellulation Vertex Edge Face}

/-- On a cyclic set with three elements, any two distinct vertices are
adjacent in at least one orientation. -/
private theorem fin_three_adjacent
    (i j : Fin 3) (hij : i ≠ j) :
    j = cyclicSucc (by omega : 0 < 3) i ∨
      i = cyclicSucc (by omega : 0 < 3) j := by
  simp only [Fin.ext_iff, cyclicSucc]
  omega

/-- A triangular face contains no red chord: its two distinct endpoints
would necessarily be adjacent, contrary to `redChord_nonadjacent`. -/
theorem triangle_no_redChord_of_nonadjacent
    (A : Data C) (f : Face) (hdeg : C.faceDegree f = 3) :
    (A.redChords f).card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hpne := A.redChord_distinct f p hp
  have hnon := A.redChord_nonadjacent f p hp
  let castIndex : Fin (C.faceDegree f) → Fin 3 := fun i ↦
    ⟨i.1, by simpa [hdeg] using i.2⟩
  have hcast_inj : Function.Injective castIndex := by
    intro i j hij
    apply Fin.ext
    simpa [castIndex] using congrArg Fin.val hij
  have hne : castIndex p.1 ≠ castIndex p.2 := by
    exact fun h ↦ hpne (hcast_inj h)
  rcases fin_three_adjacent (castIndex p.1) (castIndex p.2) hne with h | h
  · apply hnon.1
    apply Fin.ext
    have hs : (faceSucc C f p.1).val =
        (cyclicSucc (by omega : 0 < 3) (castIndex p.1)).val := by
      simp [faceSucc, castIndex, cyclicSucc, hdeg]
    exact (congrArg Fin.val h).trans hs.symm
  · apply hnon.2
    apply Fin.ext
    have hs : (faceSucc C f p.2).val =
        (cyclicSucc (by omega : 0 < 3) (castIndex p.2)).val := by
      simp [faceSucc, castIndex, cyclicSucc, hdeg]
    exact (congrArg Fin.val h).trans hs.symm

end Erdos735.ABKPR.Data
