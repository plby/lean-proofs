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

import ErdosProblems.Erdos735.ConcreteBadReceiver

/-!
# Uniqueness of a sector at a double blue corner

At a projective arrangement vertex of blue multiplicity two, the signs on
the two incident blue lines determine a strict face containing either
orientation of that vertex in its closure.  Away from those two lines the
sign is forced by weak realization at the vertex itself.

This literal sign-vector lemma is deliberately independent of the ABKPR
cellulation indexing.  It is the reusable local ingredient for reducing
Stage-3 donation-vertex collisions to the already identified edge and
two-bad-neighbour exceptions.
-/

open Classical
noncomputable section
open scoped LinearAlgebra.Projectivization

namespace Erdos735.ConcreteDoubleCornerSector

open ChartOrder ProjectiveArrangement ProjectiveBoundaryExtraction
open SignVector SignVector.RedChordSector
open ConcretePolarOrientedVertex

abbrev Point := ProjectiveArrangement.Point
abbrev Line (B : Finset Point) := ProjectiveBoundaryExtraction.Line B

/-- If exactly two blue lines pass through a projective vertex, any incident
line distinct from one named incident line is the other named line. -/
theorem other_incident_line_eq_of_multiplicity_two
    {B : Finset Point}
    (v : ProjectiveBoundaryExtraction.Vertex B)
    (l₀ l₁ l : Line B)
    (hmult : lineMultiplicity (OnLine B) v = 2)
    (hl₀ : OnLine B v l₀) (hl₁ : OnLine B v l₁)
    (hl : OnLine B v l)
    (h₀₁ : l₀ ≠ l₁) (hl₀ne : l ≠ l₀) :
    l = l₁ := by
  let S := Finset.univ.filter fun q : Line B ↦ OnLine B v q
  have hpair : ({l₀, l₁} : Finset (Line B)) ⊆ S := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl <;> simp [S, hl₀, hl₁]
  have hcard : S.card = 2 := hmult
  have hpCard : ({l₀, l₁} : Finset (Line B)).card = 2 :=
    Finset.card_pair h₀₁
  have hset : S = {l₀, l₁} := by
    exact Finset.Subset.antisymm
      (Finset.eq_of_subset_of_card_le hpair (by omega) |>.symm.subset) hpair
  have hlmem : l ∈ S := by simp [S, hl]
  rw [hset] at hlmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hlmem
  exact hlmem.resolve_left hl₀ne

/-- At a double projective blue vertex, two weakly incident strict faces
which agree on both incident blue-line signs are equal. -/
theorem face_eq_of_common_double_corner_of_owner_signs
    {B : Finset Point}
    [Nonempty (Line B)]
    (v : OrientedVertex B)
    (hmult : lineMultiplicity (OnLine B) v.1 = 2)
    (s t : Line B) (hst : s ≠ t)
    (hvs : OnLine B v.1 s) (hvt : OnLine B v.1 t)
    (f g : StrictFace (normals B))
    (hwf : WeaklyRealizes (normals B) f.1 (orientedRep v))
    (hwg : WeaklyRealizes (normals B) g.1 (orientedRep v))
    (hs : f.1 s = g.1 s) (ht : f.1 t = g.1 t) :
    f = g := by
  let S := Finset.univ.filter fun q : Line B ↦ OnLine B v.1 q
  have hpair : ({s, t} : Finset (Line B)) ⊆ S := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl <;> simp [S, hvs, hvt]
  have hcard : S.card = 2 := by
    exact hmult
  have hpCard : ({s, t} : Finset (Line B)).card = 2 :=
    Finset.card_pair hst
  have hset : S = {s, t} := by
    exact Finset.Subset.antisymm
      (Finset.eq_of_subset_of_card_le hpair (by omega) |>.symm.subset) hpair
  apply Subtype.ext
  funext q
  by_cases hqs : q = s
  · simpa [hqs] using hs
  by_cases hqt : q = t
  · simpa [hqt] using ht
  apply SignVector.LocalReceiver.sign_eq_of_weak_of_dot_ne_zero hwf hwg
  intro hzero
  have hqon : OnLine B v.1 q := by
    change Incident v.1.1 q.1
    rw [← orientedRep_projectivization v]
    exact (onProjectiveLine_mk_iff (normalVec q.1) (orientedRep v)
      (orientedRep_ne_zero v)).2 hzero
  have hqmem : q ∈ S := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqon⟩
  rw [hset] at hqmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hqmem
  exact hqmem.elim hqs hqt

end Erdos735.ConcreteDoubleCornerSector
