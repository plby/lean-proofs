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

import ErdosProblems.Erdos735.RedChordSector
import ErdosProblems.Erdos735.RedChordIncidence

/-!
# Concrete reduced-magic endpoints of red restriction sectors

The affine-chart endpoints from `RedChordSector` have active blue owners.
For a reduced magic configuration, every red--blue crossing is already a
vertex of the blue-only projective arrangement.  Consequently both explicit
sector endpoints are actual blue arrangement vertices, not merely abstract
points supplied by a cardinality equivalence.
-/

open Classical
open scoped LinearAlgebra.Projectivization Matrix
open Matrix

namespace Erdos735.RedChordConcreteEndpoints

noncomputable section

open ProjectiveArrangement RedChordIncidence SignVector
open SignVector.RedChordSector

abbrev Point := ProjectiveArrangement.Point

variable {P : Finset Point} {w : Point → ℝ} {c : ℝ}
variable [Nonempty {b // b ∈ nonordinaryPoints P}]

theorem lowerEndpoint_mem_projectiveVertices
    (hred : IsReducedMagic P w c)
    {a : Point} (ha : a ∈ ordinaryPoints P)
    {x : Vec3}
    {s : {b // b ∈ nonordinaryPoints P} → Bool}
    {hx : Realizes
      (fun b : {b // b ∈ nonordinaryPoints P} ↦ normalVec b.1) s x}
    (D : EndpointData
      (fun b : {b // b ∈ nonordinaryPoints P} ↦ normalVec b.1) s
      (normalVec a) x hx)
    (hax : normalVec a ⬝ᵥ x = 0) :
    lowerProjectiveEndpoint
        (fun b : {b // b ∈ nonordinaryPoints P} ↦ normalVec b.1) s
        (normalVec a) x D.lower_nonempty hx ∈
      projectiveVertices (nonordinaryPoints P) := by
  let v := lowerProjectiveEndpoint
    (fun b : {b // b ∈ nonordinaryPoints P} ↦ normalVec b.1) s
    (normalVec a) x D.lower_nonempty hx
  obtain ⟨b, hvb⟩ := D.exists_lower_owner_incident
  have hva : Incident v a := by
    apply (onProjectiveLine_mk_iff (normalVec a) _
      (chartPoint_ne_zero hx _)).2
    exact D.lower_on_red hax
  have hab : a ≠ b.1 := red_ne_blue ha b.2
  have heq : v = intersectionPoint a b.1 hab :=
    eq_of_two_common_lines hab hva hvb
      (intersectionPoint_on_left a b.1 hab)
      (intersectionPoint_on_right a b.1 hab)
  change v ∈ projectiveVertices (nonordinaryPoints P)
  rw [heq]
  exact red_blue_intersection_mem_projectiveVertices hred ha b.2

theorem upperEndpoint_mem_projectiveVertices
    (hred : IsReducedMagic P w c)
    {a : Point} (ha : a ∈ ordinaryPoints P)
    {x : Vec3}
    {s : {b // b ∈ nonordinaryPoints P} → Bool}
    {hx : Realizes
      (fun b : {b // b ∈ nonordinaryPoints P} ↦ normalVec b.1) s x}
    (D : EndpointData
      (fun b : {b // b ∈ nonordinaryPoints P} ↦ normalVec b.1) s
      (normalVec a) x hx)
    (hax : normalVec a ⬝ᵥ x = 0) :
    upperProjectiveEndpoint
        (fun b : {b // b ∈ nonordinaryPoints P} ↦ normalVec b.1) s
        (normalVec a) x D.upper_nonempty hx ∈
      projectiveVertices (nonordinaryPoints P) := by
  let v := upperProjectiveEndpoint
    (fun b : {b // b ∈ nonordinaryPoints P} ↦ normalVec b.1) s
    (normalVec a) x D.upper_nonempty hx
  obtain ⟨b, hvb⟩ := D.exists_upper_owner_incident
  have hva : Incident v a := by
    apply (onProjectiveLine_mk_iff (normalVec a) _
      (chartPoint_ne_zero hx _)).2
    exact D.upper_on_red hax
  have hab : a ≠ b.1 := red_ne_blue ha b.2
  have heq : v = intersectionPoint a b.1 hab :=
    eq_of_two_common_lines hab hva hvb
      (intersectionPoint_on_left a b.1 hab)
      (intersectionPoint_on_right a b.1 hab)
  change v ∈ projectiveVertices (nonordinaryPoints P)
  rw [heq]
  exact red_blue_intersection_mem_projectiveVertices hred ha b.2

/-- The two explicit endpoints form a two-element subset of the actual
blue-only projective vertex set. -/
theorem projectiveEndpoints_card_and_subset
    (hred : IsReducedMagic P w c)
    {a : Point} (ha : a ∈ ordinaryPoints P)
    {x : Vec3}
    {s : {b // b ∈ nonordinaryPoints P} → Bool}
    {hx : Realizes
      (fun b : {b // b ∈ nonordinaryPoints P} ↦ normalVec b.1) s x}
    (D : EndpointData
      (fun b : {b // b ∈ nonordinaryPoints P} ↦ normalVec b.1) s
      (normalVec a) x hx)
    (hax : normalVec a ⬝ᵥ x = 0) :
    (projectiveEndpoints
      (fun b : {b // b ∈ nonordinaryPoints P} ↦ normalVec b.1) s
      (normalVec a) x D.lower_nonempty D.upper_nonempty hx).card = 2 ∧
    projectiveEndpoints
      (fun b : {b // b ∈ nonordinaryPoints P} ↦ normalVec b.1) s
      (normalVec a) x D.lower_nonempty D.upper_nonempty hx ⊆
        projectiveVertices (nonordinaryPoints P) := by
  constructor
  · exact D.projective_card
  · intro v hv
    simp only [projectiveEndpoints, Finset.mem_insert,
      Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact lowerEndpoint_mem_projectiveVertices hred ha D hax
    · exact upperEndpoint_mem_projectiveVertices hred ha D hax

end

end Erdos735.RedChordConcreteEndpoints
