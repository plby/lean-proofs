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

import ErdosProblems.Erdos735.SignVectorIncidence

/-!
# Polar normals of a strict sign-vector face

For a strict face, orient every arrangement normal towards that face and normalize all oriented
normals into one affine plane. This file proves the exact algebraic bridge used by the polar-dual
construction: an arrangement edge on a face with owner `i` exists precisely when the normalized
normal `i` is strictly exposed from all the other normalized normals.
-/

open scoped BigOperators Matrix
open Matrix

namespace Erdos735
namespace SignVector

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A chosen point in the open cone represented by a strict face. -/
noncomputable def faceWitness (n : I → Vec3) (f : StrictFace n) : Vec3 :=
  Classical.choose f.2

theorem faceWitness_realizes (n : I → Vec3) (f : StrictFace n) :
    Realizes n f.1 (faceWitness n f) :=
  Classical.choose_spec f.2

/-- Orient the normal of each hyperplane into the half-space selected by `f`. -/
def faceOrientedNormal (n : I → Vec3) (f : StrictFace n) (i : I) : Vec3 :=
  if f.1 i then n i else -n i

@[simp] theorem faceOrientedNormal_dot (n : I → Vec3) (f : StrictFace n)
    (i : I) (y : Vec3) :
    faceOrientedNormal n f i ⬝ᵥ y = signed (f.1 i) (n i ⬝ᵥ y) := by
  cases h : f.1 i <;> simp [faceOrientedNormal, signed, h]

/-- The positive denominator used to put a signed normal in the affine polar plane. -/
noncomputable def facePolarDenom (n : I → Vec3) (f : StrictFace n) (i : I) : ℝ :=
  signed (f.1 i) (n i ⬝ᵥ faceWitness n f)

theorem facePolarDenom_pos (n : I → Vec3) (f : StrictFace n) (i : I) :
    0 < facePolarDenom n f i :=
  faceWitness_realizes n f i

/-- The signed normal normalized into the affine plane `p · faceWitness = 1`. -/
noncomputable def facePolarNormal (n : I → Vec3) (f : StrictFace n) (i : I) : Vec3 :=
  (facePolarDenom n f i)⁻¹ • faceOrientedNormal n f i

theorem facePolarNormal_dot (n : I → Vec3) (f : StrictFace n) (i : I) (y : Vec3) :
    facePolarNormal n f i ⬝ᵥ y =
      (facePolarDenom n f i)⁻¹ * signed (f.1 i) (n i ⬝ᵥ y) := by
  simp [facePolarNormal, faceOrientedNormal_dot]

@[simp] theorem facePolarNormal_dot_witness (n : I → Vec3) (f : StrictFace n)
    (i : I) :
    facePolarNormal n f i ⬝ᵥ faceWitness n f = 1 := by
  rw [facePolarNormal_dot]
  exact inv_mul_cancel₀ (facePolarDenom_pos n f i).ne'

theorem facePolarNormal_dot_pos_iff (n : I → Vec3) (f : StrictFace n)
    (i : I) (y : Vec3) :
    0 < facePolarNormal n f i ⬝ᵥ y ↔ 0 < signed (f.1 i) (n i ⬝ᵥ y) := by
  rw [facePolarNormal_dot]
  exact mul_pos_iff_of_pos_left (inv_pos.mpr (facePolarDenom_pos n f i))

theorem facePolarNormal_dot_eq_zero_iff (n : I → Vec3) (f : StrictFace n)
    (i : I) (y : Vec3) :
    facePolarNormal n f i ⬝ᵥ y = 0 ↔ n i ⬝ᵥ y = 0 := by
  rw [facePolarNormal_dot, mul_eq_zero]
  have hinv : (facePolarDenom n f i)⁻¹ ≠ 0 :=
    inv_ne_zero (facePolarDenom_pos n f i).ne'
  simp only [hinv, false_or]
  cases f.1 i <;> simp [signed]

/-- A normalized signed normal is strictly exposed if a linear functional vanishes on it and is
strictly positive on every other normalized normal. -/
def PolarStrictlyExposedAt (n : I → Vec3) (f : StrictFace n) (i : I) : Prop :=
  ∃ y : Vec3,
    facePolarNormal n f i ⬝ᵥ y = 0 ∧
      ∀ j : I, j ≠ i → 0 < facePolarNormal n f j ⬝ᵥ y

/-- The signs obtained by deleting the owner `i` from a face. -/
def faceRestrictionSigns (n : I → Vec3) (f : StrictFace n) (i : I) :
    {j : I // j ≠ i} → Bool :=
  fun j ↦ f.1 j.1

/-- The polar algebra: a face sign pattern is feasible on hyperplane `i` exactly when the
normalized signed normal `i` is strictly exposed from the remaining normalized normals. -/
theorem restrictedRealizable_face_iff_polarStrictlyExposed
    (n : I → Vec3) (f : StrictFace n) (i : I) :
    RestrictedRealizable (otherNormals n i) (n i) (faceRestrictionSigns n f i) ↔
      PolarStrictlyExposedAt n f i := by
  constructor
  · rintro ⟨y, hy, hzero⟩
    refine ⟨y, (facePolarNormal_dot_eq_zero_iff n f i y).2 hzero, ?_⟩
    intro j hji
    rw [facePolarNormal_dot_pos_iff]
    exact hy ⟨j, hji⟩
  · rintro ⟨y, hzero, hy⟩
    refine ⟨y, ?_, (facePolarNormal_dot_eq_zero_iff n f i y).1 hzero⟩
    intro j
    exact (facePolarNormal_dot_pos_iff n f j.1 y).1 (hy j.1 j.2)

/-- There is a strict edge owned by `i` on `f` exactly when the normalized signed normal `i`
is strictly exposed. -/
theorem exists_incident_strictEdge_owner_iff_polarStrictlyExposed
    (n : I → Vec3) (f : StrictFace n) (i : I) :
    (∃ e : StrictEdge n, e ∈ faceEdges n f ∧ e.1.1 = i) ↔
      PolarStrictlyExposedAt n f i := by
  rw [← restrictedRealizable_face_iff_polarStrictlyExposed n f i]
  constructor
  · rintro ⟨e, he, hei⟩
    subst i
    refine ⟨Classical.choose e.2, ?_, (Classical.choose_spec e.2).2⟩
    intro j
    have hinc := (mem_faceEdges_iff n f e).1 he j
    simpa [otherNormals, faceRestrictionSigns, hinc] using (Classical.choose_spec e.2).1 j
  · intro h
    let c : EdgeCode I := ⟨i, faceRestrictionSigns n f i⟩
    let e : StrictEdge n := ⟨c, h⟩
    refine ⟨e, ?_, rfl⟩
    rw [mem_faceEdges_iff]
    intro j
    simp [e, c, faceRestrictionSigns]

/-- Three distinct strictly exposed polar normals give three distinct strict edges on the face. -/
theorem faceEdges_card_three_le_of_three_polarStrictlyExposed
    (n : I → Vec3) (f : StrictFace n) {i j k : I}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : PolarStrictlyExposedAt n f i)
    (hj : PolarStrictlyExposedAt n f j)
    (hk : PolarStrictlyExposedAt n f k) :
    3 ≤ (faceEdges n f).card := by
  obtain ⟨ei, hei, hei_owner⟩ :=
    (exists_incident_strictEdge_owner_iff_polarStrictlyExposed n f i).2 hi
  obtain ⟨ej, hej, hej_owner⟩ :=
    (exists_incident_strictEdge_owner_iff_polarStrictlyExposed n f j).2 hj
  obtain ⟨ek, hek, hek_owner⟩ :=
    (exists_incident_strictEdge_owner_iff_polarStrictlyExposed n f k).2 hk
  have heij : ei ≠ ej := by
    intro h
    apply hij
    rw [← hei_owner, ← hej_owner, h]
  have heik : ei ≠ ek := by
    intro h
    apply hik
    rw [← hei_owner, ← hek_owner, h]
  have hejk : ej ≠ ek := by
    intro h
    apply hjk
    rw [← hej_owner, ← hek_owner, h]
  have hsubset : {ei, ej, ek} ⊆ faceEdges n f := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact hei
    · exact hej
    · exact hek
  have hcard : ({ei, ej, ek} : Finset (StrictEdge n)).card = 3 := by
    simp [heij, heik, hejk]
  rw [← hcard]
  exact Finset.card_le_card hsubset

end SignVector
end Erdos735
