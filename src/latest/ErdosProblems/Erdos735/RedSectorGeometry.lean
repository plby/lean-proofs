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

import ErdosProblems.Erdos735.RedBlueDualIncidence

/-!
# Red lines occupy opposite sectors at a blue crossing

This file proves the projective algebra underlying ABKPR's endpoint
restriction.  A red line through a crossing of two blue lines cannot enter
two sectors which differ in exactly one blue sign.
-/

namespace Erdos735.RedBlueDualIncidence

open Erdos735.ProjectiveDuality
open Erdos735.SignVector
open Matrix

lemma dot_comm_homogeneous (a b : Homogeneous) : dot a b = dot b a := by
  simp [dot]
  ring

lemma dot_cross_cross (u v y z : Homogeneous) :
    dot (cross u v) (cross y z) =
      dot u y * dot v z - dot u z * dot v y := by
  simp [dot, cross]
  ring

lemma dot_scale_scale (a b : ℝ) (x y : Homogeneous) :
    dot (scale a x) (scale b y) = a * b * dot x y := by
  simp [dot, scale]
  ring

/-- Determinantal relation for four lines through two incident projective
points.  If `u,v,r` all pass through `x`, while the two points `y,z` lie on
`r`, the restrictions of `u` and `v` to `r` are proportional. -/
theorem incident_dot_crossRatio
    {u v r x y z : Homogeneous}
    (hxne : x ≠ homZero) (hrne : r ≠ homZero)
    (hux : dot u x = 0) (hvx : dot v x = 0) (hrx : dot r x = 0)
    (hry : dot r y = 0) (hrz : dot r z = 0) :
    dot u y * dot v z = dot v y * dot u z := by
  by_cases huv : cross u v = homZero
  · have hdet := dot_cross_cross u v y z
    rw [huv] at hdet
    have hz : dot homZero (cross y z) = 0 := by simp [dot, homZero]
    rw [hz] at hdet
    linarith
  by_cases hyz : cross y z = homZero
  · have hdet := dot_cross_cross u v y z
    rw [hyz] at hdet
    have hz : dot (cross u v) homZero = 0 := by simp [dot, homZero]
    rw [hz] at hdet
    linarith
  obtain ⟨a, hxa⟩ := common_point_eq_scale_cross huv hux hvx
  obtain ⟨b, hrb⟩ := common_point_eq_scale_cross hyz
    ((dot_comm_homogeneous y r).trans hry) ((dot_comm_homogeneous z r).trans hrz)
  have ha : a ≠ 0 := by
    intro ha
    apply hxne
    rw [hxa, ha]
    ext <;> simp [scale, homZero]
  have hb : b ≠ 0 := by
    intro hb
    apply hrne
    rw [hrb, hb]
    ext <;> simp [scale, homZero]
  have hcrossdot : dot (cross u v) (cross y z) = 0 := by
    have hxr : dot x r = 0 := (dot_comm_homogeneous x r).trans hrx
    rw [hxa, hrb, dot_scale_scale] at hxr
    rcases mul_eq_zero.mp hxr with hab | hd
    · rcases mul_eq_zero.mp hab with ha0 | hb0
      · exact (ha ha0).elim
      · exact (hb hb0).elim
    · exact hd
  rw [dot_cross_cross] at hcrossdot
  linarith

/-- An incident red projective line cannot enter two blue sectors that
differ in exactly one of their two boundary-line signs.  This is the fully
explicit algebraic core of ABKPR's endpoint restriction. -/
theorem no_red_line_in_adjacent_sectors
    {u v r x y z : Homogeneous} (bu bv : Bool)
    (hxne : x ≠ homZero) (hrne : r ≠ homZero)
    (hux : dot u x = 0) (hvx : dot v x = 0) (hrx : dot r x = 0)
    (hry : dot r y = 0) (hrz : dot r z = 0)
    (hyu : 0 < signed bu (dot u y))
    (hyv : 0 < signed bv (dot v y))
    (hzu : 0 < signed (!bu) (dot u z))
    (hzv : 0 < signed bv (dot v z)) : False := by
  have hratio := incident_dot_crossRatio hxne hrne hux hvx hrx hry hrz
  cases bu <;> cases bv <;> simp [signed] at hyu hyv hzu hzv <;> nlinarith

/-- Symmetric endpoint restriction for crossing the second boundary line. -/
theorem no_red_line_in_adjacent_sectors_right
    {u v r x y z : Homogeneous} (bu bv : Bool)
    (hxne : x ≠ homZero) (hrne : r ≠ homZero)
    (hux : dot u x = 0) (hvx : dot v x = 0) (hrx : dot r x = 0)
    (hry : dot r y = 0) (hrz : dot r z = 0)
    (hyu : 0 < signed bu (dot u y))
    (hyv : 0 < signed bv (dot v y))
    (hzu : 0 < signed bu (dot u z))
    (hzv : 0 < signed (!bv) (dot v z)) : False := by
  have hratio := incident_dot_crossRatio hxne hrne hux hvx hrx hry hrz
  cases bu <;> cases bv <;> simp [signed] at hyu hyv hzu hzv <;> nlinarith

lemma dot_fromCoordinates_fromCoordinates (a b : Vec3) :
    ProjectiveDuality.dot (ProjectiveDuality.fromCoordinates a)
      (ProjectiveDuality.fromCoordinates b) = a ⬝ᵥ b := by
  simp [ProjectiveDuality.dot, ProjectiveDuality.fromCoordinates, vec3_dotProduct]

/-- Sign-vector form of the left adjacent-sector exclusion.  If `x` is a
common point of two blue lines and a red line, then the red restriction
cannot realize two blue faces obtained by flipping only the first blue sign. -/
theorem not_restrictedRealizable_of_flip_left
    {I : Type*} [Fintype I] (n : I → Vec3) (r x : Vec3)
    (i j : I) (s t : I → Bool)
    (hxne : x ≠ 0) (hrne : r ≠ 0)
    (hix : n i ⬝ᵥ x = 0) (hjx : n j ⬝ᵥ x = 0) (hrx : r ⬝ᵥ x = 0)
    (hti : t i = !(s i)) (htj : t j = s j)
    (hs : RestrictedRealizable n r s)
    (ht : RestrictedRealizable n r t) : False := by
  obtain ⟨y, hy, hry⟩ := hs
  obtain ⟨z, hz, hrz⟩ := ht
  apply no_red_line_in_adjacent_sectors (s i) (s j)
    (u := ProjectiveDuality.fromCoordinates (n i))
    (v := ProjectiveDuality.fromCoordinates (n j))
    (r := ProjectiveDuality.fromCoordinates r)
    (x := ProjectiveDuality.fromCoordinates x)
    (y := ProjectiveDuality.fromCoordinates y)
    (z := ProjectiveDuality.fromCoordinates z)
  · rw [← ProjectiveDuality.toCoordinates_ne_zero_iff]
    simpa using hxne
  · rw [← ProjectiveDuality.toCoordinates_ne_zero_iff]
    simpa using hrne
  · simpa [dot_fromCoordinates_fromCoordinates] using hix
  · simpa [dot_fromCoordinates_fromCoordinates] using hjx
  · simpa [dot_fromCoordinates_fromCoordinates] using hrx
  · simpa [dot_fromCoordinates_fromCoordinates] using hry
  · simpa [dot_fromCoordinates_fromCoordinates] using hrz
  · simpa [dot_fromCoordinates_fromCoordinates] using hy i
  · simpa [dot_fromCoordinates_fromCoordinates] using hy j
  · rw [← hti]
    simpa [dot_fromCoordinates_fromCoordinates] using hz i
  · rw [← htj]
    simpa [dot_fromCoordinates_fromCoordinates] using hz j

/-- Sign-vector form for flipping only the second blue sign. -/
theorem not_restrictedRealizable_of_flip_right
    {I : Type*} [Fintype I] (n : I → Vec3) (r x : Vec3)
    (i j : I) (s t : I → Bool)
    (hxne : x ≠ 0) (hrne : r ≠ 0)
    (hix : n i ⬝ᵥ x = 0) (hjx : n j ⬝ᵥ x = 0) (hrx : r ⬝ᵥ x = 0)
    (hti : t i = s i) (htj : t j = !(s j))
    (hs : RestrictedRealizable n r s)
    (ht : RestrictedRealizable n r t) : False := by
  obtain ⟨y, hy, hry⟩ := hs
  obtain ⟨z, hz, hrz⟩ := ht
  apply no_red_line_in_adjacent_sectors_right (s i) (s j)
    (u := ProjectiveDuality.fromCoordinates (n i))
    (v := ProjectiveDuality.fromCoordinates (n j))
    (r := ProjectiveDuality.fromCoordinates r)
    (x := ProjectiveDuality.fromCoordinates x)
    (y := ProjectiveDuality.fromCoordinates y)
    (z := ProjectiveDuality.fromCoordinates z)
  · rw [← ProjectiveDuality.toCoordinates_ne_zero_iff]
    simpa using hxne
  · rw [← ProjectiveDuality.toCoordinates_ne_zero_iff]
    simpa using hrne
  · simpa [dot_fromCoordinates_fromCoordinates] using hix
  · simpa [dot_fromCoordinates_fromCoordinates] using hjx
  · simpa [dot_fromCoordinates_fromCoordinates] using hrx
  · simpa [dot_fromCoordinates_fromCoordinates] using hry
  · simpa [dot_fromCoordinates_fromCoordinates] using hrz
  · simpa [dot_fromCoordinates_fromCoordinates] using hy i
  · simpa [dot_fromCoordinates_fromCoordinates] using hy j
  · rw [← hti]
    simpa [dot_fromCoordinates_fromCoordinates] using hz i
  · rw [← htj]
    simpa [dot_fromCoordinates_fromCoordinates] using hz j

/-- Exact edge-face form of the adjacent-sector exclusion.  At a nonzero
crossing point on the supporting blue line of `e` and one further blue line,
an incident red line cannot cut both strict faces separated by `e`. -/
theorem not_restrictedRealizable_both_edgeFaces
    {I : Type*} [Fintype I] [DecidableEq I]
    (n : I → Vec3) (hn : ∀ i, n i ≠ 0) (r x : Vec3)
    (e : StrictEdge n) (j : I) (hji : j ≠ e.1.1) (b : Bool)
    (hxne : x ≠ 0) (hrne : r ≠ 0)
    (hix : n e.1.1 ⬝ᵥ x = 0) (hjx : n j ⬝ᵥ x = 0)
    (hrx : r ⬝ᵥ x = 0)
    (hb : RestrictedRealizable n r (edgeFace n hn e b).1)
    (hnb : RestrictedRealizable n r (edgeFace n hn e (!b)).1) : False := by
  apply not_restrictedRealizable_of_flip_left n r x e.1.1 j
    (edgeFace n hn e b).1 (edgeFace n hn e (!b)).1
    hxne hrne hix hjx hrx
  · simp
  · exact extendEdgeSign_other e.1 (!b) hji |>.trans
      (extendEdgeSign_other e.1 b hji).symm
  · exact hb
  · exact hnb

/-- Concrete projective specialization: if a red dual line passes through
an endpoint of a blue strict edge, it cannot cut both blue faces adjacent
to that edge. -/
theorem not_redChord_both_edgeFaces_at_projective_endpoint
    (B : Finset ProjectiveBoundaryExtraction.Point)
    (e : StrictEdge (ProjectiveBoundaryExtraction.normals B))
    (v : ProjectiveBoundaryExtraction.Vertex B)
    (a : ProjectiveBoundaryExtraction.Point) (b : Bool)
    (howner : ProjectiveArrangement.Incident v.1 e.1.1.1)
    (hred : ProjectiveArrangement.Incident v.1 a)
    (hb : RestrictedRealizable (ProjectiveBoundaryExtraction.normals B)
      (ProjectiveArrangement.normalVec a)
      (edgeFace (ProjectiveBoundaryExtraction.normals B)
        (ProjectiveBoundaryExtraction.normals_ne_zero B) e b).1)
    (hnb : RestrictedRealizable (ProjectiveBoundaryExtraction.normals B)
      (ProjectiveArrangement.normalVec a)
      (edgeFace (ProjectiveBoundaryExtraction.normals B)
        (ProjectiveBoundaryExtraction.normals_ne_zero B) e (!b)).1) : False := by
  obtain ⟨j, hji, hjinc⟩ :=
    ProjectiveBoundaryExtraction.exists_other_incident_line B v e.1.1
  apply not_restrictedRealizable_both_edgeFaces
    (ProjectiveBoundaryExtraction.normals B)
    (ProjectiveBoundaryExtraction.normals_ne_zero B)
    (ProjectiveArrangement.normalVec a) v.1.rep e j hji b
  · exact v.1.rep_nonzero
  · exact ProjectiveArrangement.normalVec_ne_zero a
  · exact howner
  · exact hjinc
  · exact hred
  · exact hb
  · exact hnb

end Erdos735.RedBlueDualIncidence
