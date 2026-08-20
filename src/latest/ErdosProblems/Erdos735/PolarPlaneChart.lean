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

import ErdosProblems.Erdos735.PolarFace
import ErdosProblems.Erdos957.HullEdge

/-!
# A planar chart for the polar polygon of a sign-vector face

The normalized polar normals of a realized chamber lie in the affine plane
`p ⬝ᵥ x = 1`.  This file gives that plane an explicit injective coordinate
map to `EuclideanSpace ℝ (Fin 2)`.  The pivot coordinate is chosen from a
nonzero coordinate of `x`; hence no basis choice or extra assumption is needed.

This is the geometric entry point for applying the checked cyclic convex-hull
order from the Erdős 957 development to the boundary of each chamber.
-/

open scoped Matrix
open Matrix

namespace Erdos735.SignVector.PolarPlaneChart

noncomputable section

open Set

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def planePoint (a b : ℝ) : Plane :=
  WithLp.toLp 2 ![a, b]

@[simp] lemma planePoint_zero (a b : ℝ) : planePoint a b 0 = a := by
  rfl

@[simp] lemma planePoint_one (a b : ℝ) : planePoint a b 1 = b := by
  rfl

/-- Drop a coordinate on which the affine-plane normal is nonzero. -/
def coord (x p : Vec3) : Plane :=
  if x 2 ≠ 0 then planePoint (p 0) (p 1)
  else if x 1 ≠ 0 then planePoint (p 0) (p 2)
  else planePoint (p 1) (p 2)

lemma coord_of_two_ne {x : Vec3} (hx : x 2 ≠ 0) (p : Vec3) :
    coord x p = planePoint (p 0) (p 1) := by
  simp [coord, hx]

lemma coord_of_two_eq {x : Vec3} (hx2 : x 2 = 0) {p : Vec3} :
    coord x p =
      if x 1 ≠ 0 then planePoint (p 0) (p 2) else planePoint (p 1) (p 2) := by
  simp [coord, hx2]

/-- The chosen two coordinates determine a point of the affine polar plane. -/
theorem coord_injective_on_affinePlane {x : Vec3} (hx : x ≠ 0) :
    Set.InjOn (coord x) {p : Vec3 | p ⬝ᵥ x = 1} := by
  intro p hp q hq hpq
  by_cases hx2 : x 2 = 0
  · by_cases hx1 : x 1 = 0
    · have hx0 : x 0 ≠ 0 := by
        intro hx0
        apply hx
        funext i
        fin_cases i <;> assumption
      have hp1 : p 1 = q 1 := by
        have h := congrArg (fun z : Plane ↦ z 0) hpq
        simpa [coord, hx2, hx1] using h
      have hp2 : p 2 = q 2 := by
        have h := congrArg (fun z : Plane ↦ z 1) hpq
        simpa [coord, hx2, hx1] using h
      have hp0 : p 0 = q 0 := by
        change p ⬝ᵥ x = 1 at hp
        change q ⬝ᵥ x = 1 at hq
        rw [vec3_dotProduct] at hp hq
        have hm : (p 0 - q 0) * x 0 = 0 := by
          calc
            (p 0 - q 0) * x 0 =
                (p 0 * x 0 + p 1 * x 1 + p 2 * x 2) -
                  (q 0 * x 0 + q 1 * x 1 + q 2 * x 2) := by
                    rw [hp1, hp2]
                    ring
            _ = 0 := by rw [hp, hq]; ring
        exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right hx0)
      funext i
      fin_cases i <;> assumption
    · have hp0 : p 0 = q 0 := by
        have h := congrArg (fun z : Plane ↦ z 0) hpq
        simpa [coord, hx2, hx1] using h
      have hp2 : p 2 = q 2 := by
        have h := congrArg (fun z : Plane ↦ z 1) hpq
        simpa [coord, hx2, hx1] using h
      have hp1 : p 1 = q 1 := by
        change p ⬝ᵥ x = 1 at hp
        change q ⬝ᵥ x = 1 at hq
        rw [vec3_dotProduct] at hp hq
        have hm : (p 1 - q 1) * x 1 = 0 := by
          calc
            (p 1 - q 1) * x 1 =
                (p 0 * x 0 + p 1 * x 1 + p 2 * x 2) -
                  (q 0 * x 0 + q 1 * x 1 + q 2 * x 2) := by
                    rw [hp0, hp2]
                    ring
            _ = 0 := by rw [hp, hq]; ring
        exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right hx1)
      funext i
      fin_cases i <;> assumption
  · have hp0 : p 0 = q 0 := by
      have h := congrArg (fun z : Plane ↦ z 0) hpq
      simpa [coord, hx2] using h
    have hp1 : p 1 = q 1 := by
      have h := congrArg (fun z : Plane ↦ z 1) hpq
      simpa [coord, hx2] using h
    have hp2 : p 2 = q 2 := by
      change p ⬝ᵥ x = 1 at hp
      change q ⬝ᵥ x = 1 at hq
      rw [vec3_dotProduct] at hp hq
      have hm : (p 2 - q 2) * x 2 = 0 := by
        calc
          (p 2 - q 2) * x 2 =
              (p 0 * x 0 + p 1 * x 1 + p 2 * x 2) -
                (q 0 * x 0 + q 1 * x 1 + q 2 * x 2) := by
                  rw [hp0, hp1]
                  ring
          _ = 0 := by rw [hp, hq]; ring
      exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right hx2)
    funext i
    fin_cases i <;> assumption

/-- A concrete continuous linear functional on the coordinate plane. -/
def planeFunctional (a b : ℝ) : Plane →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y ↦ a * y 0 + b * y 1
      map_add' := by intro u v; simp; ring
      map_smul' := by intro c u; simp; ring }

@[simp] lemma planeFunctional_apply (a b : ℝ) (y : Plane) :
    planeFunctional a b y = a * y 0 + b * y 1 := by
  rfl

/-- Restrict a linear functional on homogeneous three-space to the affine
polar plane and express its nonconstant part in `coord x` coordinates. -/
def chartFunctional (x : Vec3) (l : Vec3 →L[ℝ] ℝ) : Plane →L[ℝ] ℝ :=
  let d := PolarFace.dualVector l
  if x 2 ≠ 0 then
    planeFunctional (d 0 - d 2 * x 0 / x 2) (d 1 - d 2 * x 1 / x 2)
  else if x 1 ≠ 0 then
    planeFunctional (d 0 - d 1 * x 0 / x 1) (d 2 - d 1 * x 2 / x 1)
  else
    planeFunctional (d 1 - d 0 * x 1 / x 0) (d 2 - d 0 * x 2 / x 0)

/-- Differences of a functional are preserved exactly by the planar chart
on the affine plane `p ⬝ᵥ x = 1`. -/
theorem chartFunctional_coord_sub {x p q : Vec3} (hx : x ≠ 0)
    (hp : p ⬝ᵥ x = 1) (hq : q ⬝ᵥ x = 1)
    (l : Vec3 →L[ℝ] ℝ) :
    chartFunctional x l (coord x p) - chartFunctional x l (coord x q) =
      l p - l q := by
  have hlp := PolarFace.dualVector_dot l p
  have hlq := PolarFace.dualVector_dot l q
  have hplane :
      (p 0 - q 0) * x 0 + (p 1 - q 1) * x 1 + (p 2 - q 2) * x 2 = 0 := by
    rw [vec3_dotProduct] at hp hq
    linarith
  by_cases hx2 : x 2 = 0
  · by_cases hx1 : x 1 = 0
    · have hx0 : x 0 ≠ 0 := by
        intro hx0
        apply hx
        funext i
        fin_cases i <;> assumption
      have hp0q : p 0 = q 0 := by
        have hm : (p 0 - q 0) * x 0 = 0 := by
          simpa [hx1, hx2] using hplane
        exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right hx0)
      simp [chartFunctional, coord, hx2, hx1, planeFunctional]
      rw [← hlp, ← hlq]
      simp [vec3_dotProduct, hp0q]
      ring
    · simp [chartFunctional, coord, hx2, hx1, planeFunctional]
      rw [← hlp, ← hlq]
      simp only [vec3_dotProduct]
      field_simp [hx1]
      simp [hx2] at hplane ⊢
      linear_combination -(PolarFace.dualVector l 1) * hplane
  · simp [chartFunctional, coord, hx2, planeFunctional]
    rw [← hlp, ← hlq]
    simp only [vec3_dotProduct]
    field_simp [hx2]
    linear_combination -(PolarFace.dualVector l 2) * hplane

/-- Strict comparison is transported from homogeneous polar points to their
planar coordinates. -/
theorem chartFunctional_coord_lt_iff {x p q : Vec3} (hx : x ≠ 0)
    (hp : p ⬝ᵥ x = 1) (hq : q ⬝ᵥ x = 1)
    (l : Vec3 →L[ℝ] ℝ) :
    chartFunctional x l (coord x p) < chartFunctional x l (coord x q) ↔
      l p < l q := by
  have h := chartFunctional_coord_sub hx hp hq l
  constructor <;> intro hlt <;> linarith

section FaceBoundary

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

/-- Supporting line labels of the canonical feasible edges of a face. -/
noncomputable def edgeOwners (n : I → Vec3) (s : I → Bool) : Finset I := by
  classical
  exact Finset.univ.filter fun i ↦ EdgeFeasible n (PolarFace.faceEdgeCode s i)

@[simp] lemma mem_edgeOwners {n : I → Vec3} {s : I → Bool} {i : I} :
    i ∈ edgeOwners n s ↔ EdgeFeasible n (PolarFace.faceEdgeCode s i) := by
  classical
  simp [edgeOwners]

/-- The planar point corresponding to a boundary-edge owner. -/
def ownerPoint (n : I → Vec3) (s : I → Bool) (x : Vec3) (i : I) : Plane :=
  coord x (PolarFace.polarPoint n s x i)

/-- The finite planar polar polygon, represented by its boundary owners. -/
def boundaryPolygon (n : I → Vec3) (s : I → Bool) (x : Vec3) : Finset Plane :=
  (edgeOwners n s).image (ownerPoint n s x)

lemma witness_ne_zero {n : I → Vec3} {s : I → Bool} {x : Vec3}
    (hx : Realizes n s x) : x ≠ 0 := by
  intro hx0
  let i : I := Classical.choice inferInstance
  have hi := hx i
  rw [hx0, dotProduct_zero] at hi
  cases hs : s i <;> simp [signed, hs] at hi

lemma ownerPoint_injective {n : I → Vec3} {s : I → Bool} {x : Vec3}
    (hx : Realizes n s x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0) :
    Function.Injective (ownerPoint n s x) := by
  intro i j hij
  apply PolarFace.polarPoint_injective hx hcross
  apply coord_injective_on_affinePlane (witness_ne_zero hx)
  · exact PolarFace.polarPoint_dot_witness hx i
  · exact PolarFace.polarPoint_dot_witness hx j
  · exact hij

lemma boundaryPolygon_card {n : I → Vec3} {s : I → Bool} {x : Vec3}
    (hx : Realizes n s x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0) :
    (boundaryPolygon n s x).card = (edgeOwners n s).card := by
  rw [boundaryPolygon, Finset.card_image_iff]
  intro i hi j hj hij
  exact ownerPoint_injective hx hcross hij

/-- The unique-max set of a linear functional is convex. -/
lemma convex_uniqueMaxSet_plane (l : Plane →L[ℝ] ℝ) (p : Plane) :
    Convex ℝ {z : Plane | l z ≤ l p ∧ (l p ≤ l z → z = p)} := by
  intro z hz w hw a b ha hb hab
  have hmap : l (a • z + b • w) = a * l z + b * l w := by simp
  constructor
  · rw [hmap]
    calc
      a * l z + b * l w ≤ a * l p + b * l p :=
        add_le_add (mul_le_mul_of_nonneg_left hz.1 ha)
          (mul_le_mul_of_nonneg_left hw.1 hb)
      _ = l p := by rw [← add_mul, hab, one_mul]
  · intro hge
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      have hpw : l p ≤ l w := by
        rw [hmap, ha0, hb1] at hge
        simpa using hge
      simpa [ha0, hb1, hw.2 hpw]
    by_cases hb0 : b = 0
    · have ha1 : a = 1 := by linarith
      have hpz : l p ≤ l z := by
        rw [hmap, ha1, hb0] at hge
        simpa using hge
      simpa [ha1, hb0, hz.2 hpz]
    · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      have hpz : l p ≤ l z := by
        by_contra hnle
        have hzlt : l z < l p := lt_of_not_ge hnle
        have hsum : a * l z + b * l w < a * l p + b * l p :=
          add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hzlt hapos)
            (mul_le_mul_of_nonneg_left hw.1 hb)
        rw [← add_mul, hab, one_mul] at hsum
        exact (not_lt_of_ge (hmap ▸ hge)) hsum
      have hpw : l p ≤ l w := by
        by_contra hnle
        have hwlt : l w < l p := lt_of_not_ge hnle
        have hsum : a * l z + b * l w < a * l p + b * l p :=
          add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hz.1 ha)
            (mul_lt_mul_of_pos_left hwlt hbpos)
        rw [← add_mul, hab, one_mul] at hsum
        exact (not_lt_of_ge (hmap ▸ hge)) hsum
      rw [hz.2 hpz, hw.2 hpw, ← add_smul, hab, one_smul]

lemma strictMax_mem_hullVertices_plane (A : Finset Plane) {p : Plane}
    (hp : p ∈ A) (l : Plane →L[ℝ] ℝ)
    (hstrict : ∀ q ∈ A, q ≠ p → l q < l p) :
    p ∈ Erdos957.hullVertices A := by
  rw [Erdos957.mem_hullVertices]
  have hgen : (A : Set Plane) ⊆
      {z : Plane | l z ≤ l p ∧ (l p ≤ l z → z = p)} := by
    intro q hq
    by_cases hqp : q = p
    · subst q
      exact ⟨le_rfl, fun _ ↦ rfl⟩
    · have hlt := hstrict q hq hqp
      exact ⟨hlt.le, fun h ↦ (not_le_of_gt hlt h).elim⟩
  have hhull : convexHull ℝ (A : Set Plane) ⊆
      {z : Plane | l z ≤ l p ∧ (l p ≤ l z → z = p)} :=
    convexHull_min hgen (convex_uniqueMaxSet_plane l p)
  refine exposedPoints_subset_extremePoints
    ⟨subset_convexHull ℝ (A : Set Plane) hp, l, ?_⟩
  intro q hq
  have hqmax := hhull hq
  exact ⟨hqmax.1, hqmax.2⟩

/-- Every feasible canonical face edge becomes a vertex of the planar polar
polygon. -/
lemma ownerPoint_mem_hullVertices {n : I → Vec3} {s : I → Bool} {x : Vec3}
    (hx : Realizes n s x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    {i : I} (hi : i ∈ edgeOwners n s) :
    ownerPoint n s x i ∈ Erdos957.hullVertices (boundaryPolygon n s x) := by
  have hextreme : PolarFace.polarPoint n s x i ∈
      (convexHull ℝ (PolarFace.polarPoints n s x : Set Vec3)).extremePoints ℝ :=
    (PolarFace.edgeFeasible_faceEdgeCode_iff_extreme hx hcross i).mp
      (mem_edgeOwners.mp hi)
  obtain ⟨l, -, hstrict⟩ :=
    PolarFace.extremePoint_exists_strictMax (PolarFace.polarPoints n s x) hextreme
  apply strictMax_mem_hullVertices_plane (A := boundaryPolygon n s x)
    (l := chartFunctional x l)
  · exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  · intro q hq hqne
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
    have hji : j ≠ i := by
      intro hji
      subst j
      exact hqne rfl
    change chartFunctional x l (coord x (PolarFace.polarPoint n s x j)) <
      chartFunctional x l (coord x (PolarFace.polarPoint n s x i))
    rw [chartFunctional_coord_lt_iff (witness_ne_zero hx)
      (PolarFace.polarPoint_dot_witness hx j)
      (PolarFace.polarPoint_dot_witness hx i)]
    exact hstrict _ (PolarFace.polarPoint_mem_polarPoints n s x j)
      ((PolarFace.polarPoint_injective hx hcross).ne hji)

/-- The polar polygon has no nonvertex generators: it is exactly the image
of the feasible canonical face-edge owners. -/
theorem hullVertices_boundaryPolygon {n : I → Vec3} {s : I → Bool} {x : Vec3}
    (hx : Realizes n s x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0) :
    Erdos957.hullVertices (boundaryPolygon n s x) = boundaryPolygon n s x := by
  apply Finset.Subset.antisymm
  · exact Erdos957.hullVertices_subset _
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    exact ownerPoint_mem_hullVertices hx hcross hi

/-- Canonical face-edge owners are in bijection with the actual strict edges
incident with the face. -/
theorem edgeOwners_card_eq_faceEdges {n : I → Vec3} (f : StrictFace n) :
    (edgeOwners n f.1).card = (faceEdges n f).card := by
  classical
  apply Finset.card_bij
      (fun i hi ↦
        (⟨PolarFace.faceEdgeCode f.1 i,
          (mem_edgeOwners.mp hi)⟩ : StrictEdge n))
  · intro i hi
    rw [mem_faceEdges_iff]
    intro j
    rfl
  · intro i hi j hj hij
    have howner := congrArg (fun e : StrictEdge n ↦ e.1.1) hij
    exact howner
  · intro e he
    rcases e with ⟨⟨k, t⟩, hfeasibleE⟩
    let i : I := k
    change (⟨⟨k, t⟩, hfeasibleE⟩ : StrictEdge n) ∈ faceEdges n f at he
    have hinc := (mem_faceEdges_iff n f
      (⟨⟨k, t⟩, hfeasibleE⟩ : StrictEdge n)).mp he
    have hcode : PolarFace.faceEdgeCode f.1 i = (⟨k, t⟩ : EdgeCode I) := by
      change (⟨k, fun j ↦ f.1 j.1⟩ : EdgeCode I) = ⟨k, t⟩
      congr 1
      funext j
      exact hinc j
    have hfeasible : EdgeFeasible n (PolarFace.faceEdgeCode f.1 i) := by
      rw [hcode]
      exact hfeasibleE
    refine ⟨i, mem_edgeOwners.mpr hfeasible, ?_⟩
    apply Subtype.ext
    exact hcode

/-- Full rank gives at least three vertices of every planar polar boundary. -/
theorem three_le_hullVertices_boundaryPolygon
    {n : I → Vec3} (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤) (f : StrictFace n)
    (x : Vec3) (hx : Realizes n f.1 x) :
    3 ≤ (Erdos957.hullVertices (boundaryPolygon n f.1 x)).card := by
  rw [hullVertices_boundaryPolygon hx hcross, boundaryPolygon_card hx hcross,
    edgeOwners_card_eq_faceEdges f]
  exact PolarFace.faceEdges_card_three_le_of_span_eq_top n hcross hspan f

/-- The checked gift-wrapping order of the genuine owner-preserving polar
boundary of a strict face. -/
noncomputable def cyclicBoundaryOrder
    {n : I → Vec3} (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤) (f : StrictFace n) :
    Erdos957.CyclicHullOrder
      (boundaryPolygon n f.1 (Classical.choose f.2)) :=
  Erdos957.cyclicHullOrderOfThree _
    (three_le_hullVertices_boundaryPolygon hcross hspan f
      (Classical.choose f.2) (Classical.choose_spec f.2))

end FaceBoundary

end

end Erdos735.SignVector.PolarPlaneChart
