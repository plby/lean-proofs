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
import ErdosProblems.Erdos735.ProjectiveArrangement
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Polar convex hull of a strict sign-vector face

Fix a point `x` realizing a strict face of a central arrangement in real
three-space.  Orient every normal toward that face and divide it by its
positive value at `x`.  The resulting polar points all lie in the affine
plane `p ⬝ᵥ x = 1`.

For a supporting index `i`, restrict the face signs to the other indices.
This is a feasible open edge on `n i` precisely when the corresponding polar
point is a vertex of the finite polar convex hull.  This canonical formulation
is important: an arbitrary feasible edge supported on `i` can carry the signs
of a different face, so its support index alone does not determine incidence.
-/

open Set
open scoped Matrix
open Matrix

namespace Erdos735.SignVector.PolarFace

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The scalar `+1` or `-1` encoded by a Boolean sign. -/
def signScalar (b : Bool) : ℝ := if b then 1 else -1

lemma signScalar_ne_zero (b : Bool) : signScalar b ≠ 0 := by
  cases b <;> simp [signScalar]

lemma signScalar_mul_self (b : Bool) : signScalar b * signScalar b = 1 := by
  cases b <;> simp [signScalar]

lemma signed_eq_signScalar_mul (b : Bool) (r : ℝ) :
    signed b r = signScalar b * r := by
  cases b <;> simp [signed, signScalar]

/-- The normal oriented toward the chamber selected by `s`. -/
def orientedNormal (n : I → Vec3) (s : I → Bool) (i : I) : Vec3 :=
  signScalar (s i) • n i

lemma orientedNormal_dot (n : I → Vec3) (s : I → Bool) (x : Vec3) (i : I) :
    orientedNormal n s i ⬝ᵥ x = signed (s i) (n i ⬝ᵥ x) := by
  rw [orientedNormal, smul_dotProduct, signed_eq_signScalar_mul]
  rfl

lemma signScalar_smul_orientedNormal (n : I → Vec3) (s : I → Bool) (i : I) :
    signScalar (s i) • orientedNormal n s i = n i := by
  simp only [orientedNormal, smul_smul]
  rw [signScalar_mul_self, one_smul]

/-- The positive denominator used to put an oriented normal in the affine
polar chart determined by `x`. -/
def polarDenom (n : I → Vec3) (s : I → Bool) (x : Vec3) (i : I) : ℝ :=
  signed (s i) (n i ⬝ᵥ x)

/-- The normalized polar point attached to supporting index `i`. -/
def polarPoint (n : I → Vec3) (s : I → Bool) (x : Vec3) (i : I) : Vec3 :=
  (polarDenom n s x i)⁻¹ • orientedNormal n s i

lemma polarDenom_pos {n : I → Vec3} {s : I → Bool} {x : Vec3}
    (hx : Realizes n s x) (i : I) : 0 < polarDenom n s x i :=
  hx i

lemma polarDenom_ne_zero {n : I → Vec3} {s : I → Bool} {x : Vec3}
    (hx : Realizes n s x) (i : I) : polarDenom n s x i ≠ 0 :=
  (polarDenom_pos hx i).ne'

/-- Every polar point belongs to the affine plane with equation `p ⬝ᵥ x = 1`. -/
lemma polarPoint_dot_witness {n : I → Vec3} {s : I → Bool} {x : Vec3}
    (hx : Realizes n s x) (i : I) : polarPoint n s x i ⬝ᵥ x = 1 := by
  rw [polarPoint, smul_dotProduct, orientedNormal_dot]
  exact inv_mul_cancel₀ (polarDenom_ne_zero hx i)

lemma orientedNormal_eq_denom_smul_polarPoint
    {n : I → Vec3} {s : I → Bool} {x : Vec3}
    (hx : Realizes n s x) (i : I) :
    orientedNormal n s i = polarDenom n s x i • polarPoint n s x i := by
  rw [polarPoint, smul_smul, mul_inv_cancel₀ (polarDenom_ne_zero hx i), one_smul]

/-- Pairwise projectively distinct normals give pairwise distinct polar
points in every realized affine chart. -/
lemma polarPoint_injective {n : I → Vec3} {s : I → Bool} {x : Vec3}
    (hx : Realizes n s x) (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0) :
    Function.Injective (polarPoint n s x) := by
  intro i j hij
  by_contra hne
  apply hcross i j hne
  rw [← signScalar_smul_orientedNormal n s i,
    ← signScalar_smul_orientedNormal n s j,
    orientedNormal_eq_denom_smul_polarPoint hx i,
    orientedNormal_eq_denom_smul_polarPoint hx j,
    hij]
  simp

/-- The finite set of normalized polar points of the face. -/
def polarPoints (n : I → Vec3) (s : I → Bool) (x : Vec3) : Finset Vec3 :=
  Finset.univ.image (polarPoint n s x)

lemma polarPoint_mem_polarPoints (n : I → Vec3) (s : I → Bool)
    (x : Vec3) (i : I) : polarPoint n s x i ∈ polarPoints n s x := by
  classical
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

/-- The edge code canonically obtained by restricting a face sign pattern
away from one supporting index. -/
def faceEdgeCode (s : I → Bool) (i : I) : EdgeCode I :=
  ⟨i, fun j ↦ s j.1⟩

@[simp] lemma faceEdgeCode_support (s : I → Bool) (i : I) :
    (faceEdgeCode s i).1 = i := rfl

@[simp] lemma faceEdgeCode_other (s : I → Bool) (i : I)
    (j : {j : I // j ≠ i}) : (faceEdgeCode s i).2 j = s j.1 := rfl

/-! ## Finite convex-hull separation -/

/-- The set on which `p` is the unique maximizer of `l` is convex.  This
elementary lemma lets a strict maximum on a finite generating set extend to
the whole convex hull without choosing barycentric coordinates. -/
lemma convex_uniqueMaxSet (l : Vec3 →L[ℝ] ℝ) (p : Vec3) :
    Convex ℝ {z : Vec3 | l z ≤ l p ∧ (l p ≤ l z → z = p)} := by
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

/-- A strict linear maximum on the finite generators is an extreme point of
their convex hull. -/
lemma strictMax_mem_extremePoints_convexHull (A : Finset Vec3) {p : Vec3}
    (hp : p ∈ A) (l : Vec3 →L[ℝ] ℝ)
    (hstrict : ∀ q ∈ A, q ≠ p → l q < l p) :
    p ∈ (convexHull ℝ (A : Set Vec3)).extremePoints ℝ := by
  have hgen : (A : Set Vec3) ⊆
      {z : Vec3 | l z ≤ l p ∧ (l p ≤ l z → z = p)} := by
    intro q hq
    by_cases hqp : q = p
    · subst q
      exact ⟨le_rfl, fun _ ↦ rfl⟩
    · have hlt := hstrict q hq hqp
      exact ⟨hlt.le, fun h ↦ (not_le_of_gt hlt h).elim⟩
  have hhull : convexHull ℝ (A : Set Vec3) ⊆
      {z : Vec3 | l z ≤ l p ∧ (l p ≤ l z → z = p)} :=
    convexHull_min hgen (convex_uniqueMaxSet l p)
  refine exposedPoints_subset_extremePoints ⟨subset_convexHull ℝ (A : Set Vec3) hp, l, ?_⟩
  intro q hq
  have hqmax := hhull hq
  exact ⟨hqmax.1, hqmax.2⟩

/-- Every extreme point of a finite convex hull admits a functional which is
strictly larger there than at every other generator. -/
lemma extremePoint_exists_strictMax (A : Finset Vec3) {p : Vec3}
    (hp : p ∈ (convexHull ℝ (A : Set Vec3)).extremePoints ℝ) :
    ∃ l : Vec3 →L[ℝ] ℝ,
      (∀ q ∈ A, l q ≤ l p) ∧
      (∀ q ∈ A, q ≠ p → l q < l p) := by
  have hpnotLarge :
      p ∉ convexHull ℝ (convexHull ℝ (A : Set Vec3) \ {p}) :=
    ((convex_convexHull ℝ (A : Set Vec3)).mem_extremePoints_iff_mem_sdiff_convexHull_sdiff.mp
      hp).2
  have heraseSubset : (A.erase p : Set Vec3) ⊆
      convexHull ℝ (A : Set Vec3) \ {p} := by
    intro q hq
    have hq' := Finset.mem_erase.mp hq
    exact ⟨subset_convexHull ℝ (A : Set Vec3) hq'.2, hq'.1⟩
  have hpnot : p ∉ convexHull ℝ (A.erase p : Set Vec3) := by
    intro hpErase
    exact hpnotLarge (convexHull_mono heraseSubset hpErase)
  have hclosed : IsClosed (convexHull ℝ (A.erase p : Set Vec3)) :=
    (Set.Finite.isCompact_convexHull ℝ (A.erase p).finite_toSet).isClosed
  obtain ⟨l, u, hlt, hulp⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (A.erase p : Set Vec3)) hclosed hpnot
  refine ⟨l, ?_, ?_⟩
  · intro q hq
    by_cases hqp : q = p
    · simpa [hqp]
    · exact (hlt q (subset_convexHull ℝ _
        (Finset.mem_erase.mpr ⟨hqp, hq⟩))).le.trans hulp.le
  · intro q hq hqp
    exact (hlt q (subset_convexHull ℝ _
      (Finset.mem_erase.mpr ⟨hqp, hq⟩))).trans hulp

/-! ## Linear functionals as concrete dot products -/

/-- Coordinate vector representing a real linear functional on `Vec3`. -/
def dualVector (l : Vec3 →L[ℝ] ℝ) : Vec3 :=
  ![l ![1, 0, 0], l ![0, 1, 0], l ![0, 0, 1]]

lemma dualVector_dot (l : Vec3 →L[ℝ] ℝ) (z : Vec3) :
    dualVector l ⬝ᵥ z = l z := by
  have hz : z = z 0 • ![1, 0, 0] + z 1 • ![0, 1, 0] + z 2 • ![0, 0, 1] := by
    funext k
    fin_cases k <;> simp
  rw [hz, map_add, map_add, map_smul, map_smul, map_smul, vec3_dotProduct]
  simp [dualVector]
  ring

/-- Dot product with a fixed vector, bundled as a continuous linear map. -/
def dotCLM (y : Vec3) : Vec3 →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z ↦ z ⬝ᵥ y
      map_add' := fun z w ↦ by simp [add_dotProduct]
      map_smul' := fun a z ↦ by simp [smul_dotProduct] }

@[simp] lemma dotCLM_apply (y z : Vec3) : dotCLM y z = z ⬝ᵥ y := by
  rfl

/-- Shift the negative representing vector of `l` by `l p` times the face
witness.  On the affine plane `q ⬝ᵥ x = 1`, dotting with this vector is
exactly `l p - l q`. -/
def separatorVector (l : Vec3 →L[ℝ] ℝ) (p x : Vec3) : Vec3 :=
  (l p) • x - dualVector l

lemma polarPoint_dot_separatorVector
    {n : I → Vec3} {s : I → Bool} {x : Vec3}
    (hx : Realizes n s x) (l : Vec3 →L[ℝ] ℝ) (p : Vec3) (i : I) :
    polarPoint n s x i ⬝ᵥ separatorVector l p x = l p - l (polarPoint n s x i) := by
  rw [separatorVector, dotProduct_sub, dotProduct_smul,
    polarPoint_dot_witness hx,
    dotProduct_comm (polarPoint n s x i) (dualVector l), dualVector_dot]
  ring

/-! ## Feasible face edges are exactly polar vertices -/

/-- The canonical edge at index `i` is feasible exactly when the normalized
polar point at `i` is an extreme point of the finite polar convex hull. -/
theorem edgeFeasible_faceEdgeCode_iff_extreme
    {n : I → Vec3} {s : I → Bool} {x : Vec3}
    (hx : Realizes n s x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0) (i : I) :
    EdgeFeasible n (faceEdgeCode s i) ↔
      polarPoint n s x i ∈
        (convexHull ℝ (polarPoints n s x : Set Vec3)).extremePoints ℝ := by
  constructor
  · rintro ⟨y, hy, hyzero⟩
    let l : Vec3 →L[ℝ] ℝ := -(dotCLM y)
    apply strictMax_mem_extremePoints_convexHull (polarPoints n s x)
      (polarPoint_mem_polarPoints n s x i) l
    intro q hq hqi
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hq
    have hji : j ≠ i := by
      intro hji
      subst j
      exact hqi rfl
    have hjpos : 0 < polarPoint n s x j ⬝ᵥ y := by
      rw [polarPoint, smul_dotProduct, orientedNormal_dot]
      exact mul_pos (inv_pos.mpr (polarDenom_pos hx j)) (hy ⟨j, hji⟩)
    have hipolar : polarPoint n s x i ⬝ᵥ y = 0 := by
      have hyzero' : n i ⬝ᵥ y = 0 := by simpa using hyzero
      rw [polarPoint, smul_dotProduct, orientedNormal_dot, hyzero']
      cases s i <;> simp [signed]
    simp only [l, ContinuousLinearMap.neg_apply, dotCLM_apply]
    linarith
  · intro hextreme
    obtain ⟨l, -, hstrict⟩ :=
      extremePoint_exists_strictMax (polarPoints n s x) hextreme
    let y := separatorVector l (polarPoint n s x i) x
    refine ⟨y, ?_, ?_⟩
    · intro j
      have hji : j.1 ≠ i := j.2
      have hpneq : polarPoint n s x j.1 ≠ polarPoint n s x i :=
        (polarPoint_injective hx hcross).ne hji
      have hlt := hstrict (polarPoint n s x j.1)
        (polarPoint_mem_polarPoints n s x j.1) hpneq
      have hpolar : 0 < polarPoint n s x j.1 ⬝ᵥ y := by
        rw [polarPoint_dot_separatorVector hx]
        exact sub_pos.mpr hlt
      rw [polarPoint, smul_dotProduct, orientedNormal_dot] at hpolar
      change 0 < (polarDenom n s x j.1)⁻¹ *
        signed (s j.1) (n j.1 ⬝ᵥ y) at hpolar
      change 0 < signed (s j.1) (n j.1 ⬝ᵥ y)
      rcases mul_pos_iff.mp hpolar with hgood | hbad
      · exact hgood.2
      · exact (not_lt_of_ge (inv_pos.mpr (polarDenom_pos hx j.1)).le hbad.1).elim
    · have hpolar : polarPoint n s x i ⬝ᵥ y = 0 := by
        rw [polarPoint_dot_separatorVector hx]
        exact sub_self _
      rw [polarPoint, smul_dotProduct, orientedNormal_dot] at hpolar
      have hsigned : signed (s i) (n i ⬝ᵥ y) = 0 :=
        (mul_eq_zero.mp hpolar).resolve_left
          (inv_ne_zero (polarDenom_ne_zero hx i))
      cases hsi : s i <;> simp [signed, hsi] at hsigned ⊢
      · exact hsigned
      · exact hsigned

/-! ## Full span gives at least three face edges -/

/-- The extreme points of the finite polar hull, represented as a finset. -/
noncomputable def polarVertices (n : I → Vec3) (s : I → Bool)
    (x : Vec3) : Finset Vec3 := by
  classical
  exact (polarPoints n s x).filter fun p ↦
    p ∈ (convexHull ℝ (polarPoints n s x : Set Vec3)).extremePoints ℝ

@[simp] lemma mem_polarVertices {n : I → Vec3} {s : I → Bool}
    {x p : Vec3} :
    p ∈ polarVertices n s x ↔
      p ∈ (convexHull ℝ (polarPoints n s x : Set Vec3)).extremePoints ℝ := by
  classical
  rw [polarVertices, Finset.mem_filter]
  constructor
  · exact fun h ↦ h.2
  · intro hp
    exact ⟨extremePoints_convexHull_subset hp, hp⟩

/-- Rescaling each normal by the nonzero polar normalization preserves full
linear span. -/
lemma span_polarPoints_eq_top_of_span_normals_eq_top
    {n : I → Vec3} {s : I → Bool} {x : Vec3}
    (hx : Realizes n s x)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤) :
    Submodule.span ℝ (polarPoints n s x : Set Vec3) = ⊤ := by
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro v ⟨i, rfl⟩
  rw [← signScalar_smul_orientedNormal n s i,
    orientedNormal_eq_denom_smul_polarPoint hx i]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
    (Submodule.subset_span (R := ℝ) (polarPoint_mem_polarPoints n s x i)))

/-- Krein--Milman, specialized to a finite polar hull: if all polar points
span three-space, then its (finite) vertex set still spans three-space. -/
lemma span_polarVertices_eq_top_of_span_normals_eq_top
    {n : I → Vec3} {s : I → Bool} {x : Vec3}
    (hx : Realizes n s x)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤) :
    Submodule.span ℝ (polarVertices n s x : Set Vec3) = ⊤ := by
  let P := polarPoints n s x
  let H := convexHull ℝ (P : Set Vec3)
  let V := polarVertices n s x
  have hV : (V : Set Vec3) = H.extremePoints ℝ := by
    ext p
    exact mem_polarVertices
  have hcompact : IsCompact H :=
    Set.Finite.isCompact_convexHull ℝ P.finite_toSet
  have hkrein : closure (convexHull ℝ (V : Set Vec3)) = H := by
    rw [hV]
    exact closure_convexHull_extremePoints hcompact (convex_convexHull ℝ _)
  have hconvSpan : convexHull ℝ (V : Set Vec3) ⊆
      Submodule.span ℝ (V : Set Vec3) :=
    convexHull_min Submodule.subset_span (Submodule.convex _)
  have hclosureSpan : closure (convexHull ℝ (V : Set Vec3)) ⊆
      Submodule.span ℝ (V : Set Vec3) :=
    closure_minimal hconvSpan (Submodule.closed_of_finiteDimensional _)
  have hPSpan : (P : Set Vec3) ⊆ Submodule.span ℝ (V : Set Vec3) := by
    intro p hp
    apply hclosureSpan
    rw [hkrein]
    exact subset_convexHull ℝ (P : Set Vec3) hp
  apply top_unique
  rw [← span_polarPoints_eq_top_of_span_normals_eq_top hx hspan]
  exact Submodule.span_le.mpr hPSpan

/-- Supporting indices whose polar point is a vertex. -/
noncomputable def extremeIndices (n : I → Vec3) (s : I → Bool)
    (x : Vec3) : Finset I := by
  classical
  exact Finset.univ.filter fun i ↦ polarPoint n s x i ∈ polarVertices n s x

@[simp] lemma mem_extremeIndices {n : I → Vec3} {s : I → Bool}
    {x : Vec3} {i : I} :
    i ∈ extremeIndices n s x ↔ polarPoint n s x i ∈ polarVertices n s x := by
  classical
  simp [extremeIndices]

lemma image_extremeIndices_eq_polarVertices
    {n : I → Vec3} {s : I → Bool} {x : Vec3} :
    (extremeIndices n s x).image (polarPoint n s x) = polarVertices n s x := by
  classical
  ext p
  constructor
  · rintro hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    exact mem_extremeIndices.mp hi
  · intro hp
    have hpP : p ∈ polarPoints n s x :=
      extremePoints_convexHull_subset (mem_polarVertices.mp hp)
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hpP
    exact Finset.mem_image.mpr ⟨i, mem_extremeIndices.mpr hp, rfl⟩

lemma card_extremeIndices_eq_card_polarVertices
    {n : I → Vec3} {s : I → Bool} {x : Vec3}
    (hx : Realizes n s x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0) :
    (extremeIndices n s x).card = (polarVertices n s x).card := by
  rw [← image_extremeIndices_eq_polarVertices,
    Finset.card_image_of_injective _ (polarPoint_injective hx hcross)]

/-- An extreme supporting index determines the canonical feasible edge with
the face's signs on every other normal. -/
def extremeIndexEdge {n : I → Vec3} {s : I → Bool} {x : Vec3}
    (hx : Realizes n s x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (i : {i // i ∈ extremeIndices n s x}) : StrictEdge n :=
  ⟨faceEdgeCode s i.1,
    (edgeFeasible_faceEdgeCode_iff_extreme hx hcross i.1).2
      (mem_polarVertices.mp (mem_extremeIndices.mp i.2))⟩

lemma extremeIndexEdge_incident {n : I → Vec3} {s : I → Bool} {x : Vec3}
    (hx : Realizes n s x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (f : StrictFace n) (hs : f.1 = s)
    (i : {i // i ∈ extremeIndices n s x}) :
    extremeIndexEdge hx hcross i ∈ faceEdges n f := by
  rw [mem_faceEdges_iff]
  intro j
  simpa [extremeIndexEdge, faceEdgeCode, hs]

lemma extremeIndexEdge_injective {n : I → Vec3} {s : I → Bool} {x : Vec3}
    (hx : Realizes n s x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0) :
    Function.Injective (extremeIndexEdge hx hcross) := by
  intro i j hij
  apply Subtype.ext
  have howner := congrArg (fun e : StrictEdge n ↦ e.1.1) hij
  exact howner

/-- A rank-three, pairwise projectively distinct central arrangement has at
least three edges on every strict face.  This is the concrete degree field
needed by `BoundaryExtraction`. -/
theorem faceEdges_card_three_le_of_span_eq_top
    (n : I → Vec3)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (f : StrictFace n) :
    3 ≤ (faceEdges n f).card := by
  let x : Vec3 := Classical.choose f.2
  have hx : Realizes n f.1 x := Classical.choose_spec f.2
  let E := extremeIndices n f.1 x
  let V := polarVertices n f.1 x
  have hspanV : Submodule.span ℝ (V : Set Vec3) = ⊤ :=
    span_polarVertices_eq_top_of_span_normals_eq_top hx hspan
  have hthreeV : 3 ≤ V.card := by
    have hfin : Module.finrank ℝ (Submodule.span ℝ (V : Set Vec3)) ≤ V.card :=
      finrank_span_finset_le_card V
    rw [hspanV] at hfin
    simpa using hfin
  have hcardEV : E.card = V.card :=
    card_extremeIndices_eq_card_polarVertices hx hcross
  let edgeInFace : {i // i ∈ E} → {e // e ∈ faceEdges n f} := fun i ↦
    ⟨extremeIndexEdge hx hcross i,
      extremeIndexEdge_incident hx hcross f rfl i⟩
  have hedgeInj : Function.Injective edgeInFace := by
    intro i j hij
    apply extremeIndexEdge_injective hx hcross
    exact congrArg Subtype.val hij
  have hcard : E.card ≤ (faceEdges n f).card := by
    simpa [edgeInFace] using Fintype.card_le_of_injective edgeInFace hedgeInj
  rw [hcardEV] at hcard
  exact hthreeV.trans hcard

/-- Concrete affine-dual specialization.  A noncollinear triple in `B`
supplies full rank, while distinct subtype indices give cross-independent
normals `![p 0, p 1, 1]`; hence every strict face of the dual arrangement has
at least three boundary edges. -/
theorem normalVec_faceEdges_card_three_le
    (B : Finset ProjectiveArrangement.Point)
    {p q r : ProjectiveArrangement.Point}
    (hp : p ∈ B) (hq : q ∈ B) (hr : r ∈ B)
    (hncol : ¬ ProjectiveDuality.Collinear3 p q r)
    (f : StrictFace
      (fun b : {x // x ∈ B} ↦ ProjectiveArrangement.normalVec b.1)) :
    3 ≤ (faceEdges
      (fun b : {x // x ∈ B} ↦ ProjectiveArrangement.normalVec b.1) f).card := by
  classical
  apply faceEdges_card_three_le_of_span_eq_top
  · intro i j hij
    exact ProjectiveArrangement.normalVec_cross_ne_zero fun hpoints ↦
      hij (Subtype.ext hpoints)
  · exact ProjectiveArrangement.span_normalVec_range_eq_top_of_noncollinear_triple
      B hp hq hr hncol

end

end Erdos735.SignVector.PolarFace
