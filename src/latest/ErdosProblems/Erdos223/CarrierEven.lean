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

import ErdosProblems.Erdos223.Basic
import ErdosProblems.Erdos223.Asymptotic
import ErdosProblems.Erdos223.CompleteBipartiteGeometry
import ErdosProblems.Erdos223.ExactLower
import ErdosProblems.Erdos223.LenzOptimization
import ErdosProblems.Erdos223.LocalCircle
import ErdosProblems.Erdos223.Obstruction
import ErdosProblems.Erdos223.Stability
import Mathlib.Geometry.Euclidean.Circumcenter

/-!
# Even-dimensional Lenz carriers for Erdős Problem 223

This file packages the geometric conclusion of the even-dimensional carrier
argument.  A carrier in `Point (2 * p)` is a family of `p` two-dimensional
affine planes with one common centre, pairwise orthogonal direction spaces,
and circle radii whose squared radii add to one in every two distinct parts.
Thus points on different carrier circles are automatically at distance one.

The definition includes the exceptional dimension four: there the two radii
may differ.  As soon as there are at least three circles, the complementary
radius equations force every squared radius to equal `1 / 2`.
-/

open Metric
open scoped BigOperators EuclideanGeometry RealInnerProductSpace SimpleGraph

namespace Erdos223

noncomputable section

/-- A family of mutually orthogonal, concentric circles in `Point (2 * p)`
whose cross-circle distances are one.  We retain the affine carrier planes
and radii because the dimension-four radii need not agree. -/
structure EvenCircleCarrier (p : ℕ) where
  center : Point (2 * p)
  plane : Fin p → AffineSubspace ℝ (Point (2 * p))
  radius : Fin p → ℝ
  center_mem : ∀ i, center ∈ plane i
  plane_finrank : ∀ i, Module.finrank ℝ (plane i).direction = 2
  direction_isOrtho : ∀ {i j}, i ≠ j → (plane i).direction ⟂ (plane j).direction
  radius_nonneg : ∀ i, 0 ≤ radius i
  radius_sq_add : ∀ {i j}, i ≠ j → radius i ^ 2 + radius j ^ 2 = 1

namespace EvenCircleCarrier

variable {p : ℕ} (C : EvenCircleCarrier p)

/-- The `i`th carrier circle. -/
def circle (i : Fin p) : Set (Point (2 * p)) :=
  {x | x ∈ C.plane i ∧ dist x C.center = C.radius i}

@[simp] theorem mem_circle {i : Fin p} {x : Point (2 * p)} :
    x ∈ C.circle i ↔ x ∈ C.plane i ∧ dist x C.center = C.radius i :=
  Iff.rfl

/-- The displacement from the common centre of a point on one carrier
circle belongs to that carrier's direction space. -/
theorem vsub_center_mem_direction {i : Fin p} {x : Point (2 * p)}
    (hx : x ∈ C.circle i) : x -ᵥ C.center ∈ (C.plane i).direction :=
  AffineSubspace.vsub_mem_direction hx.1 (C.center_mem i)

/-- Displacements of points on two different carrier circles are
orthogonal. -/
theorem inner_vsub_center_eq_zero {i j : Fin p} (hij : i ≠ j)
    {x y : Point (2 * p)} (hx : x ∈ C.circle i) (hy : y ∈ C.circle j) :
    inner ℝ (x -ᵥ C.center) (y -ᵥ C.center) = 0 := by
  have horth := C.direction_isOrtho hij
  rw [Submodule.isOrtho_iff_inner_eq] at horth
  exact horth _ (C.vsub_center_mem_direction hx) _
    (C.vsub_center_mem_direction hy)

/-- Every cross-circle pair on an even Lenz carrier is a unit-distance
pair. -/
theorem dist_eq_one_of_mem_circle_of_ne {i j : Fin p} (hij : i ≠ j)
    {x y : Point (2 * p)} (hx : x ∈ C.circle i) (hy : y ∈ C.circle j) :
    dist x y = 1 := by
  have hinner := C.inner_vsub_center_eq_zero hij hx hy
  have hnorm : ‖(x -ᵥ C.center) - (y -ᵥ C.center)‖ ^ 2 =
      ‖x -ᵥ C.center‖ ^ 2 + ‖y -ᵥ C.center‖ ^ 2 :=
    by simpa [pow_two] using norm_sub_sq_eq_norm_sq_add_norm_sq_real hinner
  have hxnorm : ‖x -ᵥ C.center‖ = C.radius i := by
    simpa [dist_eq_norm_vsub] using hx.2
  have hynorm : ‖y -ᵥ C.center‖ = C.radius j := by
    simpa [dist_eq_norm_vsub] using hy.2
  have hsq : dist x y ^ 2 = 1 := by
    rw [dist_eq_norm_vsub]
    rw [show x -ᵥ y = (x -ᵥ C.center) - (y -ᵥ C.center) by
      simp [vsub_eq_sub]]
    rw [hnorm, hxnorm, hynorm, C.radius_sq_add hij]
  nlinarith [show 0 ≤ dist x y from dist_nonneg]

/-- With three or more carrier circles, all squared radii are one half. -/
theorem radius_sq_eq_half (hp : 3 ≤ p) (i : Fin p) :
    C.radius i ^ 2 = (1 : ℝ) / 2 := by
  obtain ⟨j, hji, -⟩ := Fin.exists_ne_and_ne_of_two_lt i i (by omega : 2 < p)
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega : 2 < p)
  have hij' := C.radius_sq_add hji.symm
  have hik := C.radius_sq_add hki.symm
  have hjk := C.radius_sq_add hkj.symm
  nlinarith

/-- In dimensions at least six the nonnegative carrier radii equal
`1 / sqrt 2`. -/
theorem radius_eq_inv_sqrt_two (hp : 3 ≤ p) (i : Fin p) :
    C.radius i = 1 / Real.sqrt 2 := by
  have hsqrt : Real.sqrt (2 : ℝ) ^ 2 = 2 := by norm_num
  have hsqrtpos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsq := C.radius_sq_eq_half hp i
  have htargetsq : (1 / Real.sqrt (2 : ℝ)) ^ 2 = 1 / 2 := by
    rw [div_pow, one_pow, hsqrt]
  nlinarith [C.radius_nonneg i, (one_div_pos.mpr hsqrtpos).le]

/-- Distinct circles of a Lenz carrier are disjoint.  Otherwise the same
point, viewed in two different parts, would have distance one from itself. -/
theorem disjoint_circle {i j : Fin p} (hij : i ≠ j) :
    Disjoint (C.circle i) (C.circle j) := by
  rw [Set.disjoint_left]
  intro x hxi hxj
  have h := C.dist_eq_one_of_mem_circle_of_ne hij hxi hxj
  have hzero : dist x x = 0 := dist_self x
  linarith

/-- The carrier circle containing a point is unique. -/
theorem circle_index_unique {i j : Fin p} {x : Point (2 * p)}
    (hxi : x ∈ C.circle i) (hxj : x ∈ C.circle j) : i = j := by
  by_contra hij
  exact Set.disjoint_left.mp (C.disjoint_circle hij) hxi hxj

end EvenCircleCarrier

/-- A finite set is an even-dimensional Lenz configuration if it is
contained in the union of the circles of an `EvenCircleCarrier`. -/
def IsEvenLenz {p : ℕ} (A : Finset (Point (2 * p))) : Prop :=
  ∃ C : EvenCircleCarrier p, ∀ x ∈ A, ∃ i, x ∈ C.circle i

/-! ## The geometric carrier forced by complete multipartite triples -/

namespace EvenCarrierUpgrade

/-- Four constant cross-distance equations make the corresponding two
difference vectors orthogonal. -/
private lemma inner_sub_sub_eq_zero_of_cross_unit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {a b c e : E}
    (hac : dist a c = 1) (hae : dist a e = 1)
    (hbc : dist b c = 1) (hbe : dist b e = 1) :
    inner ℝ (b - a) (e - c) = 0 := by
  have h_ac : inner ℝ (a - c) (a - c) = 1 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, hac]
    norm_num
  have h_ae : inner ℝ (a - e) (a - e) = 1 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, hae]
    norm_num
  have h_bc : inner ℝ (b - c) (b - c) = 1 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, hbc]
    norm_num
  have h_be : inner ℝ (b - e) (b - e) = 1 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, hbe]
    norm_num
  rw [real_inner_sub_sub_self] at h_ac h_ae h_bc h_be
  simp only [inner_sub_left, inner_sub_right] at ⊢
  linarith

/-- Three distinct points on one sphere give two independent affine
directions. -/
private lemma three_points_on_unit_sphere_independent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {a b c q : E} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (haq : dist a q = 1) (hbq : dist b q = 1) (hcq : dist c q = 1) :
    LinearIndependent ℝ ![b - a, c - a] := by
  have hu : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  rw [LinearIndependent.pair_iff' hu]
  intro t ht
  have h_a : inner ℝ (a - q) (a - q) = 1 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, haq]
    norm_num
  have h_b : inner ℝ (b - q) (b - q) = 1 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, hbq]
    norm_num
  have h_c : inner ℝ (c - q) (c - q) = 1 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, hcq]
    norm_num
  have hu_pos : 0 < inner ℝ (b - a) (b - a) := (real_inner_self_pos).2 hu
  have hb_split : b - q = (a - q) + (b - a) := by abel
  have hc_split : c - q = (a - q) + (c - a) := by abel
  rw [hb_split] at h_b
  rw [hc_split, ← ht] at h_c
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right] at h_b h_c
  rw [real_inner_comm (a - q) (b - a)] at h_b h_c
  have hpoly : (t * (t - 1)) * inner ℝ (b - a) (b - a) = 0 := by
    linear_combination h_c - h_a - t * h_b + t * h_a
  have ht_factor : t * (t - 1) = 0 :=
    (mul_eq_zero.mp hpoly).resolve_right (ne_of_gt hu_pos)
  have ht_cases : t = 0 ∨ t = 1 := by
    rcases mul_eq_zero.mp ht_factor with ht0 | ht1
    · exact Or.inl ht0
    · exact Or.inr (sub_eq_zero.mp ht1)
  rcases ht_cases with rfl | rfl
  · apply hac
    have hca : c = a := sub_eq_zero.mp (by simpa using ht.symm)
    exact hca.symm
  · apply hbc
    have huv : b - a = c - a := by simpa using ht
    calc
      b = (b - a) + a := (sub_add_cancel b a).symm
      _ = (c - a) + a := congrArg (fun z : E ↦ z + a) huv
      _ = c := sub_add_cancel c a

/-- The two affine directions selected from each three-point part. -/
private def partDirection {p : ℕ} (x : Fin p → Fin 3 → Point (2 * p))
    (v : Fin p × Fin 2) : Point (2 * p) :=
  x v.1 v.2.succ - x v.1 0

/-- In the critical ambient dimension, all selected part directions form a
basis: within each part independence comes from the common sphere, and
different parts are orthogonal. -/
private lemma partDirections_linearIndependent
    {p : ℕ} (hp : 2 ≤ p) {x : Fin p → Fin 3 → Point (2 * p)}
    (hinj : ∀ i, Function.Injective (x i))
    (hdist : ∀ {i j : Fin p}, i ≠ j → ∀ a b, dist (x i a) (x j b) = 1) :
    LinearIndependent ℝ (partDirection x) := by
  have hne (i : Fin p) {a b : Fin 3} (hab : a ≠ b) : x i a ≠ x i b :=
    fun h ↦ hab (hinj i h)
  have hblock (i : Fin p) :
      LinearIndependent ℝ (fun k : Fin 2 ↦ partDirection x (i, k)) := by
    obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card (α := Fin p) (by
      rw [Fintype.card_fin]
      omega) i
    have h := three_points_on_unit_sphere_independent
      (a := x i 0) (b := x i 1) (c := x i 2) (q := x j 0)
      (hne i (by decide)) (hne i (by decide)) (hne i (by decide))
      (hdist hji.symm 0 0) (hdist hji.symm 1 0) (hdist hji.symm 2 0)
    rw [show (fun k : Fin 2 ↦ partDirection x (i, k)) =
        ![x i 1 - x i 0, x i 2 - x i 0] by
      funext k
      fin_cases k <;> rfl]
    exact h
  have hortho {i j : Fin p} (hij : i ≠ j) (k l : Fin 2) :
      inner ℝ (partDirection x (i, k)) (partDirection x (j, l)) = 0 := by
    exact inner_sub_sub_eq_zero_of_cross_unit
      (hdist hij 0 0) (hdist hij 0 l.succ)
      (hdist hij k.succ 0) (hdist hij k.succ l.succ)
  rw [Fintype.linearIndependent_iff]
  intro g hg v
  let z : Fin p → Point (2 * p) :=
    fun i ↦ ∑ k : Fin 2, g (i, k) • partDirection x (i, k)
  have hsum : ∑ i : Fin p, z i = 0 := by
    change (∑ i : Fin p, ∑ k : Fin 2,
      g (i, k) • partDirection x (i, k)) = 0
    calc
      _ = ∑ v : Fin p × Fin 2, g v • partDirection x v :=
        (Fintype.sum_prod_type
          (fun v : Fin p × Fin 2 ↦ g v • partDirection x v)).symm
      _ = 0 := hg
  have hcross {i j : Fin p} (hij : i ≠ j) : inner ℝ (z i) (z j) = 0 := by
    simp only [z, sum_inner, inner_sum, real_inner_smul_left,
      real_inner_smul_right]
    exact Finset.sum_eq_zero fun k _ ↦ Finset.sum_eq_zero fun l _ ↦ by
      rw [hortho hij]
      ring
  have hz (i : Fin p) : z i = 0 := by
    have hi := congrArg (fun y : Point (2 * p) ↦ inner ℝ y (z i)) hsum
    simp only [sum_inner, inner_zero_left] at hi
    have hii : inner ℝ (z i) (z i) = 0 := by
      rw [← hi]
      symm
      exact Finset.sum_eq_single i
        (fun j _ hji ↦ hcross hji)
        (by intro hiu; exact (hiu (Finset.mem_univ i)).elim)
    exact inner_self_eq_zero.mp hii
  exact (Fintype.linearIndependent_iff.mp (hblock v.1)
    (fun k ↦ g (v.1, k)) (hz v.1)) v.2

/-- The affine plane spanned by the selected triple in one part. -/
private def triplePlane {p : ℕ} (x : Fin p → Fin 3 → Point (2 * p))
    (i : Fin p) : AffineSubspace ℝ (Point (2 * p)) :=
  affineSpan ℝ (Set.range (x i))

/-- Each selected triple spans a genuine two-dimensional affine plane. -/
private lemma triplePlane_finrank
    {p : ℕ} (hp : 2 ≤ p) {x : Fin p → Fin 3 → Point (2 * p)}
    (hinj : ∀ i, Function.Injective (x i))
    (hdist : ∀ {i j : Fin p}, i ≠ j → ∀ a b, dist (x i a) (x j b) = 1)
    (i : Fin p) : Module.finrank ℝ (triplePlane x i).direction = 2 := by
  let v : Fin 2 → (triplePlane x i).direction := fun k ↦
    ⟨partDirection x (i, k), by
      rw [triplePlane, direction_affineSpan]
      exact vsub_mem_vectorSpan ℝ
        ⟨k.succ, rfl⟩ ⟨0, rfl⟩⟩
  have hv : LinearIndependent ℝ v := by
    have hli := partDirections_linearIndependent hp hinj hdist
    have hblock : LinearIndependent ℝ (fun k : Fin 2 ↦ partDirection x (i, k)) :=
      hli.comp (fun k ↦ (i, k)) (fun _ _ h ↦ congrArg Prod.snd h)
    apply LinearIndependent.of_comp (Submodule.subtype (triplePlane x i).direction)
    have heq : (Submodule.subtype (triplePlane x i).direction) ∘ v =
        fun k : Fin 2 ↦ partDirection x (i, k) := by
      rfl
    rw [heq]
    exact hblock
  apply le_antisymm
  · rw [triplePlane, direction_affineSpan]
    exact finrank_vectorSpan_range_le ℝ (x i) (by norm_num)
  · simpa using hv.fintype_card_le_finrank

/-- Distinct selected triple planes have orthogonal directions. -/
private lemma triplePlane_isOrtho
    {p : ℕ} {x : Fin p → Fin 3 → Point (2 * p)}
    (hdist : ∀ {i j : Fin p}, i ≠ j → ∀ a b, dist (x i a) (x j b) = 1)
    {i j : Fin p} (hij : i ≠ j) :
    (triplePlane x i).direction ⟂ (triplePlane x j).direction := by
  apply affineSpan_direction_isOrtho_of_cross_dist_eq
    (A := Set.range (x i)) (B := Set.range (x j)) (radius := 1)
    ⟨x i 0, ⟨0, rfl⟩⟩ ⟨x j 0, ⟨0, rfl⟩⟩
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  exact hdist hij a b

/-- The three selected points in each part are affinely independent. -/
private lemma triple_affineIndependent
    {p : ℕ} (hp : 2 ≤ p) {x : Fin p → Fin 3 → Point (2 * p)}
    (hinj : ∀ i, Function.Injective (x i))
    (hdist : ∀ {i j : Fin p}, i ≠ j → ∀ a b, dist (x i a) (x j b) = 1)
    (i : Fin p) : AffineIndependent ℝ (x i) := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ (x i) 0]
  let e := finSuccAboveEquiv (0 : Fin 3)
  have hli := partDirections_linearIndependent hp hinj hdist
  have hblock : LinearIndependent ℝ (fun k : Fin 2 ↦ partDirection x (i, k)) :=
    hli.comp (fun k ↦ (i, k)) (fun _ _ h ↦ congrArg Prod.snd h)
  have heq : ((fun i' : {i' : Fin 3 // i' ≠ 0} ↦ x i i' -ᵥ x i 0) ∘ e) =
      fun k : Fin 2 ↦ partDirection x (i, k) := by
    funext k
    change x i ((finSuccAboveEquiv 0 k : {i' : Fin 3 // i' ≠ 0}) : Fin 3) - x i 0 =
      x i k.succ - x i 0
    rw [finSuccAboveEquiv_apply]
    rfl
  exact (linearIndependent_equiv' e heq).mp hblock

/-- In the critical dimension, a vector orthogonal to every triple plane
except the `i`th lies in the direction of the `i`th plane. -/
private lemma mem_triplePlane_direction_of_mem_orthogonal_others
    {p : ℕ} (hp : 2 ≤ p) {x : Fin p → Fin 3 → Point (2 * p)}
    (hinj : ∀ i, Function.Injective (x i))
    (hdist : ∀ {i j : Fin p}, i ≠ j → ∀ a b, dist (x i a) (x j b) = 1)
    (i : Fin p) {v : Point (2 * p)}
    (hv : ∀ k, k ≠ i → v ∈ (triplePlane x k).directionᗮ) :
    v ∈ (triplePlane x i).direction := by
  let U : Submodule ℝ (Point (2 * p)) :=
    ⨆ k : {k : Fin p // k ≠ i}, (triplePlane x k).direction
  have hUle : U ≤ (triplePlane x i).directionᗮ := by
    apply iSup_le
    intro k
    exact triplePlane_isOrtho hdist k.property
  have hWorth : Module.finrank ℝ (triplePlane x i).directionᗮ = 2 * p - 2 := by
    have hdim := (triplePlane x i).direction.finrank_add_finrank_orthogonal
    rw [triplePlane_finrank (by omega) hinj hdist,
      finrank_euclideanSpace, Fintype.card_fin] at hdim
    omega
  let b : ({k : Fin p // k ≠ i} × Fin 2) → U := fun w ↦
    ⟨partDirection x (w.1.1, w.2), by
      apply le_iSup (fun k : {k : Fin p // k ≠ i} ↦
        (triplePlane x k).direction) w.1
      rw [triplePlane, direction_affineSpan]
      exact vsub_mem_vectorSpan ℝ ⟨w.2.succ, rfl⟩ ⟨0, rfl⟩⟩
  have hb : LinearIndependent ℝ b := by
    have hli := partDirections_linearIndependent (by omega : 2 ≤ p) hinj hdist
    let e : ({k : Fin p // k ≠ i} × Fin 2) ↪ (Fin p × Fin 2) :=
      Function.Embedding.prodMap
        ⟨Subtype.val, Subtype.val_injective⟩ (Function.Embedding.refl (Fin 2))
    have hsub : LinearIndependent ℝ
        (fun w : {k : Fin p // k ≠ i} × Fin 2 ↦
          partDirection x (w.1.1, w.2)) :=
      by
        change LinearIndependent ℝ (partDirection x ∘ e)
        exact hli.comp e e.injective
    apply LinearIndependent.of_comp (Submodule.subtype U)
    have heq : (Submodule.subtype U) ∘ b =
        fun w : {k : Fin p // k ≠ i} × Fin 2 ↦
          partDirection x (w.1.1, w.2) := by
      rfl
    rw [heq]
    exact hsub
  have hcard_ne : Fintype.card {k : Fin p // k ≠ i} = p - 1 := by
    simpa using Fintype.card_subtype_compl (fun k : Fin p ↦ k = i)
  have hUlower : 2 * p - 2 ≤ Module.finrank ℝ U := by
    have := hb.fintype_card_le_finrank
    simp only [Fintype.card_prod, Fintype.card_fin, hcard_ne] at this
    omega
  have hUupper : Module.finrank ℝ U ≤ 2 * p - 2 := by
    rw [← hWorth]
    exact Submodule.finrank_mono hUle
  have hUeq : U = (triplePlane x i).directionᗮ :=
    Submodule.eq_of_le_of_finrank_eq hUle (by omega)
  have hvU : v ∈ Uᗮ := by
    rw [← Submodule.iInf_orthogonal]
    exact (Submodule.mem_iInf _).2 fun k ↦ hv k k.property
  rw [hUeq, Submodule.orthogonal_orthogonal] at hvU
  exact hvU

/-- A point which is equidistant from the vertices of one selected simplex
has that simplex's circumcenter as its orthogonal projection to the triple
plane. -/
private lemma projection_eq_triple_circumcenter
    {p : ℕ} {x : Fin p → Fin 3 → Point (2 * p)}
    (S : Fin p → Affine.Simplex ℝ (Point (2 * p)) 2)
    (hpoints : ∀ i, (S i).points = x i)
    {i : Fin p} {q : Point (2 * p)} {r : ℝ}
    (hqr : ∀ a, dist (x i a) q = r) :
    ↑((S i).orthogonalProjectionSpan q) = (S i).circumcenter := by
  apply (S i).orthogonalProjection_eq_circumcenter_of_dist_eq
  intro a
  simpa [hpoints i] using hqr a

/-- `p` mutually cross-unit triples in `Point (2p)`, for `p ≥ 3`, lie on
one genuine even Lenz carrier.  This is the full multipartite common-center
upgrade: pairwise affine-span geometry alone does not provide the common
translation. -/
private theorem exists_evenCircleCarrier_of_cross_unit_triples_aux
    {p : ℕ} (hp : 2 ≤ p) (x : Fin p → Fin 3 → Point (2 * p))
    (hinj : ∀ i, Function.Injective (x i))
    (hdist : ∀ {i j : Fin p}, i ≠ j → ∀ a b, dist (x i a) (x j b) = 1) :
    ∃ C : EvenCircleCarrier p,
      (∀ i, C.plane i = triplePlane x i) ∧ ∀ i a, x i a ∈ C.circle i := by
  have hAI (i : Fin p) : AffineIndependent ℝ (x i) :=
    triple_affineIndependent (by omega) hinj hdist i
  let S : Fin p → Affine.Simplex ℝ (Point (2 * p)) 2 :=
    fun i ↦ ⟨x i, hAI i⟩
  have hpoints (i : Fin p) : (S i).points = x i := rfl
  let c : Fin p → Point (2 * p) := fun i ↦ (S i).circumcenter
  let r : Fin p → ℝ := fun i ↦ (S i).circumradius
  have hc_mem (i : Fin p) : c i ∈ triplePlane x i := by
    simpa [c, triplePlane, hpoints i] using (S i).circumcenter_mem_affineSpan
  have hdist_c (i : Fin p) (a : Fin 3) : dist (x i a) (c i) = r i := by
    simpa [c, r, hpoints i] using (S i).dist_circumcenter_eq_circumradius a
  have hequidistant (i k : Fin p) : ∃ s : ℝ, ∀ a, dist (x k a) (c i) = s := by
    by_cases hik : i = k
    · subst k
      exact ⟨r i, hdist_c i⟩
    · obtain ⟨-, q, ri, rk, hqmem, -, -, hqi, hqk, -⟩ :=
        completeBipartiteGeometry
          (A := Set.range (x i)) (B := Set.range (x k))
          (Set.range_nonempty _) (Set.range_nonempty _)
          (by
            rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
            exact hdist hik a b)
      have hqeq : q = c i := by
        apply (S i).eq_circumcenter_of_dist_eq
        · simpa [triplePlane, hpoints i] using hqmem
        · intro a
          simpa [hpoints i] using hqi (x i a) ⟨a, rfl⟩
      exact ⟨rk, fun a ↦ by simpa [hqeq] using hqk (x k a) ⟨a, rfl⟩⟩
  have hcenter_eq (i j : Fin p) : c i = c j := by
    have hli := partDirections_linearIndependent (by omega : 2 ≤ p) hinj hdist
    have hspan : Submodule.span ℝ (Set.range (partDirection x)) = ⊤ :=
      hli.span_eq_top_of_card_eq_finrank' (by
        simp [finrank_euclideanSpace, Nat.mul_comm])
    have hgen (v : Fin p × Fin 2) :
        inner ℝ (c j - c i) (partDirection x v) = 0 := by
      obtain ⟨ri, hri⟩ := hequidistant i v.1
      obtain ⟨rj, hrj⟩ := hequidistant j v.1
      exact EuclideanGeometry.inner_vsub_vsub_of_dist_eq_of_dist_eq
        ((hri 0).trans (hri v.2.succ).symm)
        ((hrj 0).trans (hrj v.2.succ).symm)
    have horth : c j - c i ∈
        (Submodule.span ℝ (Set.range (partDirection x)))ᗮ := by
      rw [Submodule.mem_orthogonal']
      intro u hu
      refine Submodule.span_induction
        (p := fun u _ ↦ inner ℝ (c j - c i) u = 0) ?_ ?_ ?_ ?_ hu
      · rintro _ ⟨v, rfl⟩
        exact hgen v
      · exact inner_zero_right _
      · intro u v _ _ hu hv
        rw [inner_add_right, hu, hv, add_zero]
      · intro a u _ hu
        rw [real_inner_smul_right, hu, mul_zero]
    rw [hspan, Submodule.top_orthogonal_eq_bot] at horth
    exact (sub_eq_zero.mp horth).symm
  let i0 : Fin p := ⟨0, by omega⟩
  let c0 : Point (2 * p) := c i0
  have hc0_mem (i : Fin p) : c0 ∈ triplePlane x i := by
    rw [show c0 = c i by exact hcenter_eq i0 i]
    exact hc_mem i
  have hdist_c0 (i : Fin p) (a : Fin 3) : dist (x i a) c0 = r i := by
    rw [show c0 = c i by exact hcenter_eq i0 i]
    exact hdist_c i a
  have hr_add {i j : Fin p} (hij : i ≠ j) : r i ^ 2 + r j ^ 2 = 1 := by
    have hxi : x i 0 ∈ triplePlane x i := by
      exact mem_affineSpan ℝ ⟨0, rfl⟩
    have hxj : x j 0 ∈ triplePlane x j := by
      exact mem_affineSpan ℝ ⟨0, rfl⟩
    have hinner : inner ℝ (x i 0 -ᵥ c0) (x j 0 -ᵥ c0) = 0 := by
      have ho := triplePlane_isOrtho hdist hij
      rw [Submodule.isOrtho_iff_inner_eq] at ho
      exact ho _ (AffineSubspace.vsub_mem_direction hxi (hc0_mem i)) _
        (AffineSubspace.vsub_mem_direction hxj (hc0_mem j))
    have hnorm : ‖(x i 0 -ᵥ c0) - (x j 0 -ᵥ c0)‖ ^ 2 =
        ‖x i 0 -ᵥ c0‖ ^ 2 + ‖x j 0 -ᵥ c0‖ ^ 2 := by
      simpa [pow_two] using norm_sub_sq_eq_norm_sq_add_norm_sq_real hinner
    have hi : ‖x i 0 -ᵥ c0‖ = r i := by
      simpa [dist_eq_norm_vsub] using hdist_c0 i 0
    have hj : ‖x j 0 -ᵥ c0‖ = r j := by
      simpa [dist_eq_norm_vsub] using hdist_c0 j 0
    have hcross := hdist hij (0 : Fin 3) (0 : Fin 3)
    calc
      r i ^ 2 + r j ^ 2 =
          ‖x i 0 -ᵥ c0‖ ^ 2 + ‖x j 0 -ᵥ c0‖ ^ 2 := by rw [hi, hj]
      _ = ‖(x i 0 -ᵥ c0) - (x j 0 -ᵥ c0)‖ ^ 2 := hnorm.symm
      _ = dist (x i 0) (x j 0) ^ 2 := by
        rw [dist_eq_norm_vsub]
        congr 2
        simp [vsub_eq_sub]
      _ = 1 := by rw [hcross]; norm_num
  let C : EvenCircleCarrier p :=
    { center := c0
      plane := triplePlane x
      radius := r
      center_mem := hc0_mem
      plane_finrank := triplePlane_finrank (by omega) hinj hdist
      direction_isOrtho := triplePlane_isOrtho hdist
      radius_nonneg := fun i ↦ (S i).circumradius_nonneg
      radius_sq_add := hr_add }
  refine ⟨C, fun _ ↦ rfl, fun i a ↦ ?_⟩
  exact ⟨mem_affineSpan ℝ ⟨a, rfl⟩, hdist_c0 i a⟩

/-- Base form of the full multipartite common-center upgrade. -/
theorem exists_evenCircleCarrier_of_cross_unit_triples
    {p : ℕ} (hp : 2 ≤ p) (x : Fin p → Fin 3 → Point (2 * p))
    (hinj : ∀ i, Function.Injective (x i))
    (hdist : ∀ {i j : Fin p}, i ≠ j → ∀ a b, dist (x i a) (x j b) = 1) :
    ∃ C : EvenCircleCarrier p, ∀ i a, x i a ∈ C.circle i := by
  obtain ⟨C, -, hC⟩ :=
    exists_evenCircleCarrier_of_cross_unit_triples_aux hp x hinj hdist
  exact ⟨C, hC⟩

/-- Completion form of the common-center upgrade.  A further point at unit
distance from all three selected points in every part except `i` is forced
onto the `i`th carrier circle. -/
theorem exists_evenCircleCarrier_of_cross_unit_triples_with_completion
    {p : ℕ} (hp : 2 ≤ p) (x : Fin p → Fin 3 → Point (2 * p))
    (hinj : ∀ i, Function.Injective (x i))
    (hdist : ∀ {i j : Fin p}, i ≠ j → ∀ a b, dist (x i a) (x j b) = 1) :
    ∃ C : EvenCircleCarrier p,
      (∀ i a, x i a ∈ C.circle i) ∧
      ∀ (i : Fin p) (q : Point (2 * p)),
        (∀ k, k ≠ i → ∀ a, dist q (x k a) = 1) → q ∈ C.circle i := by
  obtain ⟨C, hplane, hbase⟩ :=
    exists_evenCircleCarrier_of_cross_unit_triples_aux hp x hinj hdist
  have hAI (i : Fin p) : AffineIndependent ℝ (x i) :=
    triple_affineIndependent (by omega) hinj hdist i
  let S : Fin p → Affine.Simplex ℝ (Point (2 * p)) 2 :=
    fun i ↦ ⟨x i, hAI i⟩
  have hpoints (i : Fin p) : (S i).points = x i := rfl
  have hcirc (i : Fin p) : (S i).circumcenter = C.center := by
    symm
    apply (S i).eq_circumcenter_of_dist_eq
    · change C.center ∈ triplePlane x i
      rw [← hplane i]
      exact C.center_mem i
    · intro a
      simpa [hpoints i] using (hbase i a).2
  refine ⟨C, hbase, ?_⟩
  intro i q hq
  have hvorth (k : Fin p) (hki : k ≠ i) :
      q -ᵥ C.center ∈ (triplePlane x k).directionᗮ := by
    let : Nonempty (triplePlane x k) :=
      ⟨⟨x k 0, mem_affineSpan ℝ ⟨0, rfl⟩⟩⟩
    have hproj : ↑((S k).orthogonalProjectionSpan q) = C.center := by
      calc
        ↑((S k).orthogonalProjectionSpan q) = (S k).circumcenter := by
          apply (S k).orthogonalProjection_eq_circumcenter_of_dist_eq
          intro a
          simpa [hpoints k, dist_comm] using hq k hki a
        _ = C.center := hcirc k
    rw [← hproj]
    change q -ᵥ ↑((S k).orthogonalProjectionSpan q) ∈
      (affineSpan ℝ (Set.range (S k).points)).directionᗮ
    exact EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal
      (affineSpan ℝ (Set.range (S k).points)) q
  have hvdir : q -ᵥ C.center ∈ (triplePlane x i).direction :=
    mem_triplePlane_direction_of_mem_orthogonal_others hp hinj hdist i hvorth
  have hqplane : q ∈ C.plane i := by
    rw [hplane i]
    have hm : (q -ᵥ C.center) +ᵥ C.center ∈ triplePlane x i :=
      AffineSubspace.vadd_mem_of_mem_direction hvdir
        (by simpa [hplane i] using C.center_mem i)
    simpa only [vsub_vadd] using hm
  obtain ⟨k, hki⟩ := Fintype.exists_ne_of_one_lt_card (α := Fin p) (by
    rw [Fintype.card_fin]
    omega) i
  have hxkplane : x k 0 ∈ C.plane k := (hbase k 0).1
  have hxkdir : x k 0 -ᵥ C.center ∈ (C.plane k).direction :=
    AffineSubspace.vsub_mem_direction hxkplane (C.center_mem k)
  have hinner : inner ℝ (q -ᵥ C.center) (x k 0 -ᵥ C.center) = 0 := by
    have ho := C.direction_isOrtho hki.symm
    rw [Submodule.isOrtho_iff_inner_eq] at ho
    exact ho _ (by simpa [hplane i] using hvdir) _ hxkdir
  have hnorm : ‖(q -ᵥ C.center) - (x k 0 -ᵥ C.center)‖ ^ 2 =
      ‖q -ᵥ C.center‖ ^ 2 + ‖x k 0 -ᵥ C.center‖ ^ 2 := by
    simpa [pow_two] using norm_sub_sq_eq_norm_sq_add_norm_sq_real hinner
  have hxknorm : ‖x k 0 -ᵥ C.center‖ = C.radius k := by
    simpa [dist_eq_norm_vsub] using (hbase k 0).2
  have hqk : dist q (x k 0) = 1 := hq k hki 0
  have hsquares : ‖q -ᵥ C.center‖ ^ 2 + C.radius k ^ 2 = 1 := by
    calc
      ‖q -ᵥ C.center‖ ^ 2 + C.radius k ^ 2 =
          ‖q -ᵥ C.center‖ ^ 2 + ‖x k 0 -ᵥ C.center‖ ^ 2 := by rw [hxknorm]
      _ = ‖(q -ᵥ C.center) - (x k 0 -ᵥ C.center)‖ ^ 2 := hnorm.symm
      _ = dist q (x k 0) ^ 2 := by
        rw [dist_eq_norm_vsub]
        congr 2
        simp [vsub_eq_sub]
      _ = 1 := by rw [hqk]; norm_num
  have hradd := C.radius_sq_add hki.symm
  have hnormeq : ‖q -ᵥ C.center‖ = C.radius i := by
    nlinarith [norm_nonneg (q -ᵥ C.center), C.radius_nonneg i]
  exact ⟨hqplane, by simpa [dist_eq_norm_vsub] using hnormeq⟩

/-- Three common affinely independent points determine the carrier circle
containing them.  This is the overlap principle used to compare the base
carrier with carriers obtained from seeded selections. -/
theorem circle_eq_of_common_affineIndependent_triple
    {p : ℕ} (C D : EvenCircleCarrier p) (i : Fin p)
    (x : Fin 3 → Point (2 * p)) (hAI : AffineIndependent ℝ x)
    (hC : ∀ a, x a ∈ C.circle i) (hD : ∀ a, x a ∈ D.circle i) :
    C.circle i = D.circle i := by
  let S : Affine.Simplex ℝ (Point (2 * p)) 2 := ⟨x, hAI⟩
  have hCplane : affineSpan ℝ (Set.range x) = C.plane i := by
    apply hAI.affineSpan_eq_of_le_of_card_eq_finrank_add_one
    · rw [affineSpan_le]
      rintro _ ⟨a, rfl⟩
      exact (hC a).1
    · rw [C.plane_finrank]
      norm_num
  have hDplane : affineSpan ℝ (Set.range x) = D.plane i := by
    apply hAI.affineSpan_eq_of_le_of_card_eq_finrank_add_one
    · rw [affineSpan_le]
      rintro _ ⟨a, rfl⟩
      exact (hD a).1
    · rw [D.plane_finrank]
      norm_num
  have hCcenter : C.center = S.circumcenter := by
    apply S.eq_circumcenter_of_dist_eq
    · simpa [S, hCplane] using C.center_mem i
    · intro a
      simpa [S] using (hC a).2
  have hDcenter : D.center = S.circumcenter := by
    apply S.eq_circumcenter_of_dist_eq
    · simpa [S, hDplane] using D.center_mem i
    · intro a
      simpa [S] using (hD a).2
  have hCradius : C.radius i = S.circumradius := by
    apply S.eq_circumradius_of_dist_eq
    · simpa [S, hCplane] using C.center_mem i
    · intro a
      simpa [S] using (hC a).2
  have hDradius : D.radius i = S.circumradius := by
    apply S.eq_circumradius_of_dist_eq
    · simpa [S, hDplane] using D.center_mem i
    · intro a
      simpa [S] using (hD a).2
  ext q
  simp only [EvenCircleCarrier.mem_circle]
  rw [← hCplane, ← hDplane, hCcenter, hDcenter, hCradius, hDradius]

/-- A carrier is already complete with respect to three witnesses on every
other circle.  This is Lemma 8(c) of Swanepoel in the critical even
dimension, expressed intrinsically for an assembled carrier. -/
theorem EvenCircleCarrier.mem_circle_of_unit_to_other_triples
    {p : ℕ} (C : EvenCircleCarrier p) (hp : 2 ≤ p)
    (x : Fin p → Fin 3 → Point (2 * p))
    (hinj : ∀ i, Function.Injective (x i))
    (hxC : ∀ i a, x i a ∈ C.circle i)
    (i : Fin p) (q : Point (2 * p))
    (hq : ∀ k, k ≠ i → ∀ a, dist q (x k a) = 1) :
    q ∈ C.circle i := by
  have hdist : ∀ {k l : Fin p}, k ≠ l →
      ∀ a b, dist (x k a) (x l b) = 1 := by
    intro k l hkl a b
    exact C.dist_eq_one_of_mem_circle_of_ne hkl (hxC k a) (hxC l b)
  obtain ⟨D, hxD, hcomplete⟩ :=
    exists_evenCircleCarrier_of_cross_unit_triples_with_completion hp x hinj hdist
  have hAI : AffineIndependent ℝ (x i) :=
    triple_affineIndependent (by omega) hinj hdist i
  have hcircle : C.circle i = D.circle i :=
    circle_eq_of_common_affineIndependent_triple C D i (x i) hAI (hxC i) (hxD i)
  rw [hcircle]
  exact hcomplete i q hq

end EvenCarrierUpgrade

/-! ## Finite selection from a stable partition -/

namespace EvenStableSelection

open Finset

variable {V : Type*} [DecidableEq V]

private lemma exists_superset_subset_card_eq (K S : Finset V) (t : ℕ)
    (hKS : K ⊆ S) (hKt : K.card ≤ t) (htS : t ≤ S.card) :
    ∃ T : Finset V, K ⊆ T ∧ T ⊆ S ∧ T.card = t := by
  have hdiff : (S \ K).card = S.card - K.card :=
    Finset.card_sdiff_of_subset hKS
  have hneed : t - K.card ≤ (S \ K).card := by
    rw [hdiff]
    omega
  obtain ⟨R, hR, hRcard⟩ := Finset.exists_subset_card_eq hneed
  have hdisj : Disjoint K R := by
    rw [Finset.disjoint_left]
    intro x hxK hxR
    exact (Finset.mem_sdiff.mp (hR hxR)).2 hxK
  refine ⟨K ∪ R, Finset.subset_union_left, Finset.union_subset hKS
    (hR.trans Finset.sdiff_subset), ?_⟩
  rw [Finset.card_union_of_disjoint hdisj, hRcard]
  omega

/-- A real-valued union bound for vertices failing adjacency to a finite
seed. -/
private lemma card_bad_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (S Q : Finset V) (b : ℝ)
    (hbad : ∀ x ∈ Q, ((S.filter fun y ↦ ¬ G.Adj x y).card : ℝ) ≤ b) :
    ((Q.biUnion fun x ↦ S.filter fun y ↦ ¬ G.Adj x y).card : ℝ) ≤ Q.card * b := by
  calc
    ((Q.biUnion fun x ↦ S.filter fun y ↦ ¬ G.Adj x y).card : ℝ)
        ≤ ∑ x ∈ Q, ((S.filter fun y ↦ ¬ G.Adj x y).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ Q, b := Finset.sum_le_sum fun x hx ↦ hbad x hx
    _ = Q.card * b := by simp

/-- If at most `b` candidates are forbidden by each old vertex, the union
bound leaves `t` new mutually compatible candidates. -/
private theorem exists_card_subset_adj (G : SimpleGraph V) [DecidableRel G.Adj]
    (S Q : Finset V) (q t : ℕ) (b : ℝ)
    (hb : 0 ≤ b)
    (hQ : Q.card ≤ q)
    (hbad : ∀ x ∈ Q, ((S.filter fun y ↦ ¬ G.Adj x y).card : ℝ) ≤ b)
    (hsize : (q : ℝ) * b + t ≤ S.card) :
    ∃ T : Finset V, T ⊆ S ∧ T.card = t ∧
      ∀ y ∈ T, ∀ x ∈ Q, G.Adj x y := by
  let Bad : Finset V := Q.biUnion fun x ↦ S.filter fun y ↦ ¬ G.Adj x y
  have hBadS : Bad ⊆ S := by
    intro y hy
    simp only [Bad, Finset.mem_biUnion, Finset.mem_filter] at hy
    obtain ⟨x, -, hyS, -⟩ := hy
    exact hyS
  have hBad : (Bad.card : ℝ) ≤ (q : ℝ) * b := by
    calc
      (Bad.card : ℝ) ≤ Q.card * b := card_bad_le G S Q b hbad
      _ ≤ q * b := mul_le_mul_of_nonneg_right (by exact_mod_cast hQ) hb
  have hremain : t ≤ (S \ Bad).card := by
    rw [Finset.card_sdiff_of_subset hBadS]
    have hcast : (Bad.card : ℝ) + t ≤ S.card := by linarith
    have hnat : Bad.card + t ≤ S.card := by exact_mod_cast hcast
    omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hremain
  refine ⟨T, hTsub.trans Finset.sdiff_subset, hTcard, ?_⟩
  intro y hy x hx
  have hyDiff : y ∈ S \ Bad := hTsub hy
  have hyNotBad : y ∉ Bad := (Finset.mem_sdiff.mp hyDiff).2
  by_contra hxy
  apply hyNotBad
  simp only [Bad, Finset.mem_biUnion, Finset.mem_filter]
  exact ⟨x, hx, (Finset.mem_sdiff.mp hyDiff).1, hxy⟩

/-- Greedy multipartite selection with a prescribed base set. -/
private theorem exists_complete_on_finset_with_base
    {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : ι → Finset V) (I : Finset ι) (Q₀ : Finset V)
    (q t : ℕ) (b : ℝ)
    (hb : 0 ≤ b)
    (hIq : Q₀.card + I.card * t ≤ q)
    (hsize : ∀ i ∈ I, (q : ℝ) * b + t ≤ (S i).card)
    (hbad : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ x ∈ S i,
      (((S j).filter fun y ↦ ¬ G.Adj x y).card : ℝ) ≤ b)
    (hbadBase : ∀ x ∈ Q₀, ∀ j ∈ I,
      (((S j).filter fun y ↦ ¬ G.Adj x y).card : ℝ) ≤ b) :
    ∃ T : ι → Finset V,
      (∀ i ∈ I, T i ⊆ S i ∧ (T i).card = t) ∧
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j →
        ∀ x ∈ T i, ∀ y ∈ T j, G.Adj x y) ∧
      ∀ x ∈ Q₀, ∀ i ∈ I, ∀ y ∈ T i, G.Adj x y := by
  induction I using Finset.induction_on with
  | empty => exact ⟨fun _ ↦ ∅, by simp, by simp, by simp⟩
  | @insert a I ha ih =>
      have hIqI : Q₀.card + I.card * t ≤ q := by
        apply le_trans (Nat.add_le_add_left
          (Nat.mul_le_mul_right t (Nat.le_add_right I.card 1)) Q₀.card)
        simpa [Finset.card_insert_of_notMem ha] using hIq
      obtain ⟨T, hT, hcross, hbase⟩ := ih hIqI
        (fun i hi ↦ hsize i (Finset.mem_insert_of_mem hi))
        (fun i hi j hj hij x hx ↦
          hbad i (Finset.mem_insert_of_mem hi) j
            (Finset.mem_insert_of_mem hj) hij x hx)
        (fun x hx j hj ↦ hbadBase x hx j (Finset.mem_insert_of_mem hj))
      let Q : Finset V := Q₀ ∪ I.biUnion T
      have hQcard : Q.card ≤ q := by
        calc
          Q.card ≤ Q₀.card + (I.biUnion T).card := by
            simpa [Q] using Finset.card_union_le Q₀ (I.biUnion T)
          _ ≤ Q₀.card + ∑ i ∈ I, (T i).card :=
            Nat.add_le_add_left Finset.card_biUnion_le Q₀.card
          _ = Q₀.card + ∑ _i ∈ I, t := by
            congr 1
            exact Finset.sum_congr rfl fun i hi ↦ (hT i hi).2
          _ = Q₀.card + I.card * t := by simp
          _ ≤ q := hIqI
      have hbadQ : ∀ x ∈ Q,
          (((S a).filter fun y ↦ ¬ G.Adj x y).card : ℝ) ≤ b := by
        intro x hx
        simp only [Q, Finset.mem_union, Finset.mem_biUnion] at hx
        rcases hx with hx₀ | ⟨i, hi, hxi⟩
        · exact hbadBase x hx₀ a (Finset.mem_insert_self a I)
        · exact hbad i (Finset.mem_insert_of_mem hi) a
            (Finset.mem_insert_self a I)
            (fun hia ↦ ha (hia ▸ hi)) x ((hT i hi).1 hxi)
      obtain ⟨Ta, hTaS, hTaCard, hTaAdj⟩ :=
        exists_card_subset_adj G (S a) Q q t b hb hQcard hbadQ
          (hsize a (Finset.mem_insert_self a I))
      let T' : ι → Finset V := Function.update T a Ta
      refine ⟨T', ?_, ?_, ?_⟩
      · intro i hi
        by_cases hia : i = a
        · subst i
          simpa [T'] using And.intro hTaS hTaCard
        · have hiI : i ∈ I := (Finset.mem_insert.mp hi).resolve_left hia
          simpa [T', hia] using hT i hiI
      · intro i hi j hj hij x hxi y hyj
        by_cases hia : i = a
        · subst i
          have hja : j ≠ a := fun h ↦ hij h.symm
          have hjI : j ∈ I := (Finset.mem_insert.mp hj).resolve_left hja
          apply (G.adj_comm y x).mp
          apply hTaAdj x (by simpa [T'] using hxi) y
          simp only [Q, Finset.mem_union, Finset.mem_biUnion]
          exact Or.inr ⟨j, hjI, by simpa [T', hja] using hyj⟩
        · have hiI : i ∈ I := (Finset.mem_insert.mp hi).resolve_left hia
          by_cases hja : j = a
          · subst j
            apply hTaAdj y (by simpa [T'] using hyj) x
            simp only [Q, Finset.mem_union, Finset.mem_biUnion]
            exact Or.inr ⟨i, hiI, by simpa [T', hia] using hxi⟩
          · have hjI : j ∈ I := (Finset.mem_insert.mp hj).resolve_left hja
            apply hcross i hiI j hjI hij x
            · simpa [T', hia] using hxi
            · simpa [T', hja] using hyj
      · intro x hx i hi y hy
        by_cases hia : i = a
        · subst i
          apply hTaAdj y (by simpa [T'] using hy) x
          simp only [Q, Finset.mem_union]
          exact Or.inl hx
        · have hiI : i ∈ I := (Finset.mem_insert.mp hi).resolve_left hia
          apply hbase x hx i hiI y
          simpa [T', hia] using hy

/-- Select `t` mutually cross-adjacent vertices from every fiber, while
requiring a seed of at most `t` vertices in one distinguished fiber. -/
theorem exists_complete_parts_containing {p : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Fin p → Finset V) (i₀ : Fin p) (K : Finset V) (t : ℕ) (b : ℝ)
    (hb : 0 ≤ b)
    (hKS : K ⊆ S i₀) (hK : K.card ≤ t)
    (hsize : ∀ i, ((p * t : ℕ) : ℝ) * b + t ≤ (S i).card)
    (hbad : ∀ i j, i ≠ j → ∀ x ∈ S i,
      (((S j).filter fun y ↦ ¬ G.Adj x y).card : ℝ) ≤ b) :
    ∃ T : Fin p → Finset V,
      (∀ i, T i ⊆ S i ∧ (T i).card = t) ∧
      K ⊆ T i₀ ∧
      ∀ i j, i ≠ j → ∀ x ∈ T i, ∀ y ∈ T j, G.Adj x y := by
  have ht : t ≤ (S i₀).card := by
    have := hsize i₀
    have hterm : 0 ≤ ((p * t : ℕ) : ℝ) * b := mul_nonneg (by positivity) hb
    have hcast : (t : ℝ) ≤ (S i₀).card := by linarith
    exact_mod_cast hcast
  obtain ⟨T₀, hKT₀, hT₀S, hT₀card⟩ :=
    exists_superset_subset_card_eq K (S i₀) t hKS hK ht
  let I : Finset (Fin p) := Finset.univ.erase i₀
  have hp1 : 1 ≤ p := Nat.succ_le_iff.mpr
    (lt_of_le_of_lt (Nat.zero_le i₀.val) i₀.isLt)
  have hcardI : I.card + 1 = p := by
    simp only [I, Finset.card_erase_of_mem (Finset.mem_univ i₀),
      Finset.card_univ, Fintype.card_fin]
    omega
  have htotal : T₀.card + I.card * t ≤ p * t := by
    rw [hT₀card]
    calc
      t + I.card * t = (I.card + 1) * t := by
        simp [Nat.add_mul, Nat.add_comm]
      _ ≤ p * t := Nat.mul_le_mul_right t hcardI.le
  obtain ⟨Trest, hTrest, hcross, hbase⟩ :=
    exists_complete_on_finset_with_base G S I T₀ (p * t) t b hb htotal
      (fun i _ ↦ by simpa [Nat.cast_mul, Nat.cast_ofNat] using hsize i)
      (fun i hi j hj hij x hx ↦ hbad i j hij x hx)
      (fun x hx j hj ↦ by
        have hji : j ≠ i₀ := (Finset.mem_erase.mp hj).1
        exact hbad i₀ j hji.symm x (hT₀S hx))
  let T : Fin p → Finset V := Function.update Trest i₀ T₀
  refine ⟨T, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i = i₀
    · subst i
      simpa [T] using And.intro hT₀S hT₀card
    · have hiI : i ∈ I := Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩
      simpa [T, hi] using hTrest i hiI
  · simpa [T] using hKT₀
  · intro i j hij x hxi y hyj
    by_cases hi : i = i₀
    · subst i
      have hj : j ≠ i₀ := fun h ↦ hij h.symm
      have hjI : j ∈ I := Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩
      apply hbase x (by simpa [T] using hxi) j hjI y
      simpa [T, hj] using hyj
    · have hiI : i ∈ I := Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩
      by_cases hj : j = i₀
      · subst j
        apply (G.adj_comm y x).mp
        apply hbase y (by simpa [T] using hyj) i hiI x
        simpa [T, hi] using hxi
      · have hjI : j ∈ I := Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩
        apply hcross i hiI j hjI hij x
        · simpa [T, hi] using hxi
        · simpa [T, hj] using hyj

/-- Three-point specialization used to initialize the geometric carrier. -/
theorem exists_complete_triples_containing {p : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Fin p → Finset V) (i₀ : Fin p) (K : Finset V) (b : ℝ)
    (hb : 0 ≤ b)
    (hKS : K ⊆ S i₀) (hK : K.card ≤ 3)
    (hsize : ∀ i, (3 * p : ℝ) * b + 3 ≤ (S i).card)
    (hbad : ∀ i j, i ≠ j → ∀ x ∈ S i,
      (((S j).filter fun y ↦ ¬ G.Adj x y).card : ℝ) ≤ b) :
    ∃ T : Fin p → Finset V,
      (∀ i, T i ⊆ S i ∧ (T i).card = 3) ∧
      K ⊆ T i₀ ∧
      ∀ i j, i ≠ j → ∀ x ∈ T i, ∀ y ∈ T j, G.Adj x y := by
  apply exists_complete_parts_containing G S i₀ K 3 b hb hKS hK
  · intro i
    simpa [Nat.cast_mul, Nat.cast_ofNat, mul_comm] using hsize i
  · exact hbad

end EvenStableSelection

/-! ## Stable cores lie on one common even carrier -/

namespace Stability.StablePartition

/-- A sufficiently separated stable partition of a diameter graph has all
of its retained fibers on one even Lenz carrier.  The size hypothesis is the
finite union-bound inequality used twice: first for base triples, then for a
four-point seeded selection containing a prescribed retained vertex. -/
theorem exists_evenCircleCarrier_core
    {p : ℕ} (hp : 2 ≤ p) {A : Finset (Point (2 * p))} {epsilon : ℝ}
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (hepsilon : 0 ≤ epsilon)
    (hsize : ∀ i,
      (((p * 4 : ℕ) : ℝ) * (epsilon * A.card) + 4 ≤
        (Stability.retainedFiber P.color P.exceptional i).card)) :
    ∃ C : EvenCircleCarrier p,
      ∀ (i : Fin p) (v : {x // x ∈ A}),
        v ∈ Stability.retainedFiber P.color P.exceptional i →
          (v : Point (2 * p)) ∈ C.circle i := by
  classical
  let G := diameterGraph A
  let S : Fin p → Finset {x // x ∈ A} :=
    fun i ↦ Stability.retainedFiber P.color P.exceptional i
  let b : ℝ := epsilon * A.card
  have hb : 0 ≤ b := mul_nonneg hepsilon (by positivity)
  have hbad : ∀ i j, i ≠ j → ∀ v ∈ S i,
      (((S j).filter fun w ↦ ¬ G.Adj v w).card : ℝ) ≤ b := by
    intro i j hij v hv
    have hsub : (S j).filter (fun w ↦ ¬ G.Adj v w) ⊆
        Stability.retainedCrossNonneighbors G P.color P.exceptional v := by
      intro w hw
      have hw' := Finset.mem_filter.mp hw
      have hvi := (Stability.mem_retainedFiber P.color P.exceptional i v).mp hv
      have hwj := (Stability.mem_retainedFiber P.color P.exceptional j w).mp hw'.1
      rw [Stability.mem_retainedCrossNonneighbors]
      exact ⟨hwj.2, by simpa [hvi.1, hwj.1] using hij, hw'.2⟩
    have hcard : ((S j).filter (fun w ↦ ¬ G.Adj v w)).card ≤
        (Stability.retainedCrossNonneighbors G P.color P.exceptional v).card :=
      Finset.card_le_card hsub
    calc
      (((S j).filter fun w ↦ ¬ G.Adj v w).card : ℝ)
          ≤ (Stability.retainedCrossNonneighbors G P.color P.exceptional v).card := by
            exact_mod_cast hcard
      _ ≤ b := by simpa [G, b] using (P.crossNonneighbors_small i v hv).le
  have hsize3 : ∀ i, (3 * p : ℝ) * b + 3 ≤ (S i).card := by
    intro i
    have hs := hsize i
    have hpR : (0 : ℝ) ≤ p := by positivity
    dsimp [S, b] at hs ⊢
    norm_num [Nat.cast_mul, Nat.cast_ofNat] at hs ⊢
    nlinarith
  let i0 : Fin p := ⟨0, by omega⟩
  obtain ⟨T, hT, -, hcross⟩ :=
    EvenStableSelection.exists_complete_triples_containing
      G S i0 ∅ b hb (by simp) (by simp) hsize3 hbad
  let e (i : Fin p) : T i ≃ Fin 3 :=
    (T i).equivFinOfCardEq (hT i).2
  let u : Fin p → Fin 3 → {x // x ∈ A} :=
    fun i a ↦ ((e i).symm a : {x // x ∈ A})
  have hu_mem (i : Fin p) (a : Fin 3) : u i a ∈ T i := by
    exact ((e i).symm a).property
  have hu_inj (i : Fin p) : Function.Injective (u i) := by
    intro a a' haa'
    apply (e i).symm.injective
    exact Subtype.ext haa'
  let x : Fin p → Fin 3 → Point (2 * p) :=
    fun i a ↦ (u i a : Point (2 * p))
  have hxinj (i : Fin p) : Function.Injective (x i) :=
    Subtype.val_injective.comp (hu_inj i)
  have hxdist : ∀ {i j : Fin p}, i ≠ j →
      ∀ a c, dist (x i a) (x j c) = 1 := by
    intro i j hij a c
    exact (diameterGraph_adj A (u i a) (u j c)).mp
      (hcross i j hij (u i a) (hu_mem i a) (u j c) (hu_mem j c))
  obtain ⟨C, hbase, -⟩ :=
    EvenCarrierUpgrade.exists_evenCircleCarrier_of_cross_unit_triples_with_completion
      hp x hxinj hxdist
  refine ⟨C, ?_⟩
  intro i v hv
  let K : Finset {x // x ∈ A} := insert v (T i)
  have hKS : K ⊆ S i := by
    intro w hw
    change w ∈ insert v (T i) at hw
    rw [Finset.mem_insert] at hw
    rcases hw with rfl | hw
    · exact hv
    · exact (hT i).1 hw
  have hKcard : K.card ≤ 4 := by
    calc
      K.card ≤ (T i).card + 1 := by
        simpa [K, Nat.add_comm] using Finset.card_insert_le v (T i)
      _ = 4 := by rw [(hT i).2]
  obtain ⟨T', hT', hKT', hcross'⟩ :=
    EvenStableSelection.exists_complete_parts_containing
      G S i K 4 b hb hKS hKcard (by simpa [S, b] using hsize) hbad
  let e4 (k : Fin p) : T' k ≃ Fin 4 :=
    (T' k).equivFinOfCardEq (hT' k).2
  let u4 : Fin p → Fin 3 → {x // x ∈ A} :=
    fun k a ↦ ((e4 k).symm a.castSucc : {x // x ∈ A})
  have hu4_mem (k : Fin p) (a : Fin 3) : u4 k a ∈ T' k :=
    ((e4 k).symm a.castSucc).property
  have hu4_inj (k : Fin p) : Function.Injective (u4 k) := by
    intro a a' haa'
    have hcast : a.castSucc = a'.castSucc := by
      apply (e4 k).symm.injective
      exact Subtype.ext haa'
    exact Fin.castSucc_injective 3 hcast
  let u' : Fin p → Fin 3 → {x // x ∈ A} := fun k a ↦
    if h : k = i then u i a else u4 k a
  have hu'_mem (k : Fin p) (a : Fin 3) : u' k a ∈ T' k := by
    by_cases hki : k = i
    · subst k
      have huK : u i a ∈ K := by
        change u i a ∈ insert v (T i)
        simp only [Finset.mem_insert]
        exact Or.inr (hu_mem i a)
      simpa [u'] using hKT' huK
    · simpa [u', hki] using hu4_mem k a
  have hu'_inj (k : Fin p) : Function.Injective (u' k) := by
    by_cases hki : k = i
    · subst k
      simpa [u'] using hu_inj i
    · simpa [u', hki] using hu4_inj k
  let x' : Fin p → Fin 3 → Point (2 * p) :=
    fun k a ↦ (u' k a : Point (2 * p))
  have hx'inj (k : Fin p) : Function.Injective (x' k) :=
    Subtype.val_injective.comp (hu'_inj k)
  have hx'dist : ∀ {k l : Fin p}, k ≠ l →
      ∀ a c, dist (x' k a) (x' l c) = 1 := by
    intro k l hkl a c
    exact (diameterGraph_adj A (u' k a) (u' l c)).mp
      (hcross' k l hkl (u' k a) (hu'_mem k a) (u' l c) (hu'_mem l c))
  obtain ⟨C', hbase', hcomplete'⟩ :=
    EvenCarrierUpgrade.exists_evenCircleCarrier_of_cross_unit_triples_with_completion
      hp x' hx'inj hx'dist
  have hvT' : v ∈ T' i := hKT' (by simp [K])
  have hvC' : (v : Point (2 * p)) ∈ C'.circle i := by
    apply hcomplete' i (v : Point (2 * p))
    intro k hki a
    exact (diameterGraph_adj A v (u' k a)).mp
      (hcross' i k hki.symm v hvT' (u' k a) (hu'_mem k a))
  have hxAI : AffineIndependent ℝ (x i) :=
    EvenCarrierUpgrade.triple_affineIndependent (by omega) hxinj hxdist i
  have hcircle : C.circle i = C'.circle i := by
    apply EvenCarrierUpgrade.circle_eq_of_common_affineIndependent_triple
      C C' i (x i) hxAI
    · exact hbase i
    · intro a
      have hxi : x' i a = x i a := by simp [x', u', x]
      simpa [hxi] using hbase' i a
  rw [hcircle]
  exact hvC'

/-- A vertex outside the carrier has at most two diameter neighbours in two
different retained fibers.  Otherwise three neighbours can be chosen in
all but at most one fiber, and carrier completion puts the vertex on the
remaining circle. -/
theorem exists_two_low_fibers_of_not_mem_carrier
    {p : ℕ} (hp : 2 ≤ p) {A : Finset (Point (2 * p))} {epsilon : ℝ}
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (C : EvenCircleCarrier p)
    (hcore : ∀ (i : Fin p) (w : {x // x ∈ A}),
      w ∈ Stability.retainedFiber P.color P.exceptional i →
        (w : Point (2 * p)) ∈ C.circle i)
    (hthree : ∀ i, 3 ≤ (Stability.retainedFiber
      P.color P.exceptional i).card)
    (v : {x // x ∈ A})
    (hv : ¬ ∃ i, (v : Point (2 * p)) ∈ C.circle i) :
    ∃ i j : Fin p, i ≠ j ∧
      ((Stability.retainedFiber P.color P.exceptional i).filter
        fun w ↦ (diameterGraph A).Adj v w).card ≤ 2 ∧
      ((Stability.retainedFiber P.color P.exceptional j).filter
        fun w ↦ (diameterGraph A).Adj v w).card ≤ 2 := by
  classical
  let G := diameterGraph A
  let S : Fin p → Finset {x // x ∈ A} :=
    fun i ↦ Stability.retainedFiber P.color P.exceptional i
  let N : Fin p → Finset {x // x ∈ A} :=
    fun i ↦ (S i).filter (G.Adj v)
  by_contra hpair
  have hnotpair : ∀ i j : Fin p, i ≠ j → ¬ ((N i).card ≤ 2 ∧ (N j).card ≤ 2) := by
    intro i j hij hlow
    apply hpair
    exact ⟨i, j, hij, by simpa [N, S, G] using hlow.1,
      by simpa [N, S, G] using hlow.2⟩
  by_cases hlow : ∃ i, (N i).card ≤ 2
  · let i₀ : Fin p := hlow.choose
    have hi₀ : (N i₀).card ≤ 2 := hlow.choose_spec
    have hlarge (k : Fin p) (hki : k ≠ i₀) : 3 ≤ (N k).card := by
      by_contra hk
      have hk' : (N k).card ≤ 2 := by omega
      exact hnotpair k i₀ hki ⟨hk', hi₀⟩
    have hchoose : ∀ k : Fin p, ∃ T : Finset {x // x ∈ A},
        T ⊆ S k ∧ T.card = 3 ∧
          (k ≠ i₀ → ∀ w ∈ T, G.Adj v w) := by
      intro k
      by_cases hki : k = i₀
      · obtain ⟨T, hTS, hTcard⟩ :=
          Finset.exists_subset_card_eq (hthree k)
        exact ⟨T, by simpa [S] using hTS, hTcard, by simp [hki]⟩
      · obtain ⟨T, hTN, hTcard⟩ :=
          Finset.exists_subset_card_eq (hlarge k hki)
        refine ⟨T, ?_, hTcard, ?_⟩
        · exact hTN.trans (by intro w hw; exact (Finset.mem_filter.mp hw).1)
        · intro _ w hw
          exact (Finset.mem_filter.mp (hTN hw)).2
    choose T hTS hTcard hTv using hchoose
    let e (k : Fin p) : T k ≃ Fin 3 :=
      (T k).equivFinOfCardEq (hTcard k)
    let u : Fin p → Fin 3 → {x // x ∈ A} :=
      fun k a ↦ ((e k).symm a : {x // x ∈ A})
    have huT (k : Fin p) (a : Fin 3) : u k a ∈ T k :=
      ((e k).symm a).property
    have huinj (k : Fin p) : Function.Injective (u k) := by
      intro a b hab
      apply (e k).symm.injective
      exact Subtype.ext hab
    let x : Fin p → Fin 3 → Point (2 * p) :=
      fun k a ↦ (u k a : Point (2 * p))
    have hxinj (k : Fin p) : Function.Injective (x k) :=
      Subtype.val_injective.comp (huinj k)
    have hxC (k : Fin p) (a : Fin 3) : x k a ∈ C.circle k := by
      apply hcore k (u k a)
      exact hTS k (huT k a)
    have hq (k : Fin p) (hki : k ≠ i₀) (a : Fin 3) :
        dist (v : Point (2 * p)) (x k a) = 1 := by
      exact (diameterGraph_adj A v (u k a)).mp (hTv k hki (u k a) (huT k a))
    exact hv ⟨i₀,
      EvenCarrierUpgrade.EvenCircleCarrier.mem_circle_of_unit_to_other_triples
        C hp x hxinj hxC i₀ (v : Point (2 * p)) hq⟩
  · have hlarge (k : Fin p) : 3 ≤ (N k).card := by
      have hk : ¬ (N k).card ≤ 2 := fun hk ↦ hlow ⟨k, hk⟩
      omega
    let i₀ : Fin p := ⟨0, by omega⟩
    obtain ⟨T₀, hT₀S, hT₀card⟩ :=
      Finset.exists_subset_card_eq (hthree i₀)
    have hchoose : ∀ k : Fin p, ∃ T : Finset {x // x ∈ A},
        T ⊆ S k ∧ T.card = 3 ∧
          (k ≠ i₀ → ∀ w ∈ T, G.Adj v w) := by
      intro k
      by_cases hki : k = i₀
      · subst k
        exact ⟨T₀, by simpa [S] using hT₀S, hT₀card, by simp⟩
      · obtain ⟨T, hTN, hTcard⟩ :=
          Finset.exists_subset_card_eq (hlarge k)
        refine ⟨T, ?_, hTcard, ?_⟩
        · exact hTN.trans (by intro w hw; exact (Finset.mem_filter.mp hw).1)
        · intro _ w hw
          exact (Finset.mem_filter.mp (hTN hw)).2
    choose T hTS hTcard hTv using hchoose
    let e (k : Fin p) : T k ≃ Fin 3 :=
      (T k).equivFinOfCardEq (hTcard k)
    let u : Fin p → Fin 3 → {x // x ∈ A} :=
      fun k a ↦ ((e k).symm a : {x // x ∈ A})
    have huT (k : Fin p) (a : Fin 3) : u k a ∈ T k :=
      ((e k).symm a).property
    have huinj (k : Fin p) : Function.Injective (u k) := by
      intro a b hab
      apply (e k).symm.injective
      exact Subtype.ext hab
    let x : Fin p → Fin 3 → Point (2 * p) :=
      fun k a ↦ (u k a : Point (2 * p))
    have hxinj (k : Fin p) : Function.Injective (x k) :=
      Subtype.val_injective.comp (huinj k)
    have hxC (k : Fin p) (a : Fin 3) : x k a ∈ C.circle k := by
      apply hcore k (u k a)
      exact hTS k (huT k a)
    have hq (k : Fin p) (hki : k ≠ i₀) (a : Fin 3) :
        dist (v : Point (2 * p)) (x k a) = 1 := by
      exact (diameterGraph_adj A v (u k a)).mp (hTv k hki (u k a) (huT k a))
    exact hv ⟨i₀,
      EvenCarrierUpgrade.EvenCircleCarrier.mem_circle_of_unit_to_other_triples
        C hp x hxinj hxC i₀ (v : Point (2 * p)) hq⟩

end Stability.StablePartition

/-- A Lenz decomposition records the unique carrier circle of every point.
This is the form used for edge counting. -/
structure EvenLenzDecomposition {p : ℕ} (A : Finset (Point (2 * p))) where
  carrier : EvenCircleCarrier p
  part : {x // x ∈ A} → Fin p
  mem_circle : ∀ x, (x : Point (2 * p)) ∈ carrier.circle (part x)

namespace EvenLenzDecomposition

variable {p : ℕ} {A : Finset (Point (2 * p))}

/-- Points assigned to different Lenz parts are at unit distance. -/
theorem dist_eq_one_of_part_ne (D : EvenLenzDecomposition A)
    {x y : {z // z ∈ A}} (hxy : D.part x ≠ D.part y) :
    dist (x : Point (2 * p)) (y : Point (2 * p)) = 1 :=
  D.carrier.dist_eq_one_of_mem_circle_of_ne hxy (D.mem_circle x) (D.mem_circle y)

/-- Consequently, every cross-part pair is an edge of the diameter graph. -/
theorem diameterGraph_adj_of_part_ne (D : EvenLenzDecomposition A)
    {x y : {z // z ∈ A}} (hxy : D.part x ≠ D.part y) :
    (diameterGraph A).Adj x y :=
  D.dist_eq_one_of_part_ne hxy

/-- The part containing a monochromatic edge. -/
noncomputable def monochromaticEdgePart (D : EvenLenzDecomposition A)
    (e : {e // e ∈ Stability.monochromaticEdges (diameterGraph A) D.part}) :
    Fin p :=
  (e.1.map D.part).diagElem
    ((Stability.mem_monochromaticEdges D.part).mp e.2).2

@[simp] theorem monochromaticEdgePart_mk (D : EvenLenzDecomposition A)
    (x y : {z // z ∈ A})
    (hxy : s(x, y) ∈ Stability.monochromaticEdges (diameterGraph A) D.part) :
    D.monochromaticEdgePart ⟨s(x, y), hxy⟩ = D.part x := by
  rfl

/-- A pointwise version of the local-circle input implies injectivity of the
edge-to-carrier map. -/
theorem monochromaticEdgePart_injective_of_internal_edge_unique
    (D : EvenLenzDecomposition A)
    (hunique : ∀ (i : Fin p) (x y z w : {a // a ∈ A}),
      D.part x = i → D.part y = i → D.part z = i → D.part w = i →
      (diameterGraph A).Adj x y → (diameterGraph A).Adj z w →
      s(x, y) = s(z, w)) :
    Function.Injective D.monochromaticEdgePart := by
  rintro ⟨e, he⟩ ⟨f, hf⟩ hef
  revert he hf hef
  refine Sym2.inductionOn₂ e f ?_
  intro x y z w he hf hef
  have he' := (Stability.mk_mem_monochromaticEdges_iff D.part x y).mp he
  have hf' := (Stability.mk_mem_monochromaticEdges_iff D.part z w).mp hf
  simp only [monochromaticEdgePart_mk] at hef
  apply Subtype.ext
  exact hunique (D.part x) x y z w rfl he'.2.symm hef.symm
    (hf'.2.symm.trans hef.symm) he'.1 hf'.1

/-- If each carrier circle contributes at most one internal diameter, mapping
a monochromatic edge to its circle is injective, and hence there are at most
`p` internal diameter pairs. -/
theorem card_monochromaticEdges_le_of_edgePart_injective
    (D : EvenLenzDecomposition A)
    (hinj : Function.Injective D.monochromaticEdgePart) :
    (Stability.monochromaticEdges (diameterGraph A) D.part).card ≤ p := by
  rw [← Fintype.card_coe]
  simpa using Fintype.card_le_of_injective D.monochromaticEdgePart hinj

/-- The cross-part subgraph has at most the Turán number of edges. -/
theorem card_partiteCore_le_turanNumber (D : EvenLenzDecomposition A)
    : (Stability.partiteCore (diameterGraph A) D.part).edgeFinset.card ≤
      turanNumber p A.card := by
  have hcolor :
      (Stability.partiteCore (diameterGraph A) D.part).Colorable p :=
    Stability.partiteCore_colorable (diameterGraph A) D.part
  have hfree := hcolor.cliqueFree (Nat.lt_succ_self p)
  rw [turanNumber_eq]
  simpa using hfree.card_edgeFinset_le

/-- Once the total number of within-circle diameter pairs is at most `p`,
the usual `t_p(n) + p` upper bound follows. -/
theorem diameterPairCount_le_turanNumber_add (D : EvenLenzDecomposition A)
    (hinternal : (Stability.monochromaticEdges (diameterGraph A) D.part).card ≤ p) :
    diameterPairCount A ≤ turanNumber p A.card + p := by
  rw [diameterPairCount,
    Stability.card_edgeFinset_eq_card_partiteCore_add_card_monochromatic D.part]
  exact Nat.add_le_add D.card_partiteCore_le_turanNumber hinternal

/-- The recorded part agrees with membership in any carrier circle. -/
theorem part_eq_of_mem_circle (D : EvenLenzDecomposition A)
    (x : {z // z ∈ A}) {i : Fin p}
    (hxi : (x : Point (2 * p)) ∈ D.carrier.circle i) : D.part x = i :=
  D.carrier.circle_index_unique (D.mem_circle x) hxi

/-- In dimension at least six, two internal diameter edges in the same
carrier circle have the same unordered endpoints. -/
theorem internal_edge_unique (D : EvenLenzDecomposition A) (hp : 3 ≤ p)
    (hA : IsDiameterOne A) (i : Fin p) (x y z w : {a // a ∈ A})
    (hxi : D.part x = i) (hyi : D.part y = i)
    (hzi : D.part z = i) (hwi : D.part w = i)
    (hxy : (diameterGraph A).Adj x y) (hzw : (diameterGraph A).Adj z w) :
    s(x, y) = s(z, w) := by
  have hxC : (x : Point (2 * p)) ∈ D.carrier.circle i := by
    simpa [hxi] using D.mem_circle x
  have hyC : (y : Point (2 * p)) ∈ D.carrier.circle i := by
    simpa [hyi] using D.mem_circle y
  have hzC : (z : Point (2 * p)) ∈ D.carrier.circle i := by
    simpa [hzi] using D.mem_circle z
  have hwC : (w : Point (2 * p)) ∈ D.carrier.circle i := by
    simpa [hwi] using D.mem_circle w
  have hsqrt2pos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrtlt : Real.sqrt (2 : ℝ) < Real.sqrt 3 :=
    Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hr : 1 / Real.sqrt 3 < D.carrier.radius i := by
    rw [D.carrier.radius_eq_inv_sqrt_two hp]
    exact one_div_lt_one_div_of_lt hsqrt2pos hsqrtlt
  have h := LocalCircle.unit_chords_eq_or_swap_of_large_radius
    (D.carrier.plane_finrank i) (D.carrier.center_mem i)
    hxC.1 hyC.1 hzC.1 hwC.1 hxC.2 hyC.2 hzC.2 hwC.2 hr
    hxy hzw
    (hA.dist_le x.property z.property)
    (hA.dist_le x.property w.property)
    (hA.dist_le y.property z.property)
    (hA.dist_le y.property w.property)
  rcases h with ⟨hzx, hwy⟩ | ⟨hzy, hwx⟩
  · have hzxe : z = x := Subtype.ext hzx
    have hwye : w = y := Subtype.ext hwy
    subst z
    subst w
    rfl
  · have hzye : z = y := Subtype.ext hzy
    have hwxe : w = x := Subtype.ext hwx
    subst z
    subst w
    exact Sym2.eq_swap

/-- A diameter-one even Lenz configuration in dimension at least six has
at most one internal diameter on each carrier circle. -/
theorem card_monochromaticEdges_le (D : EvenLenzDecomposition A)
    (hp : 3 ≤ p) (hA : IsDiameterOne A) :
    (Stability.monochromaticEdges (diameterGraph A) D.part).card ≤ p := by
  apply D.card_monochromaticEdges_le_of_edgePart_injective
  apply D.monochromaticEdgePart_injective_of_internal_edge_unique
  exact D.internal_edge_unique hp hA

/-- The sharp upper bound inside the class of even-dimensional Lenz
configurations (`d ≥ 6`). -/
theorem diameterPairCount_le_turanNumber_add_of_isDiameterOne
    (D : EvenLenzDecomposition A) (hp : 3 ≤ p) (hA : IsDiameterOne A) :
    diameterPairCount A ≤ turanNumber p A.card + p :=
  D.diameterPairCount_le_turanNumber_add (D.card_monochromaticEdges_le hp hA)

end EvenLenzDecomposition

/-- An explicitly given carrier proves the Lenz property. -/
theorem isEvenLenz_of_forall_mem_circle {p : ℕ}
    {A : Finset (Point (2 * p))} (C : EvenCircleCarrier p)
    (hA : ∀ x ∈ A, ∃ i, x ∈ C.circle i) : IsEvenLenz A :=
  ⟨C, hA⟩

/-- The existential carrier formulation and the decomposition formulation
are equivalent. -/
theorem isEvenLenz_iff_exists_decomposition {p : ℕ}
    {A : Finset (Point (2 * p))} :
    IsEvenLenz A ↔ Nonempty (EvenLenzDecomposition A) := by
  constructor
  · rintro ⟨C, hC⟩
    let part : {x // x ∈ A} → Fin p := fun x ↦ (hC x x.property).choose
    exact ⟨⟨C, part, fun x ↦ (hC x x.property).choose_spec⟩⟩
  · rintro ⟨D⟩
    exact ⟨D.carrier, fun x hx ↦ ⟨D.part ⟨x, hx⟩, D.mem_circle ⟨x, hx⟩⟩⟩

/-- Choose the canonical part decomposition supplied by a Lenz carrier. -/
noncomputable def IsEvenLenz.decomposition {p : ℕ}
    {A : Finset (Point (2 * p))} (hA : IsEvenLenz A) :
    EvenLenzDecomposition A :=
  (isEvenLenz_iff_exists_decomposition.mp hA).some

/-- Structural exact upper bound for every diameter-one even Lenz
configuration in dimension at least six. -/
theorem IsEvenLenz.diameterPairCount_le_turanNumber_add {p : ℕ}
    {A : Finset (Point (2 * p))} (hL : IsEvenLenz A)
    (hp : 3 ≤ p) (hA : IsDiameterOne A) :
    diameterPairCount A ≤ turanNumber p A.card + p :=
  hL.decomposition.diameterPairCount_le_turanNumber_add_of_isDiameterOne hp hA

/-- The Lenz property is inherited by subsets. -/
theorem IsEvenLenz.mono {p : ℕ} {A B : Finset (Point (2 * p))}
    (hB : IsEvenLenz B) (hAB : A ⊆ B) : IsEvenLenz A := by
  obtain ⟨C, hC⟩ := hB
  exact ⟨C, fun x hx ↦ hC x (hAB hx)⟩

/-! ## Numerical core of the exceptional-point replacement

The geometric stability argument produces an exceptional class and `p`
large carrier classes.  For the fixed error `1 / (2p²)`, a point outside
the carrier has at most two neighbours in each of two carrier classes.
Replacing it by a safe point of one of those circles gains degree.  The
following declarations isolate, and prove, all arithmetic in that last
comparison.
-/

namespace ReplacementNumerics

open Finset Fintype

/-- The error used in Swanepoel's even-dimensional replacement argument. -/
def stabilityEpsilon (p : ℕ) : ℝ := 1 / (2 * (p : ℝ) ^ 2)

/-- Cardinality information supplied by an even-dimensional stability
partition. -/
structure StableEvenCore (p n : ℕ) where
  exceptionalCard : ℕ
  partCard : Fin p → ℕ
  exceptional_lt :
    (exceptionalCard : ℝ) < stabilityEpsilon p * n
  part_lower : ∀ i,
    (n : ℝ) / p - stabilityEpsilon p * n < partCard i
  part_upper : ∀ i,
    (partCard i : ℝ) < (n : ℝ) / p + stabilityEpsilon p * n

variable {p n : ℕ} (K : StableEvenCore p n)

/-- Every regular class is strictly larger than the exceptional class. -/
theorem exceptionalCard_lt_partCard (hp : 2 ≤ p) (hn : 0 < n) (i : Fin p) :
    K.exceptionalCard < K.partCard i := by
  apply (Nat.cast_lt (α := ℝ)).mp
  have hlow := K.part_lower i
  have hexceptional := K.exceptional_lt
  have hzero : (0 : ℝ) < n := by exact_mod_cast hn
  have hpzero : (0 : ℝ) < p := by positivity
  have hpcast : (2 : ℝ) ≤ p := by exact_mod_cast hp
  simp only [stabilityEpsilon] at hexceptional hlow
  field_simp [ne_of_gt hpzero] at hexceptional hlow ⊢
  nlinarith [sq_pos_of_pos hpzero]

/-- Above the replacement threshold every regular class contains at least
three points, as required by the complete multipartite geometry lemma. -/
theorem three_le_partCard (hp : 2 ≤ p) (hn : 3 * p ^ 2 ≤ n) (i : Fin p) :
    3 ≤ K.partCard i := by
  by_contra h
  have hpart : K.partCard i ≤ 2 := by omega
  have hlow := K.part_lower i
  have hpzero : (0 : ℝ) < p := by positivity
  have hpcast : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hncast : (3 : ℝ) * (p : ℝ) ^ 2 ≤ n := by exact_mod_cast hn
  have hpartcast : (K.partCard i : ℝ) ≤ 2 := by exact_mod_cast hpart
  simp only [stabilityEpsilon] at hlow
  field_simp [ne_of_gt hpzero] at hlow
  nlinarith [sq_pos_of_pos hpzero]

private theorem card_univ_erase (_hp : 1 ≤ p) (i : Fin p) :
    (Finset.univ.erase i).card = p - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin]

private theorem card_univ_erase_erase (hp : 2 ≤ p) {i j : Fin p} (hij : i ≠ j) :
    ((Finset.univ.erase i).erase j).card = p - 2 := by
  have hj : j ∈ Finset.univ.erase i := by simp [hij.symm]
  rw [Finset.card_erase_of_mem hj, card_univ_erase (by omega) i]
  omega

/-- Upper bound for the sum of all part sizes except two specified parts. -/
theorem sum_erase_two_upper (hp : 2 ≤ p) {i j : Fin p} (hij : i ≠ j) :
    ((∑ k ∈ (Finset.univ.erase i).erase j, K.partCard k : ℕ) : ℝ) ≤
      (p - 2 : ℕ) * ((n : ℝ) / p + stabilityEpsilon p * n) := by
  rw [Nat.cast_sum]
  calc
    ∑ k ∈ (Finset.univ.erase i).erase j, (K.partCard k : ℝ)
        ≤ ∑ _k ∈ (Finset.univ.erase i).erase j,
            ((n : ℝ) / p + stabilityEpsilon p * n) := by
          exact Finset.sum_le_sum fun k _ ↦ (K.part_upper k).le
    _ = ((Finset.univ.erase i).erase j).card *
          ((n : ℝ) / p + stabilityEpsilon p * n) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    _ = (p - 2 : ℕ) * ((n : ℝ) / p + stabilityEpsilon p * n) := by
          rw [card_univ_erase_erase hp hij]

/-- Strict lower bound for the sum of all part sizes except one specified
part. -/
theorem sum_erase_one_lower (hp : 2 ≤ p) (i : Fin p) :
    (p - 1 : ℕ) * ((n : ℝ) / p - stabilityEpsilon p * n) <
      ((∑ k ∈ Finset.univ.erase i, K.partCard k : ℕ) : ℝ) := by
  have hne : (Finset.univ.erase i).Nonempty := by
    rw [← Finset.card_pos, card_univ_erase (by omega) i]
    omega
  rw [Nat.cast_sum]
  calc
    (p - 1 : ℕ) * ((n : ℝ) / p - stabilityEpsilon p * n)
        = ∑ _k ∈ Finset.univ.erase i,
            ((n : ℝ) / p - stabilityEpsilon p * n) := by
          rw [Finset.sum_const, nsmul_eq_mul, card_univ_erase (by omega) i]
    _ < ∑ k ∈ Finset.univ.erase i, (K.partCard k : ℝ) := by
          exact Finset.sum_lt_sum_of_nonempty hne fun k _ ↦ K.part_lower k

/-- The numerical heart of the even-dimensional exceptional-point removal.

`oldDegree` is bounded by the exceptional vertices, the four possible
neighbours in two low classes (with the old vertex itself removed), and all
vertices in the other `p - 2` classes.  `newDegree` is at least every vertex
outside the target class.  At `n ≥ 3p²`, replacement strictly gains degree. -/
theorem degree_strictly_increases
    (hp : 2 ≤ p) (hn : 3 * p ^ 2 ≤ n)
    {i j : Fin p} (hij : i ≠ j) {oldDegree newDegree : ℕ}
    (hold : oldDegree ≤ K.exceptionalCard + 3 +
      ∑ k ∈ (Finset.univ.erase i).erase j, K.partCard k)
    (hnew : (∑ k ∈ Finset.univ.erase i, K.partCard k) ≤ newDegree) :
    oldDegree < newDegree := by
  have holdcast : (oldDegree : ℝ) ≤
      K.exceptionalCard + 3 +
        ((∑ k ∈ (Finset.univ.erase i).erase j, K.partCard k : ℕ) : ℝ) := by
    exact_mod_cast hold
  have holdsum := sum_erase_two_upper K hp hij
  have hnewsum := sum_erase_one_lower K hp i
  have hnewcast :
      (((∑ k ∈ Finset.univ.erase i, K.partCard k : ℕ) : ℝ)) ≤ newDegree := by
    exact_mod_cast hnew
  have hpzero : (0 : ℝ) < p := by positivity
  have hncast : (3 : ℝ) * (p : ℝ) ^ 2 ≤ n := by exact_mod_cast hn
  have hexceptional := K.exceptional_lt
  simp only [stabilityEpsilon] at hexceptional holdsum hnewsum
  field_simp [ne_of_gt hpzero] at hexceptional holdsum hnewsum
  rw [Nat.cast_sub hp] at holdsum
  rw [Nat.cast_sub (by omega : 1 ≤ p)] at hnewsum
  norm_num only [Nat.cast_ofNat] at holdsum hnewsum
  have hlt : (oldDegree : ℝ) < newDegree := by
    have hscale : (0 : ℝ) ≤ 2 * (p : ℝ) ^ 2 := by positivity
    have holdscaled := mul_le_mul_of_nonneg_left holdcast hscale
    have hnewscaled := mul_le_mul_of_nonneg_left hnewcast hscale
    by_contra hnot
    have hdegree : (newDegree : ℝ) ≤ oldDegree := le_of_not_gt hnot
    have hdegreescaled := mul_le_mul_of_nonneg_left hdegree hscale
    nlinarith [sq_pos_of_pos hpzero]
  exact_mod_cast hlt

end ReplacementNumerics

/-! ## Removing the exceptional vertices -/

namespace EvenExceptionalRemoval

open Finset Fintype SimpleGraph

/-- Vertices of a configuration which already lie on one of the circles of
an assembled carrier. -/
noncomputable def carrierVertices {p : ℕ} {A : Finset (Point (2 * p))}
    (C : EvenCircleCarrier p) : Finset {x // x ∈ A} := by
  classical
  exact Finset.univ.filter fun v ↦ ∃ i, (v : Point (2 * p)) ∈ C.circle i

/-- The corresponding point configuration. -/
noncomputable def carrierPoints {p : ℕ} (A : Finset (Point (2 * p)))
    (C : EvenCircleCarrier p) : Finset (Point (2 * p)) := by
  classical
  exact A.filter fun x ↦ ∃ i, x ∈ C.circle i

@[simp] theorem mem_carrierVertices {p : ℕ} {A : Finset (Point (2 * p))}
    {C : EvenCircleCarrier p} {v : {x // x ∈ A}} :
    v ∈ carrierVertices C ↔ ∃ i, (v : Point (2 * p)) ∈ C.circle i := by
  simp [carrierVertices]

@[simp] theorem mem_carrierPoints {p : ℕ} {A : Finset (Point (2 * p))}
    {C : EvenCircleCarrier p} {x : Point (2 * p)} :
    x ∈ carrierPoints A C ↔ x ∈ A ∧ ∃ i, x ∈ C.circle i := by
  simp [carrierPoints]

theorem card_carrierPoints_eq_card_carrierVertices
    {p : ℕ} {A : Finset (Point (2 * p))} (C : EvenCircleCarrier p) :
    (carrierPoints A C).card = (carrierVertices (A := A) C).card := by
  classical
  refine Finset.card_bij
    (fun x hx ↦ ⟨x, (mem_carrierPoints.mp hx).1⟩) ?_ ?_ ?_
  · intro x hx
    exact mem_carrierVertices.mpr (mem_carrierPoints.mp hx).2
  · intro x hx y hy hxy
    exact Subtype.ext_iff.mp hxy
  · intro v hv
    refine ⟨(v : Point (2 * p)), mem_carrierPoints.mpr
      ⟨v.property, mem_carrierVertices.mp hv⟩, ?_⟩
    rfl

/-- The on-carrier points form a genuine even Lenz configuration. -/
theorem isEvenLenz_carrierPoints {p : ℕ} {A : Finset (Point (2 * p))}
    (C : EvenCircleCarrier p) : IsEvenLenz (carrierPoints A C) := by
  refine ⟨C, ?_⟩
  intro x hx
  exact (mem_carrierPoints.mp hx).2

/-- The induced diameter graph on the on-carrier vertices is canonically
isomorphic to the diameter graph of the filtered point configuration. -/
theorem card_induce_carrierVertices_eq_diameterPairCount
    {p : ℕ} {A : Finset (Point (2 * p))} (C : EvenCircleCarrier p) :
    ((diameterGraph A).induce
      (↑(carrierVertices (A := A) C) : Set {x // x ∈ A})).edgeFinset.card =
      diameterPairCount (carrierPoints A C) := by
  classical
  let e : {v : {x // x ∈ A} // v ∈ carrierVertices (A := A) C} ≃
      {x // x ∈ carrierPoints A C} :=
    { toFun := fun v ↦ ⟨(v.1 : Point (2 * p)),
        mem_carrierPoints.mpr ⟨v.1.property, mem_carrierVertices.mp v.2⟩⟩
      invFun := fun x ↦ ⟨⟨(x : Point (2 * p)), (mem_carrierPoints.mp x.2).1⟩,
        mem_carrierVertices.mpr (mem_carrierPoints.mp x.2).2⟩
      left_inv := by intro v; exact Subtype.ext (Subtype.ext rfl)
      right_inv := by intro x; exact Subtype.ext rfl }
  let iso : (diameterGraph A).induce
      (↑(carrierVertices (A := A) C) : Set {x // x ∈ A}) ≃g
      diameterGraph (carrierPoints A C) := by
    refine { toEquiv := e, map_rel_iff' := ?_ }
    intro v w
    rfl
  rw [diameterPairCount]
  exact iso.card_edgeFinset_eq

/-- Sharp carrier upper bound for the induced on-carrier subgraph. -/
theorem card_induce_carrierVertices_le
    {p : ℕ} (hp : 3 ≤ p) {A : Finset (Point (2 * p))}
    (hA : IsDiameterOne A) (C : EvenCircleCarrier p)
    (hnonempty : ∀ i, ∃ x ∈ A, x ∈ C.circle i) :
    ((diameterGraph A).induce
      (↑(carrierVertices (A := A) C) : Set {x // x ∈ A})).edgeFinset.card ≤
      turanNumber p (carrierVertices (A := A) C).card + p := by
  rw [card_induce_carrierVertices_eq_diameterPairCount]
  rw [← card_carrierPoints_eq_card_carrierVertices C]
  apply (isEvenLenz_carrierPoints C).diameterPairCount_le_turanNumber_add hp
  rw [isDiameterOne_iff]
  constructor
  · intro x hx y hy
    exact hA.dist_le (mem_carrierPoints.mp hx).1 (mem_carrierPoints.mp hy).1
  · let i : Fin p := ⟨0, by omega⟩
    obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card (α := Fin p) (by
      rw [Fintype.card_fin]
      omega) i
    obtain ⟨x, hxA, hxC⟩ := hnonempty i
    obtain ⟨y, hyA, hyC⟩ := hnonempty j
    exact ⟨x, mem_carrierPoints.mpr ⟨hxA, ⟨i, hxC⟩⟩,
      y, mem_carrierPoints.mpr ⟨hyA, ⟨j, hyC⟩⟩,
      C.dist_eq_one_of_mem_circle_of_ne hji.symm hxC hyC⟩

/-- Retained fibers belonging to different colors are disjoint. -/
private theorem retainedFiber_disjoint
    {V : Type*} [Fintype V] [DecidableEq V] {p : ℕ} (c : V → Fin p) (S0 : Finset V)
    {i j : Fin p} (hij : i ≠ j) :
    Disjoint (Stability.retainedFiber c S0 i)
      (Stability.retainedFiber c S0 j) := by
  rw [Finset.disjoint_left]
  intro v hvi hvj
  have hi := (Stability.mem_retainedFiber c S0 i v).mp hvi
  have hj := (Stability.mem_retainedFiber c S0 j v).mp hvj
  exact hij (hi.1.symm.trans hj.1)

/-- The two-low-fibers conclusion gives the required quantitative bound on
the number of on-carrier neighbours of an off-carrier vertex. -/
theorem card_neighbors_inter_carrierVertices_le
    {p : ℕ} (hp : 2 ≤ p) {A : Finset (Point (2 * p))} {epsilon : ℝ}
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (C : EvenCircleCarrier p)
    (hcore : ∀ (i : Fin p) (w : {x // x ∈ A}),
      w ∈ Stability.retainedFiber P.color P.exceptional i →
        (w : Point (2 * p)) ∈ C.circle i)
    (hthree : ∀ i, 3 ≤ (Stability.retainedFiber
      P.color P.exceptional i).card)
    (v : {x // x ∈ A}) (hv : v ∉ carrierVertices (A := A) C) :
    (((diameterGraph A).neighborFinset v ∩ carrierVertices (A := A) C).card : ℝ) ≤
      (carrierVertices (A := A) C).card -
        2 * ((A.card : ℝ) / p - epsilon * A.card) + 4 := by
  classical
  let G := diameterGraph A
  let L := carrierVertices (A := A) C
  let S : Fin p → Finset {x // x ∈ A} :=
    fun i ↦ Stability.retainedFiber P.color P.exceptional i
  have hv' : ¬ ∃ i, (v : Point (2 * p)) ∈ C.circle i := by
    simpa [L] using hv
  obtain ⟨i, j, hij, hi, hj⟩ :=
    P.exists_two_low_fibers_of_not_mem_carrier hp C hcore hthree v hv'
  have hSiL : S i ⊆ L := by
    intro w hw
    exact mem_carrierVertices.mpr ⟨i, hcore i w hw⟩
  have hSjL : S j ⊆ L := by
    intro w hw
    exact mem_carrierVertices.mpr ⟨j, hcore j w hw⟩
  have hdisj : Disjoint (S i) (S j) :=
    retainedFiber_disjoint P.color P.exceptional hij
  let R := L \ (S i ∪ S j)
  let Ni := (S i).filter (G.Adj v)
  let Nj := (S j).filter (G.Adj v)
  have hsubset : G.neighborFinset v ∩ L ⊆ R ∪ Ni ∪ Nj := by
    intro w hw
    have hw' := Finset.mem_inter.mp hw
    by_cases hwi : w ∈ S i
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hwi, (G.mem_neighborFinset v w).mp hw'.1⟩))
    · by_cases hwj : w ∈ S j
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hwj, (G.mem_neighborFinset v w).mp hw'.1⟩)
      · apply Finset.mem_union_left
        apply Finset.mem_union_left
        apply Finset.mem_sdiff.mpr
        refine ⟨hw'.2, ?_⟩
        intro hwU
        rcases Finset.mem_union.mp hwU with hwi' | hwj'
        · exact hwi hwi'
        · exact hwj hwj'
  have hcardNat : (G.neighborFinset v ∩ L).card ≤
      R.card + Ni.card + Nj.card := by
    calc
      (G.neighborFinset v ∩ L).card ≤ (R ∪ Ni ∪ Nj).card :=
        Finset.card_le_card hsubset
      _ ≤ (R ∪ Ni).card + Nj.card := Finset.card_union_le _ _
      _ ≤ R.card + Ni.card + Nj.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
  have hunionSubset : S i ∪ S j ⊆ L := Finset.union_subset hSiL hSjL
  have hunionCard : (S i ∪ S j).card = (S i).card + (S j).card :=
    Finset.card_union_of_disjoint hdisj
  have hsumle : (S i).card + (S j).card ≤ L.card := by
    rw [← hunionCard]
    exact Finset.card_le_card hunionSubset
  have hRcard : R.card + (S i).card + (S j).card = L.card := by
    dsimp [R]
    rw [Finset.card_sdiff_of_subset hunionSubset, hunionCard]
    omega
  have hi' : Ni.card ≤ 2 := by simpa [Ni, S, G] using hi
  have hj' : Nj.card ≤ 2 := by simpa [Nj, S, G] using hj
  have hcount : (G.neighborFinset v ∩ L).card + (S i).card + (S j).card ≤
      L.card + 4 := by omega
  have hcountR : ((G.neighborFinset v ∩ L).card : ℝ) +
      (S i).card + (S j).card ≤ (L.card : ℝ) + 4 := by
    exact_mod_cast hcount
  have hbal_i := (abs_lt.mp (P.balanced i)).1
  have hbal_j := (abs_lt.mp (P.balanced j)).1
  have hcardA : Fintype.card {x // x ∈ A} = A.card := by simp
  rw [hcardA] at hbal_i hbal_j
  nlinarith

/-- Edge decomposition relative to the carrier, with the crossing term
bounded by the two-low-fibers estimate and the off-carrier induced graph by
the complete graph. -/
theorem card_edgeFinset_le_of_stable_core
    {p : ℕ} (hp : 3 ≤ p) {A : Finset (Point (2 * p))} {epsilon : ℝ}
    (hA : IsDiameterOne A)
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (C : EvenCircleCarrier p)
    (hcore : ∀ (i : Fin p) (w : {x // x ∈ A}),
      w ∈ Stability.retainedFiber P.color P.exceptional i →
        (w : Point (2 * p)) ∈ C.circle i)
    (hthree : ∀ i, 3 ≤ (Stability.retainedFiber
      P.color P.exceptional i).card) :
    let L := carrierVertices (A := A) C
    let B := Lᶜ
    ((diameterGraph A).edgeFinset.card : ℝ) ≤
      turanNumber p L.card + p +
        (B.card : ℝ) *
          ((L.card : ℝ) - 2 * ((A.card : ℝ) / p - epsilon * A.card) + 4) +
        (B.card.choose 2 : ℕ) := by
  classical
  let G := diameterGraph A
  let L := carrierVertices (A := A) C
  let B := Lᶜ
  have hnonempty : ∀ i, ∃ x ∈ A, x ∈ C.circle i := by
    intro i
    have hne : (Stability.retainedFiber P.color P.exceptional i).Nonempty :=
      Finset.card_pos.mp (by have := hthree i; omega)
    obtain ⟨v, hv⟩ := hne
    exact ⟨(v : Point (2 * p)), v.property, hcore i v hv⟩
  have hinside : (G.induce (↑L : Set {x // x ∈ A})).edgeFinset.card ≤
      turanNumber p L.card + p := by
    simpa [G, L] using card_induce_carrierVertices_le hp hA C hnonempty
  have hoff (v : {x // x ∈ A}) (hv : v ∈ B) :
      (((G.neighborFinset v ∩ L).card : ℝ)) ≤
        (L.card : ℝ) - 2 * ((A.card : ℝ) / p - epsilon * A.card) + 4 := by
    apply card_neighbors_inter_carrierVertices_le (by omega) P C hcore hthree v
    have hv' : v ∉ L := by
      change v ∈ Lᶜ at hv
      exact Finset.mem_compl.mp hv
    simpa only [L] using hv'
  let X : Finset ({x // x ∈ A} × {x // x ∈ A}) :=
    (L ×ˢ B).filter fun e ↦ G.Adj e.1 e.2
  have hcross : (X.card : ℝ) =
      ∑ v ∈ B, ((G.neighborFinset v ∩ L).card : ℝ) := by
    calc
      (X.card : ℝ) =
          ∑ x ∈ L, ∑ v ∈ B, if G.Adj x v then (1 : ℝ) else 0 := by
        simp only [X, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
          Nat.cast_one, Nat.cast_zero, Finset.sum_product]
      _ = ∑ v ∈ B, ∑ x ∈ L, if G.Adj v x then (1 : ℝ) else 0 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro v hv
        apply Finset.sum_congr rfl
        intro x hx
        simpa only [G.adj_comm]
      _ = ∑ v ∈ B, ((G.neighborFinset v ∩ L).card : ℝ) := by
        apply Finset.sum_congr rfl
        intro v hv
        have heq : G.neighborFinset v ∩ L = L.filter (G.Adj v) := by
          ext x
          simp [and_comm]
        rw [heq, Finset.card_filter, Nat.cast_sum]
        simp
  have hcrossBound : (X.card : ℝ) ≤
      (B.card : ℝ) *
        ((L.card : ℝ) - 2 * ((A.card : ℝ) / p - epsilon * A.card) + 4) := by
    rw [hcross]
    calc
      ∑ v ∈ B, ((G.neighborFinset v ∩ L).card : ℝ) ≤
          ∑ _v ∈ B,
            ((L.card : ℝ) - 2 * ((A.card : ℝ) / p - epsilon * A.card) + 4) := by
        exact Finset.sum_le_sum fun v hv ↦ hoff v hv
      _ = (B.card : ℝ) *
            ((L.card : ℝ) - 2 * ((A.card : ℝ) / p - epsilon * A.card) + 4) := by
        rw [Finset.sum_const, nsmul_eq_mul]
  have hBcard : Fintype.card {v : {x // x ∈ A} // v ∈ (↑B : Set _)} = B.card := by
    simp
  have hBinside : (G.induce (↑B : Set {x // x ∈ A})).edgeFinset.card ≤
      B.card.choose 2 := by
    simpa [hBcard] using
      (G.induce (↑B : Set {x // x ∈ A})).card_edgeFinset_le_card_choose_two
  have hdecomp0 := Stability.card_edgeFinset_decomp G L
  have hdecomp : G.edgeFinset.card =
      (G.induce (↑L : Set {x // x ∈ A})).edgeFinset.card + X.card +
        (G.induce (↑B : Set {x // x ∈ A})).edgeFinset.card := by
    simpa only [X, B] using hdecomp0
  have hdecompR : (G.edgeFinset.card : ℝ) =
      (G.induce (↑L : Set {x // x ∈ A})).edgeFinset.card + X.card +
        (G.induce (↑B : Set {x // x ∈ A})).edgeFinset.card := by
    exact_mod_cast hdecomp
  dsimp only
  dsimp [G] at hdecompR
  norm_num only [Nat.cast_add]
  have hinsideR : ((G.induce (↑L : Set {x // x ∈ A})).edgeFinset.card : ℝ) ≤
      turanNumber p L.card + p := by exact_mod_cast hinside
  have hBinsideR : ((G.induce (↑B : Set {x // x ∈ A})).edgeFinset.card : ℝ) ≤
      B.card.choose 2 := by exact_mod_cast hBinside
  change (G.edgeFinset.card : ℝ) ≤ _
  nlinarith

/-! ### Turán growth and the strict exceptional-edge deficit -/

/-- Each new vertex increases the Turán number by at least the continuous
balanced marginal. -/
theorem turanNumber_succ_gap_real {p : ℕ} (hp : 0 < p) (m : ℕ) :
    (((p : ℝ) - 1) / p) * m ≤
      (turanNumber p (m + 1) : ℝ) - turanNumber p m := by
  rw [turanNumber_succ_formula hp]
  rw [Nat.cast_add, Nat.cast_sub (Nat.div_le_self m p)]
  have hdiv : ((m / p : ℕ) : ℝ) ≤ (m : ℝ) / p := Nat.cast_div_le
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have heq : (((p : ℝ) - 1) / p) * m = (m : ℝ) - (m : ℝ) / p := by
    field_simp
  rw [heq]
  nlinarith

/-- Adding `b` vertices increases `t_p` by at least `b` times the balanced
marginal at the initial size. -/
theorem turanNumber_add_gap_real {p : ℕ} (hp : 0 < p) (l b : ℕ) :
    (turanNumber p l : ℝ) +
        (((p : ℝ) - 1) / p) * b * l ≤ turanNumber p (l + b) := by
  induction b with
  | zero => simp
  | succ b ih =>
      have hstep := turanNumber_succ_gap_real hp (l + b)
      have hcoeff : 0 ≤ ((p : ℝ) - 1) / p := by
        have hpR : (0 : ℝ) < p := by exact_mod_cast hp
        exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast hp)) hpR.le
      rw [show l + (b + 1) = (l + b) + 1 by omega]
      norm_num only [Nat.cast_add, Nat.cast_one]
      norm_num only [Nat.cast_add] at hstep
      have hl : (l : ℝ) ≤ l + b := by
        exact_mod_cast Nat.le_add_right l b
      calc
        (turanNumber p l : ℝ) + ((p : ℝ) - 1) / p * (b + 1) * l =
            ((turanNumber p l : ℝ) + ((p : ℝ) - 1) / p * b * l) +
              ((p : ℝ) - 1) / p * l := by ring
        _ ≤ (turanNumber p (l + b) : ℝ) + ((p : ℝ) - 1) / p * l :=
          add_le_add ih (le_refl _)
        _ ≤ (turanNumber p (l + b) : ℝ) + ((p : ℝ) - 1) / p * (l + b) := by
          exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hl hcoeff)
        _ ≤ turanNumber p (l + b + 1) := by linarith

/-- Pure arithmetic form of the exceptional-vertex deficit.  The
off-carrier crossing estimate plus all possible off-carrier internal edges
is strictly smaller than the Turán growth obtained by restoring those
vertices. -/
theorem offCarrier_extra_lt_turan_gap
    {p n l b : ℕ} {epsilon : ℝ} (hp : 3 ≤ p)
    (hsum : l + b = n) (hb : 0 < b) (hepsilon : 0 ≤ epsilon)
    (hbsmall : (b : ℝ) < epsilon * n)
    (hlarge : 5 * (p : ℝ) * epsilon * n + 7 * p < 2 * n) :
    (b : ℝ) * ((l : ℝ) - 2 * ((n : ℝ) / p - epsilon * n) + 4) +
        (b.choose 2 : ℕ) <
      (((p : ℝ) - 1) / p) * b * l := by
  have hpR : (0 : ℝ) < p := by positivity
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hsumR : (l : ℝ) + b = n := by exact_mod_cast hsum
  have hbsub : 1 ≤ b := by omega
  have hchooseNat : 2 * b.choose 2 = b * (b - 1) := by
    rw [Nat.choose_two_right]
    rw [mul_comm]
    exact Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self b)
  have hchoose : (2 : ℝ) * (b.choose 2 : ℕ) = b * (b - 1) := by
    exact_mod_cast hchooseNat
  have hbsubR : ((b - 1 : ℕ) : ℝ) = b - 1 := by
    rw [Nat.cast_sub hbsub]
    norm_num
  have hpge : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hbadterm : (2 - (p : ℝ)) * (epsilon * n) ≤ (2 - (p : ℝ)) * b := by
    exact mul_le_mul_of_nonpos_left hbsmall.le (by linarith)
  have hscaled :
      (2 * (p : ℝ)) *
        ((b : ℝ) * ((l : ℝ) - 2 * ((n : ℝ) / p - epsilon * n) + 4) +
          (b.choose 2 : ℕ)) <
      (2 * (p : ℝ)) * ((((p : ℝ) - 1) / p) * b * l) := by
    field_simp
    nlinarith
  have hscale : (0 : ℝ) < 2 * (p : ℝ) := by positivity
  nlinarith

/-- A fixed stability error small enough simultaneously for the greedy
four-point selections and the final exceptional-edge deficit. -/
def evenStabilityEpsilon (p : ℕ) : ℝ := 1 / (100 * (p : ℝ) ^ 2)

/-! ### The exceptional four-dimensional carrier optimization -/

/-- Forget the ambient-subtype wrapper on a finite vertex set. -/
def vertexPoints {d : ℕ} {A : Finset (Point d)}
    (S : Finset {x // x ∈ A}) : Finset (Point d) :=
  S.image fun v : {x // x ∈ A} ↦ (v : Point d)

@[simp] theorem card_vertexPoints {d : ℕ} {A : Finset (Point d)}
    (S : Finset {x // x ∈ A}) : (vertexPoints S).card = S.card := by
  rw [vertexPoints, Finset.card_image_iff.mpr Subtype.val_injective.injOn]

theorem card_induce_eq_diameterPairCount_vertexPoints
    {d : ℕ} {A : Finset (Point d)} (S : Finset {x // x ∈ A}) :
    ((diameterGraph A).induce (↑S : Set {x // x ∈ A})).edgeFinset.card =
      diameterPairCount (vertexPoints S) := by
  classical
  let pre (x : {x // x ∈ vertexPoints S}) : {x // x ∈ A} :=
    (Finset.mem_image.mp x.2).choose
  have hpre_mem (x : {x // x ∈ vertexPoints S}) : pre x ∈ S :=
    (Finset.mem_image.mp x.2).choose_spec.1
  have hpre_eq (x : {x // x ∈ vertexPoints S}) :
      (pre x : Point d) = (x : Point d) :=
    (Finset.mem_image.mp x.2).choose_spec.2
  let e : {v : {x // x ∈ A} // v ∈ S} ≃ {x // x ∈ vertexPoints S} :=
    { toFun := fun v ↦ ⟨(v.1 : Point d), by simp [vertexPoints, v.2]⟩
      invFun := fun x ↦ ⟨pre x, hpre_mem x⟩
      left_inv := by
        intro v
        apply Subtype.ext
        apply Subtype.ext
        exact hpre_eq _
      right_inv := by intro x; exact Subtype.ext (hpre_eq _) }
  let iso : (diameterGraph A).induce (↑S : Set {x // x ∈ A}) ≃g
      diameterGraph (vertexPoints S) := by
    refine { toEquiv := e, map_rel_iff' := ?_ }
    intro v w
    rfl
  rw [diameterPairCount]
  exact iso.card_edgeFinset_eq

theorem isDiameterOne_vertexPoints_of_count_pos
    {d : ℕ} {A : Finset (Point d)} (hA : IsDiameterOne A)
    (S : Finset {x // x ∈ A}) (hpos : 0 < diameterPairCount (vertexPoints S)) :
    IsDiameterOne (vertexPoints S) := by
  classical
  rw [isDiameterOne_iff]
  constructor
  · intro x hx y hy
    obtain ⟨vx, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨vy, -, rfl⟩ := Finset.mem_image.mp hy
    exact hA.dist_le vx.property vy.property
  · have hne : (diameterGraph (vertexPoints S)).edgeFinset.Nonempty := by
      rw [← Finset.card_pos]
      simpa [diameterPairCount] using hpos
    obtain ⟨e, he⟩ := hne
    revert he
    refine Sym2.inductionOn e ?_
    intro x y hxy
    rw [SimpleGraph.mem_edgeFinset] at hxy
    exact ⟨(x : Point d), x.property, (y : Point d), y.property, hxy⟩

/-- Vertices assigned to one circle by a Lenz decomposition. -/
def partVertices {p : ℕ} {A : Finset (Point (2 * p))}
    (D : EvenLenzDecomposition A) (i : Fin p) : Finset {x // x ∈ A} :=
  Finset.univ.filter fun v ↦ D.part v = i

@[simp] theorem mem_partVertices {p : ℕ} {A : Finset (Point (2 * p))}
    {D : EvenLenzDecomposition A} {i : Fin p} {v : {x // x ∈ A}} :
    v ∈ partVertices D i ↔ D.part v = i := by simp [partVertices]

theorem isOnCircle_vertexPoints_partVertices
    {p : ℕ} {A : Finset (Point (2 * p))}
    (D : EvenLenzDecomposition A) (i : Fin p) :
    LocalCircle.IsOnCircle (vertexPoints (partVertices D i))
      D.carrier.center (D.carrier.radius i) (D.carrier.plane i) := by
  refine ⟨D.carrier.plane_finrank i, D.carrier.center_mem i, ?_⟩
  intro x hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
  have hpart : D.part v = i := mem_partVertices.mp hv
  simpa [hpart] using D.mem_circle v

/-- Exact dimension-four optimization for every two-circle Lenz
configuration. -/
theorem IsEvenLenz.diameterPairCount_le_fourValue
    {A : Finset (Point 4)} (hL : IsEvenLenz (p := 2) A) (hA : IsDiameterOne A)
    (hn : 2 ≤ A.card) :
    diameterPairCount A ≤
      turanNumber 2 A.card + ceilQuot A.card 2 + fourCorrection A.card := by
  classical
  let D := hL.decomposition
  let i0 : Fin 2 := ⟨0, by omega⟩
  let i1 : Fin 2 := ⟨1, by omega⟩
  have hi01 : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    norm_num [i0, i1] at this
  have hradd := D.carrier.radius_sq_add hi01
  have hsqrt3 : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrt3sq : Real.sqrt (3 : ℝ) ^ 2 = 3 := by norm_num
  have hlarge : 1 / Real.sqrt 3 < D.carrier.radius i0 ∨
      1 / Real.sqrt 3 < D.carrier.radius i1 := by
    by_contra h
    push_neg at h
    have h0 := D.carrier.radius_nonneg i0
    have h1 := D.carrier.radius_nonneg i1
    have hinv : (0 : ℝ) < 1 / Real.sqrt 3 := by positivity
    have hinvsq : (1 / Real.sqrt (3 : ℝ)) ^ 2 = 1 / 3 := by
      rw [div_pow, one_pow, hsqrt3sq]
    have h0sq : D.carrier.radius i0 ^ 2 ≤ 1 / 3 := by nlinarith
    have h1sq : D.carrier.radius i1 ^ 2 ≤ 1 / 3 := by nlinarith
    nlinarith
  have ordered_bound (ia ib : Fin 2) (hiab : ia ≠ ib)
      (hrb : 1 / Real.sqrt 3 < D.carrier.radius ib) :
      diameterPairCount A ≤
        turanNumber 2 A.card + ceilQuot A.card 2 + fourCorrection A.card := by
    let SA := partVertices D ia
    let SB := SAᶜ
    have hcover (v : {x // x ∈ A}) : D.part v = ia ∨ D.part v = ib := by
      by_cases h : D.part v = ia
      · exact Or.inl h
      · right
        apply Fin.ext
        have hk := (D.part v).isLt
        have hia := ia.isLt
        have hib := ib.isLt
        have hval : (D.part v).val ≠ ia.val := fun hv ↦ h (Fin.ext hv)
        have hiabval : ia.val ≠ ib.val := fun hv ↦ hiab (Fin.ext hv)
        omega
    have hpartB (v : {x // x ∈ A}) (hv : v ∈ SB) : D.part v = ib := by
      rcases hcover v with h | h
      · have hvnot : v ∉ SA := Finset.mem_compl.mp (by simpa only [SB] using hv)
        exact False.elim (hvnot (mem_partVertices.mpr h))
      · exact h
    have hsum : SA.card + SB.card = A.card := by
      have hc := Finset.card_add_card_compl SA
      simpa only [SB, Fintype.card_coe] using hc
    let localA := diameterPairCount (vertexPoints SA)
    let localB := diameterPairCount (vertexPoints SB)
    have hlocalA : localA ≤ cyclicDiameterAllowance SA.card := by
      by_cases hz : localA = 0
      · simp [hz]
      · have hpos : 0 < localA := Nat.pos_of_ne_zero hz
        have hdiam := isDiameterOne_vertexPoints_of_count_pos hA SA hpos
        have hcircle := isOnCircle_vertexPoints_partVertices D ia
        by_cases heven : Even SA.card
        · have heven' : Even (vertexPoints SA).card := by simpa using heven
          have hle := LocalCircle.diameterPairCount_le_card_sub_one_of_even
            hdiam hcircle heven'
          have hmod : SA.card % 2 = 0 := Nat.even_iff.mp heven
          simpa [localA, cyclicDiameterAllowance, hmod] using hle
        · have hmod : SA.card % 2 ≠ 0 := fun h ↦ heven (Nat.even_iff.mpr h)
          simpa [localA, cyclicDiameterAllowance, hmod] using
            (LocalCircle.diameterPairCount_le_card hcircle)
    have hlocalB : localB ≤ 1 := by
      by_cases hz : localB = 0
      · simp [hz]
      · have hpos : 0 < localB := Nat.pos_of_ne_zero hz
        have hcircleB : LocalCircle.IsOnCircle (vertexPoints SB)
            D.carrier.center (D.carrier.radius ib) (D.carrier.plane ib) := by
          refine ⟨D.carrier.plane_finrank ib, D.carrier.center_mem ib, ?_⟩
          intro x hx
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
          have hpv := hpartB v hv
          have hmem := D.mem_circle v
          rw [hpv] at hmem
          exact hmem
        exact LocalCircle.diameterPairCount_le_one_of_radius_gt
          (isDiameterOne_vertexPoints_of_count_pos hA SB hpos)
          hcircleB hrb
    let crossEdges := (SA ×ˢ SB).filter fun e ↦ (diameterGraph A).Adj e.1 e.2
    have hcross : crossEdges.card ≤ SA.card * SB.card := by
      calc
        crossEdges.card ≤ (SA ×ˢ SB).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        _ = SA.card * SB.card := Finset.card_product SA SB
    have hinsideA :
        ((diameterGraph A).induce (↑SA : Set {x // x ∈ A})).edgeFinset.card = localA := by
      exact card_induce_eq_diameterPairCount_vertexPoints SA
    have hinsideB :
        ((diameterGraph A).induce (↑SB : Set {x // x ∈ A})).edgeFinset.card = localB := by
      exact card_induce_eq_diameterPairCount_vertexPoints SB
    have hdecomp0 := Stability.card_edgeFinset_decomp (diameterGraph A) SA
    have hdecomp : (diameterGraph A).edgeFinset.card =
        ((diameterGraph A).induce (↑SA : Set {x // x ∈ A})).edgeFinset.card +
          crossEdges.card +
        ((diameterGraph A).induce (↑SB : Set {x // x ∈ A})).edgeFinset.card := by
      simpa only [crossEdges, SB] using hdecomp0
    have hedge : diameterPairCount A ≤ SA.card * SB.card + localA + 1 := by
      rw [hinsideA, hinsideB] at hdecomp
      rw [diameterPairCount]
      dsimp [localA, localB] at hdecomp hlocalA hlocalB ⊢
      omega
    exact four_upper_of_carrier hn hsum hlocalA hedge
  rcases hlarge with h0 | h1
  · exact ordered_bound i1 i0 hi01.symm h0
  · exact ordered_bound i0 i1 hi01 h1

theorem card_induce_carrierVertices_le_four
    {A : Finset (Point 4)} (hA : IsDiameterOne A) (C : EvenCircleCarrier 2)
    (hnonempty : ∀ i, ∃ x ∈ A, x ∈ C.circle i) :
    ((diameterGraph A).induce
      (↑(carrierVertices (A := A) C) : Set {x // x ∈ A})).edgeFinset.card ≤
      turanNumber 2 (carrierVertices (A := A) C).card +
        ceilQuot (carrierVertices (A := A) C).card 2 +
        fourCorrection (carrierVertices (A := A) C).card := by
  rw [card_induce_carrierVertices_eq_diameterPairCount]
  rw [← card_carrierPoints_eq_card_carrierVertices C]
  apply IsEvenLenz.diameterPairCount_le_fourValue
    (isEvenLenz_carrierPoints C)
  · rw [isDiameterOne_iff]
    constructor
    · intro x hx y hy
      exact hA.dist_le (mem_carrierPoints.mp hx).1 (mem_carrierPoints.mp hy).1
    · let i0 : Fin 2 := ⟨0, by omega⟩
      let i1 : Fin 2 := ⟨1, by omega⟩
      obtain ⟨x, hxA, hxC⟩ := hnonempty i0
      obtain ⟨y, hyA, hyC⟩ := hnonempty i1
      have hij : i0 ≠ i1 := by
        intro h
        have := congrArg Fin.val h
        norm_num [i0, i1] at this
      exact ⟨x, mem_carrierPoints.mpr ⟨hxA, ⟨i0, hxC⟩⟩,
        y, mem_carrierPoints.mpr ⟨hyA, ⟨i1, hyC⟩⟩,
        C.dist_eq_one_of_mem_circle_of_ne hij hxC hyC⟩
  · let i0 : Fin 2 := ⟨0, by omega⟩
    let i1 : Fin 2 := ⟨1, by omega⟩
    obtain ⟨x, hxA, hxC⟩ := hnonempty i0
    obtain ⟨y, hyA, hyC⟩ := hnonempty i1
    have hxy : x ≠ y := by
      intro h
      subst y
      exact Set.disjoint_left.mp (C.disjoint_circle (by
        intro h; have := congrArg Fin.val h; norm_num [i0, i1] at this)) hxC hyC
    have hx : x ∈ carrierPoints A C := mem_carrierPoints.mpr ⟨hxA, ⟨i0, hxC⟩⟩
    have hy : y ∈ carrierPoints A C := mem_carrierPoints.mpr ⟨hyA, ⟨i1, hyC⟩⟩
    rw [show 2 ≤ (carrierPoints A C).card ↔ 1 < (carrierPoints A C).card by omega,
      Finset.one_lt_card_iff]
    exact ⟨x, y, hx, hy, hxy⟩

theorem card_edgeFinset_le_of_stable_core_with_inside
    {p : ℕ} (hp : 2 ≤ p) {A : Finset (Point (2 * p))} {epsilon : ℝ}
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (C : EvenCircleCarrier p)
    (hcore : ∀ (i : Fin p) (w : {x // x ∈ A}),
      w ∈ Stability.retainedFiber P.color P.exceptional i →
        (w : Point (2 * p)) ∈ C.circle i)
    (hthree : ∀ i, 3 ≤ (Stability.retainedFiber P.color P.exceptional i).card)
    (insideBound : ℕ)
    (hinside : ((diameterGraph A).induce
      (↑(carrierVertices (A := A) C) : Set {x // x ∈ A})).edgeFinset.card ≤
        insideBound) :
    let L := carrierVertices (A := A) C
    let B := Lᶜ
    ((diameterGraph A).edgeFinset.card : ℝ) ≤
      insideBound + (B.card : ℝ) *
        ((L.card : ℝ) - 2 * ((A.card : ℝ) / p - epsilon * A.card) + 4) +
        (B.card.choose 2 : ℕ) := by
  classical
  let G := diameterGraph A
  let L := carrierVertices (A := A) C
  let B := Lᶜ
  have hoff (v : {x // x ∈ A}) (hv : v ∈ B) :
      (((G.neighborFinset v ∩ L).card : ℝ)) ≤
        (L.card : ℝ) - 2 * ((A.card : ℝ) / p - epsilon * A.card) + 4 := by
    apply card_neighbors_inter_carrierVertices_le hp P C hcore hthree v
    exact Finset.mem_compl.mp hv
  let X := (L ×ˢ B).filter fun e ↦ G.Adj e.1 e.2
  have hcross : (X.card : ℝ) =
      ∑ v ∈ B, ((G.neighborFinset v ∩ L).card : ℝ) := by
    calc
      (X.card : ℝ) = ∑ x ∈ L, ∑ v ∈ B, if G.Adj x v then (1 : ℝ) else 0 := by
        simp only [X, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
          Nat.cast_one, Nat.cast_zero, Finset.sum_product]
      _ = ∑ v ∈ B, ∑ x ∈ L, if G.Adj v x then (1 : ℝ) else 0 := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun v _ ↦ Finset.sum_congr rfl fun x _ ↦ by
          simpa only [G.adj_comm]
      _ = ∑ v ∈ B, ((G.neighborFinset v ∩ L).card : ℝ) := by
        apply Finset.sum_congr rfl
        intro v hv
        have heq : G.neighborFinset v ∩ L = L.filter (G.Adj v) := by
          ext x; simp [and_comm]
        rw [heq, Finset.card_filter, Nat.cast_sum]
        simp
  have hcrossBound : (X.card : ℝ) ≤ (B.card : ℝ) *
      ((L.card : ℝ) - 2 * ((A.card : ℝ) / p - epsilon * A.card) + 4) := by
    rw [hcross]
    calc
      _ ≤ ∑ _v ∈ B,
          ((L.card : ℝ) - 2 * ((A.card : ℝ) / p - epsilon * A.card) + 4) :=
        Finset.sum_le_sum fun v hv ↦ hoff v hv
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hBinside : (G.induce (↑B : Set {x // x ∈ A})).edgeFinset.card ≤
      B.card.choose 2 := by
    simpa using (G.induce (↑B : Set {x // x ∈ A})).card_edgeFinset_le_card_choose_two
  have hdecomp := Stability.card_edgeFinset_decomp G L
  have hdecompR : (G.edgeFinset.card : ℝ) =
      (G.induce (↑L : Set {x // x ∈ A})).edgeFinset.card + X.card +
        (G.induce (↑B : Set {x // x ∈ A})).edgeFinset.card := by
    exact_mod_cast (by simpa only [X, B] using hdecomp)
  have hinsideR : ((G.induce (↑L : Set {x // x ∈ A})).edgeFinset.card : ℝ) ≤
      insideBound := by exact_mod_cast hinside
  have hBinsideR : ((G.induce (↑B : Set {x // x ∈ A})).edgeFinset.card : ℝ) ≤
      B.card.choose 2 := by exact_mod_cast hBinside
  dsimp only
  change (G.edgeFinset.card : ℝ) ≤ _
  nlinarith

theorem offCarrier_four_extra_add_one_lt_turan_gap
    {n l b : ℕ} (hsum : l + b = n) (hb : 0 < b)
    (hbsmall : (b : ℝ) < (1 / 400 : ℝ) * n) (hn : 16 ≤ n) :
    (b : ℝ) * ((l : ℝ) - 2 * ((n : ℝ) / 2 - (1 / 400 : ℝ) * n) + 4) +
        (b.choose 2 : ℕ) + 1 < (1 / 2 : ℝ) * b * l := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hsumR : (l : ℝ) + b = n := by exact_mod_cast hsum
  have hbsub : 1 ≤ b := by omega
  have hchooseNat : 2 * b.choose 2 = b * (b - 1) := by
    rw [Nat.choose_two_right, mul_comm]
    exact Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self b)
  have hchoose : (2 : ℝ) * (b.choose 2 : ℕ) = b * (b - 1) := by
    exact_mod_cast hchooseNat
  have hbsubR : ((b - 1 : ℕ) : ℝ) = b - 1 := by
    rw [Nat.cast_sub hbsub]
    norm_num
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

theorem fourValue_l_add_extra_lt_fourValue_n
    {n l b : ℕ} (hsum : l + b = n) (hb : 0 < b)
    (hbsmall : (b : ℝ) < (1 / 400 : ℝ) * n) (hn : 16 ≤ n) :
    (turanNumber 2 l + ceilQuot l 2 + fourCorrection l : ℕ) +
      ((b : ℝ) * ((l : ℝ) - 2 * ((n : ℝ) / 2 - (1 / 400 : ℝ) * n) + 4) +
        (b.choose 2 : ℕ)) < turanNumber 2 n + ceilQuot n 2 + fourCorrection n := by
  have hceil : ceilQuot l 2 ≤ ceilQuot n 2 := by unfold ceilQuot; omega
  have hlocalR : ceilQuot l 2 + fourCorrection l ≤
      ceilQuot n 2 + fourCorrection n + 1 := by
    have hl := show l ≤ n by omega
    have hcorr_l : fourCorrection l ≤ 1 := by unfold fourCorrection; split <;> omega
    omega
  have hgap := turanNumber_add_gap_real (p := 2) (by omega) l b
  rw [hsum] at hgap
  norm_num at hgap
  have hextra := offCarrier_four_extra_add_one_lt_turan_gap hsum hb hbsmall hn
  have hlocalRR : ((ceilQuot l 2 + fourCorrection l : ℕ) : ℝ) ≤
      ((ceilQuot n 2 + fourCorrection n + 1 : ℕ) : ℝ) := by exact_mod_cast hlocalR
  norm_num only [Nat.cast_add] at hlocalRR ⊢
  nlinarith

/-- Swanepoel's eventual sharp upper bound in every even dimension at least
six.  No stability or carrier hypothesis remains in the statement. -/
theorem eventually_f_even_le_turanNumber_add
    (p : ℕ) (hp : 3 ≤ p) :
    ∀ᶠ n in Filter.atTop, f (2 * p) n ≤ turanNumber p n + p := by
  classical
  let epsilon : ℝ := evenStabilityEpsilon p
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon, evenStabilityEpsilon]
    positivity
  obtain ⟨delta, hdelta, hstable⟩ :=
    Stability.eventually_exists_stablePartition_completeEquipartite_free
      p (by omega) hepsilon
  have hratio := f_ratio_tendsto (2 * p) (by omega : 4 ≤ 2 * p)
  have hclose := hratio.eventually (Metric.ball_mem_nhds _ hdelta)
  filter_upwards [hstable, hclose,
      Filter.eventually_ge_atTop (1000 * p ^ 3)] with n hstable_n hclose_n hn
  have hn2 : 2 ≤ n := by
    have hp0 : 0 < p := by omega
    have hpow : 0 < p ^ 3 := pow_pos hp0 3
    have hbase : 2 ≤ 1000 * p ^ 3 := by omega
    exact hbase.trans hn
  obtain ⟨A, hAcard, hA, hcount⟩ :=
    exists_diameterPairCount_eq_f (2 * p) n (by omega) (by omega)
  let G := diameterGraph A
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnSq : (0 : ℝ) < (n : ℝ) ^ 2 := sq_pos_of_pos hnR
  have hclose' :
      |(f (2 * p) n : ℝ) / (n : ℝ) ^ 2 -
          (((p : ℝ) - 1) / (2 * p))| < delta := by
    have hm := Metric.mem_ball.mp hclose_n
    rw [Real.dist_eq] at hm
    have hhalf : 2 * p / 2 = p := by omega
    simpa only [hhalf] using hm
  have hratioLower :
      (((p : ℝ) - 1) / (2 * p) - delta) <
        (f (2 * p) n : ℝ) / (n : ℝ) ^ 2 := by
    have := (abs_lt.mp hclose').1
    linarith
  have hnearF :
      (((p : ℝ) - 1) / (2 * p) - delta) * (n : ℝ) ^ 2 ≤
        (f (2 * p) n : ℝ) :=
    ((lt_div_iff₀ hnSq).mp hratioLower).le
  have hfree : (completeEquipartiteGraph (p + 1) 3).Free G := by
    have hf := diameterGraph_completeEquipartiteGraph_free
      (d := 2 * p) (by omega : 4 ≤ 2 * p) A
    rw [show 2 * p / 2 = p by omega] at hf
    exact hf
  have hcardV : Fintype.card {x // x ∈ A} = n := by simpa [hAcard]
  have hnearG :
      (((p : ℝ) - 1) / (2 * p) - delta) * (n : ℝ) ^ 2 ≤
        (G.edgeFinset.card : ℝ) := by
    rw [← hcount] at hnearF
    simpa only [G, diameterPairCount] using hnearF
  obtain ⟨P⟩ := hstable_n {x // x ∈ A} hcardV G hfree hnearG
  have hsize (i : Fin p) :
      (((p * 4 : ℕ) : ℝ) * (epsilon * A.card) + 4 ≤
        (Stability.retainedFiber P.color P.exceptional i).card) := by
    have hbal := (abs_lt.mp (P.balanced i)).1
    have hcardSubtype : Fintype.card {x // x ∈ A} = A.card := by simp
    rw [hcardSubtype, hAcard] at hbal
    rw [hAcard]
    have hnum : (((p * 4 : ℕ) : ℝ) * (epsilon * n) + 4) ≤
        (n : ℝ) / p - epsilon * n := by
      have hpR : (0 : ℝ) < p := by positivity
      have hnLarge : (1000 : ℝ) * (p : ℝ) ^ 3 ≤ n := by exact_mod_cast hn
      have hpPowNat : p ^ 2 ≤ p ^ 3 := by
        calc
          p ^ 2 ≤ p ^ 2 * p := Nat.le_mul_of_pos_right _ (by omega)
          _ = p ^ 3 := by ring
      have h400Nat : 400 * p ^ 2 ≤ n := by
        apply le_trans (b := 1000 * p ^ 3)
        · calc
            400 * p ^ 2 ≤ 1000 * p ^ 2 := Nat.mul_le_mul_right _ (by omega)
            _ ≤ 1000 * p ^ 3 := Nat.mul_le_mul_left _ hpPowNat
        · exact hn
      have h400 : (400 : ℝ) * (p : ℝ) ^ 2 ≤ n := by exact_mod_cast h400Nat
      dsimp [epsilon, evenStabilityEpsilon]
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      field_simp
      have hcoef : (400 : ℝ) * (p : ℝ) ^ 2 ≤
          (96 * (p : ℝ) - 1) * n := by
        calc
          (400 : ℝ) * (p : ℝ) ^ 2 ≤ n := h400
          _ ≤ (96 * (p : ℝ) - 1) * n := by
            have : (1 : ℝ) ≤ 96 * p - 1 := by
              have hpge : (3 : ℝ) ≤ p := by exact_mod_cast hp
              linarith
            exact le_mul_of_one_le_left hnR.le this
      nlinarith [hcoef]
    have hbal' : (n : ℝ) / p - epsilon * n ≤
        (Stability.retainedFiber P.color P.exceptional i).card := by
      linarith
    exact hnum.trans hbal'
  obtain ⟨C, hcore⟩ := P.exists_evenCircleCarrier_core (by omega) hepsilon.le hsize
  have hthree (i : Fin p) :
      3 ≤ (Stability.retainedFiber P.color P.exceptional i).card := by
    have hs := hsize i
    have hnonneg : 0 ≤ (((p * 4 : ℕ) : ℝ) * (epsilon * A.card)) := by positivity
    have hcast : (3 : ℝ) ≤
        (Stability.retainedFiber P.color P.exceptional i).card := by
      nlinarith
    exact_mod_cast hcast
  let L := carrierVertices (A := A) C
  let B := Lᶜ
  have hcardSubtype : Fintype.card {x // x ∈ A} = A.card := by simp
  by_cases hB : B.Nonempty
  · have hBpos : 0 < B.card := Finset.card_pos.mpr hB
    have hBsubset : B ⊆ P.exceptional := by
      intro v hv
      by_contra hv0
      have hvret : v ∈ Stability.retainedFiber P.color P.exceptional (P.color v) :=
        Stability.mem_retainedFiber P.color P.exceptional (P.color v) v |>.mpr
          ⟨rfl, hv0⟩
      have hvL : v ∈ L := by
        exact mem_carrierVertices.mpr ⟨P.color v, hcore (P.color v) v hvret⟩
      exact (Finset.mem_compl.mp (by simpa only [B] using hv)) hvL
    have hBsmallNat : B.card ≤ P.exceptional.card :=
      Finset.card_le_card hBsubset
    have hBsmall : (B.card : ℝ) < epsilon * n := by
      have hcast : (B.card : ℝ) ≤ P.exceptional.card := by exact_mod_cast hBsmallNat
      have hex := P.exceptional_small
      rw [hcardSubtype, hAcard] at hex
      exact hcast.trans_lt hex
    have hsum : L.card + B.card = n := by
      have hc := Finset.card_compl_add_card L
      rw [hAcard] at hcardSubtype
      simpa [B, hcardSubtype, add_comm] using hc
    have hlargeNum :
        5 * (p : ℝ) * epsilon * n + 7 * p < 2 * n := by
      have hpR : (0 : ℝ) < p := by positivity
      have hpge : (3 : ℝ) ≤ p := by exact_mod_cast hp
      have hepsTerm : 5 * (p : ℝ) * epsilon * n ≤ n := by
        dsimp [epsilon, evenStabilityEpsilon]
        field_simp
        nlinarith [sq_pos_of_pos hpR, hnR.le, hpge]
      have h7Nat : 7 * p < n := by
        apply lt_of_lt_of_le (b := 1000 * p ^ 3) _ hn
        have hpPowNat : p ≤ p ^ 3 := by
          calc
            p ≤ p * p := Nat.le_mul_of_pos_right _ (by omega : 0 < p)
            _ = p ^ 2 := by ring
            _ ≤ p ^ 2 * p := Nat.le_mul_of_pos_right _ (by omega : 0 < p)
            _ = p ^ 3 := by ring
        calc
          7 * p < 1000 * p := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
          _ ≤ 1000 * p ^ 3 := Nat.mul_le_mul_left _ hpPowNat
      have h7 : (7 : ℝ) * p < n := by exact_mod_cast h7Nat
      nlinarith
    have hextra := offCarrier_extra_lt_turan_gap hp hsum hBpos hepsilon.le
      hBsmall hlargeNum
    have hedge := card_edgeFinset_le_of_stable_core hp hA P C hcore hthree
    have hedge' : (G.edgeFinset.card : ℝ) ≤
        turanNumber p L.card + p +
          (B.card : ℝ) *
            ((L.card : ℝ) - 2 * ((n : ℝ) / p - epsilon * n) + 4) +
          (B.card.choose 2 : ℕ) := by
      simpa only [G, L, B, hAcard] using hedge
    have hgap := turanNumber_add_gap_real (by omega : 0 < p) L.card B.card
    rw [hsum] at hgap
    have hstrict : (G.edgeFinset.card : ℝ) < turanNumber p n + p := by
      nlinarith [hedge']
    have hlower : turanNumber p n + p ≤ f (2 * p) n := by
      have heven : Even (2 * p) := ⟨p, by omega⟩
      have hhalf : 2 * p / 2 = p := by omega
      have hpPowNat : p ≤ p ^ 3 := by
        calc
          p ≤ p * p := Nat.le_mul_of_pos_right _ (by omega : 0 < p)
          _ = p ^ 2 := by ring
          _ ≤ p ^ 2 * p := Nat.le_mul_of_pos_right _ (by omega : 0 < p)
          _ = p ^ 3 := by ring
      have hnLower : 2 * (2 * p / 2) ≤ n := by
        rw [hhalf]
        exact (calc
          2 * p ≤ 1000 * p := Nat.mul_le_mul_right p (by omega)
          _ ≤ 1000 * p ^ 3 := Nat.mul_le_mul_left _ hpPowNat
          _ ≤ n := hn)
      simpa using ExactLower.even_exact_lower
        (d := 2 * p) (n := n) (by omega : 6 ≤ 2 * p) heven hnLower
    have hcountG : G.edgeFinset.card = f (2 * p) n := by
      simpa [G, diameterPairCount] using hcount
    rw [hcountG] at hstrict
    exact False.elim ((not_lt_of_ge (by exact_mod_cast hlower)) hstrict)
  · have hBempty : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    have hLuniv : L = Finset.univ := by
      apply (Finset.compl_eq_empty_iff L).mp
      simpa only [B] using hBempty
    have hLenz : IsEvenLenz A := by
      refine ⟨C, ?_⟩
      intro x hx
      let v : {x // x ∈ A} := ⟨x, hx⟩
      have hvL : v ∈ L := by rw [hLuniv]; simp
      exact mem_carrierVertices.mp hvL
    have hu := hLenz.diameterPairCount_le_turanNumber_add hp hA
    rw [hAcard, hcount] at hu
    exact hu

/-- Swanepoel's eventual sharp upper bound in the exceptional even
dimension four.  The two carrier circles may have unequal radii, so the
linear term and its residue-class correction are retained explicitly. -/
theorem eventually_f_four_le_exactValue :
    ∀ᶠ n in Filter.atTop,
      f 4 n ≤ turanNumber 2 n + ceilQuot n 2 + fourCorrection n := by
  classical
  let epsilon : ℝ := evenStabilityEpsilon 2
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon, evenStabilityEpsilon]
    norm_num
  obtain ⟨delta, hdelta, hstable⟩ :=
    Stability.eventually_exists_stablePartition_completeEquipartite_free
      2 (by omega) hepsilon
  have hratio := f_ratio_tendsto 4 (by omega)
  have hclose := hratio.eventually (Metric.ball_mem_nhds _ hdelta)
  filter_upwards [hstable, hclose, Filter.eventually_ge_atTop 8000] with
      n hstable_n hclose_n hn
  have hn2 : 2 ≤ n := by omega
  have hn8 : 8 ≤ n := by omega
  have hn16 : 16 ≤ n := by omega
  obtain ⟨A, hAcard, hA, hcount⟩ :=
    exists_diameterPairCount_eq_f 4 n (by omega) hn2
  let G := diameterGraph A
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnSq : (0 : ℝ) < (n : ℝ) ^ 2 := sq_pos_of_pos hnR
  have hclose' :
      |(f 4 n : ℝ) / (n : ℝ) ^ 2 -
          (((2 : ℝ) - 1) / (2 * 2))| < delta := by
    have hm := Metric.mem_ball.mp hclose_n
    rw [Real.dist_eq] at hm
    norm_num at hm ⊢
    exact hm
  have hratioLower :
      (((2 : ℝ) - 1) / (2 * 2) - delta) <
        (f 4 n : ℝ) / (n : ℝ) ^ 2 := by
    have := (abs_lt.mp hclose').1
    linarith
  have hnearF :
      (((2 : ℝ) - 1) / (2 * 2) - delta) * (n : ℝ) ^ 2 ≤
        (f 4 n : ℝ) :=
    ((lt_div_iff₀ hnSq).mp hratioLower).le
  have hfree : (completeEquipartiteGraph 3 3).Free G := by
    simpa using (diameterGraph_completeEquipartiteGraph_free
      (d := 4) (by omega) A)
  have hcardV : Fintype.card {x // x ∈ A} = n := by simpa [hAcard]
  have hnearG :
      (((2 : ℝ) - 1) / (2 * 2) - delta) * (n : ℝ) ^ 2 ≤
        (G.edgeFinset.card : ℝ) := by
    rw [← hcount] at hnearF
    simpa only [G, diameterPairCount] using hnearF
  obtain ⟨P⟩ := hstable_n {x // x ∈ A} hcardV G hfree hnearG
  have hsize (i : Fin 2) :
      (((2 * 4 : ℕ) : ℝ) * (epsilon * A.card) + 4 ≤
        (Stability.retainedFiber P.color P.exceptional i).card) := by
    have hbal := (abs_lt.mp (P.balanced i)).1
    have hcardSubtype : Fintype.card {x // x ∈ A} = A.card := by simp
    rw [hcardSubtype, hAcard] at hbal
    rw [hAcard]
    have hnum : (((2 * 4 : ℕ) : ℝ) * (epsilon * n) + 4) ≤
        (n : ℝ) / 2 - epsilon * n := by
      have hnLarge : (16 : ℝ) ≤ n := by exact_mod_cast hn16
      dsimp [epsilon, evenStabilityEpsilon]
      norm_num
      nlinarith
    have hbal' : (n : ℝ) / 2 - epsilon * n ≤
        (Stability.retainedFiber P.color P.exceptional i).card := by
      linarith
    exact hnum.trans hbal'
  obtain ⟨C, hcore⟩ := P.exists_evenCircleCarrier_core
    (p := 2) (by omega) hepsilon.le hsize
  have hthree (i : Fin 2) :
      3 ≤ (Stability.retainedFiber P.color P.exceptional i).card := by
    have hs := hsize i
    have hnonneg : 0 ≤ (((2 * 4 : ℕ) : ℝ) * (epsilon * A.card)) := by
      positivity
    have hcast : (3 : ℝ) ≤
        (Stability.retainedFiber P.color P.exceptional i).card := by
      nlinarith
    exact_mod_cast hcast
  have hnonempty (i : Fin 2) : ∃ x ∈ A, x ∈ C.circle i := by
    have hpos : 0 < (Stability.retainedFiber P.color P.exceptional i).card := by
      have hi := hthree i
      omega
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
    exact ⟨v, v.property, hcore i v hv⟩
  let L := carrierVertices (A := A) C
  let B := Lᶜ
  have hcardSubtype : Fintype.card {x // x ∈ A} = A.card := by simp
  by_cases hB : B.Nonempty
  · have hBpos : 0 < B.card := Finset.card_pos.mpr hB
    have hBsubset : B ⊆ P.exceptional := by
      intro v hv
      by_contra hv0
      have hvret : v ∈ Stability.retainedFiber P.color P.exceptional (P.color v) :=
        Stability.mem_retainedFiber P.color P.exceptional (P.color v) v |>.mpr
          ⟨rfl, hv0⟩
      have hvL : v ∈ L :=
        mem_carrierVertices.mpr ⟨P.color v, hcore (P.color v) v hvret⟩
      exact (Finset.mem_compl.mp (by simpa only [B] using hv)) hvL
    have hBsmallNat : B.card ≤ P.exceptional.card :=
      Finset.card_le_card hBsubset
    have hBsmall : (B.card : ℝ) < epsilon * n := by
      have hcast : (B.card : ℝ) ≤ P.exceptional.card := by
        exact_mod_cast hBsmallNat
      have hex := P.exceptional_small
      rw [hcardSubtype, hAcard] at hex
      exact hcast.trans_lt hex
    have hBsmall400 : (B.card : ℝ) < (1 / 400 : ℝ) * n := by
      norm_num [epsilon, evenStabilityEpsilon] at hBsmall ⊢
      exact hBsmall
    have hsum : L.card + B.card = n := by
      have hc := Finset.card_compl_add_card L
      rw [hAcard] at hcardSubtype
      simpa [B, hcardSubtype, add_comm] using hc
    have hinside := card_induce_carrierVertices_le_four hA C hnonempty
    have hedge := card_edgeFinset_le_of_stable_core_with_inside
      (p := 2) (by omega) P C hcore hthree
      (turanNumber 2 L.card + ceilQuot L.card 2 + fourCorrection L.card)
      (by simpa only [L] using hinside)
    have hedge' : (G.edgeFinset.card : ℝ) ≤
        (turanNumber 2 L.card + ceilQuot L.card 2 + fourCorrection L.card : ℕ) +
          (B.card : ℝ) *
            ((L.card : ℝ) - 2 * ((n : ℝ) / 2 - (1 / 400 : ℝ) * n) + 4) +
          (B.card.choose 2 : ℕ) := by
      have heps : epsilon = (1 / 400 : ℝ) := by
        norm_num [epsilon, evenStabilityEpsilon]
      rw [heps] at hedge
      simpa only [G, L, B, hAcard, Nat.cast_ofNat] using hedge
    have hgap := fourValue_l_add_extra_lt_fourValue_n hsum hBpos hBsmall400 hn16
    have hstrict : (G.edgeFinset.card : ℝ) <
        turanNumber 2 n + ceilQuot n 2 + fourCorrection n :=
      by nlinarith [hedge', hgap]
    have hlower :
        turanNumber 2 n + ceilQuot n 2 + fourCorrection n ≤ f 4 n :=
      ExactLower.four_exact_lower hn8
    have hcountG : G.edgeFinset.card = f 4 n := by
      simpa [G, diameterPairCount] using hcount
    rw [hcountG] at hstrict
    exact False.elim ((not_lt_of_ge (by exact_mod_cast hlower)) hstrict)
  · have hBempty : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    have hLuniv : L = Finset.univ := by
      apply (Finset.compl_eq_empty_iff L).mp
      simpa only [B] using hBempty
    have hLenz : IsEvenLenz (p := 2) A := by
      refine ⟨C, ?_⟩
      intro x hx
      let v : {x // x ∈ A} := ⟨x, hx⟩
      have hvL : v ∈ L := by rw [hLuniv]; simp
      exact mem_carrierVertices.mp hvL
    have hu := IsEvenLenz.diameterPairCount_le_fourValue hLenz hA (by
      rw [hAcard]
      exact hn2)
    rw [hAcard, hcount] at hu
    exact hu

end EvenExceptionalRemoval

end

end Erdos223
