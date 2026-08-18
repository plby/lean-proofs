/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.AxisBoxes
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# A comparable enclosing box from a maximal simplex

This file proves the finite maximal-simplex normalization used in the
Pham--Zakharov density-increment argument.  If a finite set in `d`-dimensional
Euclidean space contains a nondegenerate `(d+1)`-tuple, choose such a tuple
with maximal absolute determinant.  Coordinates in the resulting affine
frame put every point of the finite set in `[-1,1]^d`: replacing the `i`th
non-base vertex by the point shows that the absolute value of its `i`th
coordinate is at most one.

The convex hull contains the smaller cube `[0,1/(d+1)]^d`, since every point
of that cube is a convex combination of the selected vertices.  Consequently
the containing cube has volume at most `(2*(d+1))^d` times the volume of the
normalized convex hull.  This slightly larger constant avoids any dependence
on a simplex-volume formula and is uniform in the finite set.
-/

open Set MeasureTheory Module
open scoped BigOperators ENNReal Pointwise

namespace Erdos186.PZ.ConvexDensity

noncomputable section

/-- The edge vectors of an ordered `(d+1)`-tuple, based at vertex zero. -/
def simplexFrame {d : ℕ} (p : Fin (d + 1) → EuclideanPoint d) :
    Fin d → EuclideanPoint d :=
  fun i ↦ p i.succ - p 0

/-- Determinant of the edge frame, in the standard orthonormal basis. -/
def simplexDet {d : ℕ} (p : Fin (d + 1) → EuclideanPoint d) : ℝ :=
  (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.det (simplexFrame p)

/-- A finite collection of tuples has a maximal absolute simplex determinant.
The nonzero conclusion is retained when a nondegenerate candidate is supplied. -/
theorem exists_maximal_simplex {d : ℕ} (X : Finset (EuclideanPoint d))
    {p₀ : Fin (d + 1) → EuclideanPoint d}
    (hp₀X : ∀ i, p₀ i ∈ X) (hp₀ : simplexDet p₀ ≠ 0) :
    ∃ p : Fin (d + 1) → EuclideanPoint d,
      (∀ i, p i ∈ X) ∧ simplexDet p ≠ 0 ∧
        ∀ q : Fin (d + 1) → EuclideanPoint d,
          (∀ i, q i ∈ X) → |simplexDet q| ≤ |simplexDet p| := by
  classical
  let p₀' : Fin (d + 1) → {x // x ∈ X} := fun i ↦ ⟨p₀ i, hp₀X i⟩
  obtain ⟨p', -, hp'max⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin (d + 1) → {x // x ∈ X}))
      (fun q ↦ |simplexDet (fun i ↦ (q i : EuclideanPoint d))|)
      ⟨p₀', Finset.mem_univ _⟩
  let p : Fin (d + 1) → EuclideanPoint d := fun i ↦ p' i
  refine ⟨p, fun i ↦ (p' i).property, ?_, ?_⟩
  · intro hpzero
    have hle := hp'max p₀' (Finset.mem_univ _)
    simp only [p, p₀', hpzero, abs_zero] at hle
    exact hp₀ (abs_eq_zero.mp (le_antisymm hle (abs_nonneg _)))
  · intro q hqX
    let q' : Fin (d + 1) → {x // x ∈ X} := fun i ↦ ⟨q i, hqX i⟩
    simpa only [p, q'] using hp'max q' (Finset.mem_univ _)

/-- The linear basis carried by a nondegenerate simplex frame. -/
def simplexBasis {d : ℕ} (p : Fin (d + 1) → EuclideanPoint d)
    (hp : simplexDet p ≠ 0) : Basis (Fin d) ℝ (EuclideanPoint d) := by
  let e := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
  have hu : IsUnit (e.det (simplexFrame p)) := isUnit_iff_ne_zero.mpr hp
  have hv := (e.is_basis_iff_det).mpr hu
  exact Basis.mk hv.1 hv.2.ge

@[simp]
theorem simplexBasis_apply {d : ℕ} (p : Fin (d + 1) → EuclideanPoint d)
    (hp : simplexDet p ≠ 0) (i : Fin d) :
    simplexBasis p hp i = p i.succ - p 0 := by
  simp [simplexBasis, simplexFrame]

/-- Affine coordinates based at vertex zero of a nondegenerate simplex. -/
def simplexAffineEquiv {d : ℕ} (p : Fin (d + 1) → EuclideanPoint d)
    (hp : simplexDet p ≠ 0) : EuclideanPoint d ≃ᵃ[ℝ] EuclideanPoint d :=
  (AffineEquiv.constVAdd ℝ (EuclideanPoint d) (-p 0)).trans
    ((simplexBasis p hp).equiv
      (EuclideanSpace.basisFun (Fin d) ℝ).toBasis (Equiv.refl (Fin d))).toAffineEquiv

@[simp]
theorem simplexAffineEquiv_base {d : ℕ}
    (p : Fin (d + 1) → EuclideanPoint d) (hp : simplexDet p ≠ 0) :
    simplexAffineEquiv p hp (p 0) = 0 := by
  simp [simplexAffineEquiv]

@[simp]
theorem simplexAffineEquiv_vertex {d : ℕ}
    (p : Fin (d + 1) → EuclideanPoint d) (hp : simplexDet p ≠ 0)
    (i : Fin d) :
    simplexAffineEquiv p hp (p i.succ) =
      (EuclideanSpace.basisFun (Fin d) ℝ).toBasis i := by
  let L := (simplexBasis p hp).equiv
    (EuclideanSpace.basisFun (Fin d) ℝ).toBasis (Equiv.refl (Fin d))
  change L (-p 0 + p i.succ) = _
  rw [add_comm, ← sub_eq_add_neg, ← simplexBasis_apply p hp i]
  exact Module.Basis.equiv_apply _ _ _ _

/-- In simplex coordinates, the `i`th coordinate is the corresponding dual
basis coordinate of the displacement from the base vertex. -/
theorem simplexAffineEquiv_apply_coord {d : ℕ}
    (p : Fin (d + 1) → EuclideanPoint d) (hp : simplexDet p ≠ 0)
    (x : EuclideanPoint d) (i : Fin d) :
    simplexAffineEquiv p hp x i = (simplexBasis p hp).coord i (x - p 0) := by
  let b := simplexBasis p hp
  let e := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
  let L := b.equiv e (Equiv.refl (Fin d))
  change (L (-p 0 + x)) i = b.coord i (x - p 0)
  rw [add_comm, ← sub_eq_add_neg]
  change e.repr (L (x - p 0)) i = b.repr (x - p 0) i
  simp [L, Module.Basis.equiv]

/-- Replacing a non-base vertex replaces exactly the corresponding frame
column. -/
theorem simplexFrame_update_succ {d : ℕ}
    (p : Fin (d + 1) → EuclideanPoint d) (i : Fin d)
    (x : EuclideanPoint d) :
    simplexFrame (Function.update p i.succ x) =
      Function.update (simplexFrame p) i (x - p 0) := by
  funext j
  by_cases hji : j = i
  · subst j
    have hi0 : i.succ ≠ (0 : Fin (d + 1)) := Fin.succ_ne_zero i
    simp only [simplexFrame, Function.update_self]
    rw [Function.update_of_ne hi0.symm]
  · have hsji : j.succ ≠ i.succ := fun h ↦ hji (Fin.succ_injective d h)
    have hi0 : i.succ ≠ (0 : Fin (d + 1)) := Fin.succ_ne_zero i
    simp only [simplexFrame]
    rw [Function.update_of_ne hsji, Function.update_of_ne hi0.symm,
      Function.update_of_ne hji]
    rfl

/-- Cramer's rule in the exact form needed for maximal-simplex coordinates. -/
theorem simplexDet_update_succ {d : ℕ}
    (p : Fin (d + 1) → EuclideanPoint d) (hp : simplexDet p ≠ 0)
    (i : Fin d) (x : EuclideanPoint d) :
    simplexDet (Function.update p i.succ x) =
      simplexDet p * simplexAffineEquiv p hp x i := by
  let e := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
  let b := simplexBasis p hp
  have hcramer := e.det_smul_mk_coord_eq_det_update
    b.linearIndependent b.span_eq.ge i
  have hbmk : Basis.mk b.linearIndependent b.span_eq.ge = b := by
    apply DFunLike.coe_injective
    funext j
    simp
  have hbfun : (b : Fin d → EuclideanPoint d) = simplexFrame p := by
    funext j
    exact simplexBasis_apply p hp j
  rw [hbmk] at hcramer
  have happ := LinearMap.congr_fun hcramer (x - p 0)
  rw [hbfun] at happ
  dsimp only [e] at happ
  change (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.det (simplexFrame p) *
      (simplexBasis p hp).coord i (x - p 0) =
    (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.det
      (Function.update (simplexFrame p) i (x - p 0)) at happ
  rw [simplexAffineEquiv_apply_coord]
  rw [simplexDet, simplexFrame_update_succ]
  exact happ.symm

/-- Maximality of the simplex determinant puts the finite set in the unit
coordinate cube. -/
theorem subset_unitCube_of_maximal_simplex {d : ℕ}
    {X : Finset (EuclideanPoint d)} {p : Fin (d + 1) → EuclideanPoint d}
    (hpX : ∀ i, p i ∈ X) (hp : simplexDet p ≠ 0)
    (hmax : ∀ q : Fin (d + 1) → EuclideanPoint d,
      (∀ i, q i ∈ X) → |simplexDet q| ≤ |simplexDet p|) :
    simplexAffineEquiv p hp '' (X : Set (EuclideanPoint d)) ⊆
      closedAxisBox (fun _ ↦ -1) (fun _ ↦ 1) := by
  rintro y ⟨x, hxX, rfl⟩ i
  let q := Function.update p i.succ x
  have hqX : ∀ j, q j ∈ X := by
    intro j
    by_cases hj : j = i.succ
    · subst j
      simpa [q] using hxX
    · simpa [q, hj] using hpX j
  have hle := hmax q hqX
  rw [simplexDet_update_succ p hp i x, abs_mul] at hle
  have hdetpos : 0 < |simplexDet p| := abs_pos.mpr hp
  have hcoord : |simplexAffineEquiv p hp x i| ≤ 1 := by
    nlinarith
  exact abs_le.mp hcoord

/-- The fixed outer cube used after simplex normalization. -/
def normalizedOuterCube (d : ℕ) : Set (EuclideanPoint d) :=
  closedAxisBox (fun _ ↦ -1) (fun _ ↦ 1)

/-- A small cube contained in the standard simplex.  The side `1/(d+1)`
works uniformly, including in dimension zero. -/
def normalizedInnerCube (d : ℕ) : Set (EuclideanPoint d) :=
  closedAxisBox (fun _ ↦ 0) (fun _ ↦ ((d + 1 : ℕ) : ℝ)⁻¹)

/-- The small normalized cube is contained in the convex hull of the selected
maximal-simplex vertices. -/
theorem normalizedInnerCube_subset_image_convexHull {d : ℕ}
    {X : Finset (EuclideanPoint d)} {p : Fin (d + 1) → EuclideanPoint d}
    (hpX : ∀ i, p i ∈ X) (hp : simplexDet p ≠ 0) :
    normalizedInnerCube d ⊆
      simplexAffineEquiv p hp '' convexHull ℝ (X : Set (EuclideanPoint d)) := by
  classical
  intro y hy
  have hycoord : ∀ i, 0 ≤ y i ∧ y i ≤ ((d + 1 : ℕ) : ℝ)⁻¹ := hy
  have hsum_upper : ∑ i, y i ≤ (d : ℝ) * ((d + 1 : ℕ) : ℝ)⁻¹ := by
    calc
      ∑ i, y i ≤ ∑ _i : Fin d, ((d + 1 : ℕ) : ℝ)⁻¹ :=
        Finset.sum_le_sum fun i _ ↦ (hycoord i).2
      _ = (d : ℝ) * ((d + 1 : ℕ) : ℝ)⁻¹ := by simp
  have hcastpos : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by positivity
  have hfrac : (d : ℝ) * ((d + 1 : ℕ) : ℝ)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hcastpos]
    norm_num
  have hsum : ∑ i, y i ≤ 1 := hsum_upper.trans hfrac
  let w : Fin (d + 1) → ℝ := Fin.cons (1 - ∑ i, y i) y
  have hw_nonneg : ∀ i, 0 ≤ w i := by
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa [w] using sub_nonneg.mpr hsum
    · simpa [w] using (hycoord j).1
  have hw_sum : ∑ i, w i = 1 := by
    simp [w, Fin.sum_univ_succ]
  let z : Fin (d + 1) → EuclideanPoint d := fun i ↦ simplexAffineEquiv p hp (p i)
  have hz : ∀ i, z i ∈ simplexAffineEquiv p hp '' (X : Set (EuclideanPoint d)) := by
    intro i
    exact ⟨p i, hpX i, rfl⟩
  have hcenter : Finset.univ.centerMass w z = y := by
    rw [Finset.centerMass_eq_of_sum_1 _ _ (by simpa using hw_sum)]
    rw [Fin.sum_univ_succ]
    simp only [w, z, Fin.cons_zero, Fin.cons_succ, simplexAffineEquiv_base,
      simplexAffineEquiv_vertex, smul_zero, zero_add]
    ext j
    simp [EuclideanSpace.basisFun_apply, Pi.single_apply]
  have hyhull : y ∈ convexHull ℝ
      (simplexAffineEquiv p hp '' (X : Set (EuclideanPoint d))) := by
    rw [← hcenter]
    exact Finset.univ.centerMass_mem_convexHull
      (fun i _ ↦ hw_nonneg i) (hw_sum.symm ▸ zero_lt_one)
      (fun i _ ↦ hz i)
  have himage : simplexAffineEquiv p hp '' convexHull ℝ (X : Set (EuclideanPoint d)) =
      convexHull ℝ (simplexAffineEquiv p hp '' (X : Set (EuclideanPoint d))) := by
    exact (simplexAffineEquiv p hp).toAffineMap.image_convexHull _
  rw [himage]
  exact hyhull

/-- The determinant-maximality bound extends from the finite set to its
convex hull. -/
theorem image_convexHull_subset_normalizedOuterCube {d : ℕ}
    {X : Finset (EuclideanPoint d)} {p : Fin (d + 1) → EuclideanPoint d}
    (hpX : ∀ i, p i ∈ X) (hp : simplexDet p ≠ 0)
    (hmax : ∀ q : Fin (d + 1) → EuclideanPoint d,
      (∀ i, q i ∈ X) → |simplexDet q| ≤ |simplexDet p|) :
    simplexAffineEquiv p hp '' convexHull ℝ (X : Set (EuclideanPoint d)) ⊆
      normalizedOuterCube d := by
  have himage : simplexAffineEquiv p hp '' convexHull ℝ (X : Set (EuclideanPoint d)) =
      convexHull ℝ (simplexAffineEquiv p hp '' (X : Set (EuclideanPoint d))) := by
    exact (simplexAffineEquiv p hp).toAffineMap.image_convexHull _
  rw [himage]
  exact convexHull_min (subset_unitCube_of_maximal_simplex hpX hp hmax)
    (convex_closedAxisBox _ _)

theorem volume_normalizedOuterCube (d : ℕ) :
    volume (normalizedOuterCube d) = ∏ _i : Fin d, (2 : ℝ≥0∞) := by
  rw [normalizedOuterCube, volume_closedAxisBox]
  congr 1
  funext i
  norm_num

theorem volume_normalizedInnerCube (d : ℕ) :
    volume (normalizedInnerCube d) =
      ∏ _i : Fin d, ENNReal.ofReal (((d + 1 : ℕ) : ℝ)⁻¹) := by
  rw [normalizedInnerCube, volume_closedAxisBox]
  congr 1
  funext i
  simp

theorem volume_normalizedInnerCube_ne_zero (d : ℕ) :
    volume (normalizedInnerCube d) ≠ 0 := by
  rw [volume_normalizedInnerCube]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'

theorem volume_normalizedInnerCube_ne_top (d : ℕ) :
    volume (normalizedInnerCube d) ≠ ∞ := by
  exact volume_closedAxisBox_ne_top _ _

def normalizedBoxConstant (d : ℕ) : ℝ≥0∞ :=
  volume (normalizedOuterCube d) / volume (normalizedInnerCube d)

theorem normalizedOuterCube_volume_le_image_convexHull {d : ℕ}
    {X : Finset (EuclideanPoint d)} {p : Fin (d + 1) → EuclideanPoint d}
    (hpX : ∀ i, p i ∈ X) (hp : simplexDet p ≠ 0) :
    volume (normalizedOuterCube d) ≤
      normalizedBoxConstant d * volume (simplexAffineEquiv p hp ''
        convexHull ℝ (X : Set (EuclideanPoint d))) := by
  have hsmall : volume (normalizedInnerCube d) ≤
      volume (simplexAffineEquiv p hp '' convexHull ℝ (X : Set (EuclideanPoint d))) :=
    measure_mono (normalizedInnerCube_subset_image_convexHull hpX hp)
  calc
    volume (normalizedOuterCube d) =
        normalizedBoxConstant d * volume (normalizedInnerCube d) := by
      symm
      exact ENNReal.div_mul_cancel (volume_normalizedInnerCube_ne_zero d)
        (volume_normalizedInnerCube_ne_top d)
    _ ≤ normalizedBoxConstant d *
        volume (simplexAffineEquiv p hp '' convexHull ℝ (X : Set (EuclideanPoint d))) :=
      by gcongr

theorem exists_comparable_enclosing_box_of_nonzero_simplex {d : ℕ}
    (X : Finset (EuclideanPoint d)) {p₀ : Fin (d + 1) → EuclideanPoint d}
    (hp₀X : ∀ i, p₀ i ∈ X) (hp₀ : simplexDet p₀ ≠ 0) :
    ∃ (p : Fin (d + 1) → EuclideanPoint d) (hp : simplexDet p ≠ 0)
      (e : EuclideanPoint d ≃ᵃ[ℝ] EuclideanPoint d),
      (∀ i, p i ∈ X) ∧ e = simplexAffineEquiv p hp ∧
      normalizedInnerCube d ⊆ e '' convexHull ℝ (X : Set (EuclideanPoint d)) ∧
      e '' convexHull ℝ (X : Set (EuclideanPoint d)) ⊆ normalizedOuterCube d ∧
      volume (normalizedOuterCube d) ≤ normalizedBoxConstant d *
        volume (e '' convexHull ℝ (X : Set (EuclideanPoint d))) := by
  obtain ⟨p, hpX, hp, hmax⟩ := exists_maximal_simplex X hp₀X hp₀
  refine ⟨p, hp, simplexAffineEquiv p hp, hpX, rfl,
    normalizedInnerCube_subset_image_convexHull hpX hp,
    image_convexHull_subset_normalizedOuterCube hpX hp hmax, ?_⟩
  exact normalizedOuterCube_volume_le_image_convexHull hpX hp

/-- A finite affinely spanning set contains a nondegenerate ordered simplex. -/
theorem exists_nonzero_simplex_of_affineSpan_eq_top {d : ℕ}
    (X : Finset (EuclideanPoint d))
    (hspanX : affineSpan ℝ (X : Set (EuclideanPoint d)) = ⊤) :
    ∃ p : Fin (d + 1) → EuclideanPoint d,
      (∀ i, p i ∈ X) ∧ simplexDet p ≠ 0 := by
  classical
  obtain ⟨t, htX, htspan, htind⟩ :=
    exists_affineIndependent ℝ (EuclideanPoint d) (X : Set (EuclideanPoint d))
  have htfinite : t.Finite := X.finite_toSet.subset htX
  let _ := htfinite.fintype
  let b : AffineBasis t ℝ (EuclideanPoint d) :=
    ⟨fun x ↦ x.1, htind, by simpa using htspan.trans hspanX⟩
  have hcard : Fintype.card t = d + 1 := by
    simpa using b.card_eq_finrank_add_one
  let σ : Fin (d + 1) ≃ t := Fintype.equivOfCardEq (by simpa using hcard.symm)
  let p : Fin (d + 1) → EuclideanPoint d := fun i ↦ (σ i).1
  have hpX : ∀ i, p i ∈ X := fun i ↦ htX (σ i).2
  have hpind : AffineIndependent ℝ p := by
    let bp : AffineBasis (Fin (d + 1)) ℝ (EuclideanPoint d) := b.reindex σ.symm
    exact bp.ind
  have hvsub := (affineIndependent_iff_linearIndependent_vsub ℝ p 0).mp hpind
  let f : Fin d → {j : Fin (d + 1) // j ≠ 0} :=
    fun i ↦ ⟨i.succ, Fin.succ_ne_zero i⟩
  have hf : Function.Injective f := by
    intro i j hij
    exact Fin.succ_injective d (congrArg Subtype.val hij)
  have hvli : LinearIndependent ℝ (simplexFrame p) := by
    have hcomp := hvsub.comp f hf
    simpa only [simplexFrame, f, Function.comp_apply, vsub_eq_sub] using! hcomp
  have hvspan : Submodule.span ℝ (Set.range (simplexFrame p)) = ⊤ :=
    hvli.span_eq_top_of_card_eq_finrank' (by simp)
  have hunit : IsUnit ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis.det
      (simplexFrame p)) :=
    ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis.is_basis_iff_det).mp
      ⟨hvli, hvspan⟩
  refine ⟨p, hpX, ?_⟩
  exact isUnit_iff_ne_zero.mp hunit

/-- Comparable enclosing-box normalization for every finite full-dimensional
set, with no separately supplied simplex. -/
theorem exists_comparable_enclosing_box {d : ℕ}
    (X : Finset (EuclideanPoint d))
    (hspanX : affineSpan ℝ (X : Set (EuclideanPoint d)) = ⊤) :
    ∃ (p : Fin (d + 1) → EuclideanPoint d) (hp : simplexDet p ≠ 0)
      (e : EuclideanPoint d ≃ᵃ[ℝ] EuclideanPoint d),
      (∀ i, p i ∈ X) ∧ e = simplexAffineEquiv p hp ∧
      normalizedInnerCube d ⊆ e '' convexHull ℝ (X : Set (EuclideanPoint d)) ∧
      e '' convexHull ℝ (X : Set (EuclideanPoint d)) ⊆ normalizedOuterCube d ∧
      volume (normalizedOuterCube d) ≤ normalizedBoxConstant d *
        volume (e '' convexHull ℝ (X : Set (EuclideanPoint d))) := by
  obtain ⟨p₀, hp₀X, hp₀⟩ := exists_nonzero_simplex_of_affineSpan_eq_top X hspanX
  exact exists_comparable_enclosing_box_of_nonzero_simplex X hp₀X hp₀

end

end Erdos186.PZ.ConvexDensity
