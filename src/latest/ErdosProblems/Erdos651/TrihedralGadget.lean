/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos651.AboveBelow
import ErdosProblems.Erdos651.TwoSeparation
import ErdosProblems.Erdos651.PolytopeCap
import ErdosProblems.Erdos651.CapRamsey
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dual.Basis

/-!
# The trihedral gadget of Pohoata--Zakharov

This file formalizes the three-region construction in Proposition 3.1 of
Pohoata--Zakharov.  For `j₁ < j₂ < j₃`, the clusters other than the
middle cluster `X j₂` are divided into the two alternating regions

* `i < j₁` or `j₂ < i ≤ j₃`, and
* `j₁ ≤ i < j₂` or `j₃ < i`.

The robust planar support construction separates the middle cluster from all
the others.  The two lifted alternating-block separations split the first
region from the second region together with the middle, and the second region
from the first together with the middle.  We turn these three strict
separations into two honest nondegenerate `OrientedTrihedral`s.

There are two small but important technical points.

1. Three separating normals need not initially be linearly independent.  The
   strict sign conditions form an open set.  The complement of every proper
   subspace of the three-dimensional dual is dense, so the normals can be
   perturbed, successively, to an independent triple without changing any
   sign on the finite cluster union.
2. Using the same closed threshold for both polyhedra would leave a common
   boundary ray.  We therefore choose a second threshold strictly inside the
   positive side of each finite separation.  The resulting closed
   polyhedra have a genuine gap, which supplies exactly the three convex-
   position separations used in the subsequent poset argument.
-/

namespace Erdos651

open Set

noncomputable section

abbrev PlaneNormal := Point 3 →L[ℝ] ℝ

/-! ## Alternating index regions -/

/-- The first region in (4.8): the initial block and the block immediately
after the middle index. -/
def firstTrihedralIndices {k : ℕ} (j₁ j₂ j₃ : Fin k) : Finset (Fin k) :=
  Finset.univ.filter fun i => i < j₁ ∨ (j₂ < i ∧ i ≤ j₃)

/-- The second region in (4.8): the block before the middle index and the
final block. -/
def secondTrihedralIndices {k : ℕ} (j₁ j₂ j₃ : Fin k) : Finset (Fin k) :=
  Finset.univ.filter fun i => (j₁ ≤ i ∧ i < j₂) ∨ j₃ < i

@[simp] theorem mem_firstTrihedralIndices {k : ℕ} {j₁ j₂ j₃ i : Fin k} :
    i ∈ firstTrihedralIndices j₁ j₂ j₃ ↔
      i < j₁ ∨ (j₂ < i ∧ i ≤ j₃) := by
  simp [firstTrihedralIndices]

@[simp] theorem mem_secondTrihedralIndices {k : ℕ} {j₁ j₂ j₃ i : Fin k} :
    i ∈ secondTrihedralIndices j₁ j₂ j₃ ↔
      (j₁ ≤ i ∧ i < j₂) ∨ j₃ < i := by
  simp [secondTrihedralIndices]

theorem trihedralIndices_pairwise_disjoint {k : ℕ}
    {j₁ j₂ j₃ : Fin k} (h₁₂ : j₁ < j₂) (h₂₃ : j₂ < j₃) :
    Disjoint (firstTrihedralIndices j₁ j₂ j₃)
      (secondTrihedralIndices j₁ j₂ j₃) := by
  classical
  rw [Finset.disjoint_left]
  intro i hi₁ hi₂
  simp only [mem_firstTrihedralIndices] at hi₁
  simp only [mem_secondTrihedralIndices] at hi₂
  rcases hi₁ with hi₁ | hi₁ <;> rcases hi₂ with hi₂ | hi₂ <;> omega

theorem trihedralIndices_union_middle {k : ℕ}
    {j₁ j₂ j₃ : Fin k} (h₁₂ : j₁ < j₂) (h₂₃ : j₂ < j₃) :
    firstTrihedralIndices j₁ j₂ j₃ ∪
        (secondTrihedralIndices j₁ j₂ j₃ ∪ {j₂}) = Finset.univ := by
  classical
  ext i
  simp only [Finset.mem_union, mem_firstTrihedralIndices,
    mem_secondTrihedralIndices, Finset.mem_singleton, Finset.mem_univ, iff_true]
  rcases lt_trichotomy i j₁ with hi | rfl | hi
  · exact Or.inl (Or.inl hi)
  · exact Or.inr (Or.inl (Or.inl ⟨le_rfl, h₁₂⟩))
  · rcases lt_trichotomy i j₂ with hi₂ | rfl | hi₂
    · exact Or.inr (Or.inl (Or.inl ⟨hi.le, hi₂⟩))
    · exact Or.inr (Or.inr rfl)
    · by_cases hi₃ : i ≤ j₃
      · exact Or.inl (Or.inr ⟨hi₂, hi₃⟩)
      · exact Or.inr (Or.inl (Or.inr (lt_of_not_ge hi₃)))

/-! ## Strict finite plane patterns -/

/-- A normal and two separated levels realizing a strict finite bipartition.
The negative finite set lies strictly below `low`; the positive finite set
lies strictly above `high`. -/
structure StrictPlaneSplit (A B : Finset (Point 3)) where
  normal : PlaneNormal
  low high : ℝ
  low_lt_high : low < high
  left_lt_low : ∀ x ∈ A, normal x < low
  high_lt_right : ∀ x ∈ B, high < normal x

/-- The un-gapped strict sign pattern about one level. -/
def RealizesPlanePattern (A B : Finset (Point 3))
    (normal : PlaneNormal) (offset : ℝ) : Prop :=
  (∀ x ∈ A, normal x < offset) ∧
    ∀ x ∈ B, offset < normal x

abbrev PlaneConstraint := PlaneNormal →ₗ[ℝ] ℝ

/-- A generic scalar coordinate separates a prescribed pair of points. -/
def pointDifferenceConstraint (x y : Point 3) : PlaneConstraint where
  toFun normal := normal x - normal y
  map_add' _ _ := by simp; ring
  map_smul' _ _ := by simp; ring

/-- With the first planar coordinate fixed to `first`, this is the oriented
area of the images of `x,y,z` as a linear functional of the second
coordinate. -/
def planarOrientationConstraint (first : PlaneNormal)
    (x y z : Point 3) : PlaneConstraint where
  toFun second :=
    (first y - first x) * (second z - second x) -
      (first z - first x) * (second y - second x)
  map_add' _ _ := by simp; ring
  map_smul' _ _ := by simp; ring

/-- Every triple of distinct points of `U` is affinely independent.  This is
the exact finite generic-position consequence needed for the three edge
projections. -/
def NoThreeCollinear (U : Finset (Point 3)) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U,
    x ≠ y → y ≠ z → x ≠ z →
      LinearIndependent ℝ ![y - x, z - x]

/-- The finite constraints saying that one scalar coordinate is injective on
`U`. -/
def pointDifferenceConstraints (U : Finset (Point 3)) : Finset PlaneConstraint :=
  by
    classical
    exact ((U.product U).filter fun p => p.1 ≠ p.2).image
      fun p => pointDifferenceConstraint p.1 p.2

/-- Once `first` is injective, these finite constraints say that the planar
map `(first, second)` sends no distinct triple of `U` to a collinear triple. -/
def planarOrientationConstraints (U : Finset (Point 3))
    (first : PlaneNormal) : Finset PlaneConstraint :=
  by
    classical
    exact ((U.product (U.product U)).filter fun p =>
        p.1 ≠ p.2.1 ∧ p.2.1 ≠ p.2.2 ∧ p.1 ≠ p.2.2).image
      fun p => planarOrientationConstraint first p.1 p.2.1 p.2.2

private theorem isOpen_realizesPlanePattern (A B : Finset (Point 3)) (offset : ℝ) :
    IsOpen {normal : PlaneNormal | RealizesPlanePattern A B normal offset} := by
  classical
  have hcontinuous (x : Point 3) :
      Continuous (fun normal : PlaneNormal => normal x) := by
    fun_prop
  have hleft : IsOpen {normal : PlaneNormal | ∀ x ∈ A, normal x < offset} := by
    induction A using Finset.induction_on with
    | empty => simp
    | @insert x A hx ih =>
        simpa only [Finset.mem_insert, forall_eq_or_imp, Set.setOf_and] using
          (isOpen_lt (hcontinuous x) continuous_const).inter ih
  have hright : IsOpen {normal : PlaneNormal | ∀ x ∈ B, offset < normal x} := by
    induction B using Finset.induction_on with
    | empty => simp
    | @insert x B hx ih =>
        simpa only [Finset.mem_insert, forall_eq_or_imp, Set.setOf_and] using
          (isOpen_lt continuous_const (hcontinuous x)).inter ih
  simpa only [RealizesPlanePattern, Set.setOf_and] using hleft.inter hright

private theorem finrank_planeNormal : Module.finrank ℝ PlaneNormal = 3 := by
  rw [← (LinearMap.toContinuousLinearMap
    (E := Point 3) (F' := ℝ)).finrank_eq]
  rw [Module.finrank_linearMap_self, finrank_euclideanSpace_fin]

private theorem span_planeNormals_ne_top {m : ℕ} (hm : m < 3)
    (v : Fin m → PlaneNormal) :
    Submodule.span ℝ (Set.range v) ≠ ⊤ := by
  intro htop
  have hdim := finrank_range_le_card (R := ℝ) v
  rw [htop, Submodule.finrank_top, finrank_planeNormal] at hdim
  exact (not_le_of_gt hm) (by simpa using hdim)

private theorem dense_compl_ker_planeConstraint {L : PlaneConstraint} (hL : L ≠ 0) :
    Dense (((LinearMap.ker L : Submodule ℝ PlaneNormal) : Set PlaneNormal)ᶜ) := by
  apply interior_eq_empty_iff_dense_compl.mp
  by_contra hne
  have htop := (LinearMap.ker L).eq_top_of_nonempty_interior'
    (Set.nonempty_iff_ne_empty.mpr hne)
  exact hL (LinearMap.ker_eq_top.mp htop)

private theorem isOpen_compl_ker_planeConstraint (L : PlaneConstraint) :
    IsOpen (((LinearMap.ker L : Submodule ℝ PlaneNormal) : Set PlaneNormal)ᶜ) := by
  exact (Submodule.closed_of_finiteDimensional (LinearMap.ker L)).isOpen_compl

/-- A nonempty open family of normals contains a point avoiding any finite
family of nonzero linear equations. -/
private theorem exists_mem_open_avoiding_constraints
    {O : Set PlaneNormal} (hO : IsOpen O) (hOne : O.Nonempty)
    (C : Finset PlaneConstraint) (hC : ∀ L ∈ C, L ≠ 0) :
    ∃ normal ∈ O, ∀ L ∈ C, L normal ≠ 0 := by
  classical
  induction C using Finset.induction_on generalizing O with
  | empty =>
      obtain ⟨normal, hn⟩ := hOne
      exact ⟨normal, hn, by simp⟩
  | @insert L C hLC ih =>
      have hL : L ≠ 0 := hC L (by simp)
      let O' : Set PlaneNormal :=
        O ∩ (((LinearMap.ker L : Submodule ℝ PlaneNormal) : Set PlaneNormal)ᶜ)
      have hO' : IsOpen O' :=
        hO.inter (isOpen_compl_ker_planeConstraint L)
      have hOne' : O'.Nonempty := by
        obtain ⟨normal, hnker, hnO⟩ :=
          (dense_compl_ker_planeConstraint hL).exists_mem_open hO hOne
        exact ⟨normal, hnO, hnker⟩
      obtain ⟨normal, hnO', hnC⟩ :=
        ih hO' hOne' (fun K hKC => hC K (by simp [hKC]))
      refine ⟨normal, hnO'.1, ?_⟩
      intro K hK
      rw [Finset.mem_insert] at hK
      rcases hK with rfl | hK
      · simpa only [LinearMap.mem_ker, Set.mem_compl_iff] using hnO'.2
      · exact hnC K hK

/-- Strict finite sign patterns can avoid any proper linear subspace of the
dual.  This is the sign-preserving perturbation used to make the three
separators independent. -/
private theorem exists_pattern_normal_not_mem
    (A B : Finset (Point 3)) (offset : ℝ)
    (W : Submodule ℝ PlaneNormal) (hW : W ≠ ⊤)
    (normal : PlaneNormal) (hpattern : RealizesPlanePattern A B normal offset) :
    ∃ normal' : PlaneNormal,
      normal' ∉ W ∧ RealizesPlanePattern A B normal' offset := by
  have hinterior : interior (W : Set PlaneNormal) = ∅ := by
    by_contra hne
    exact hW (W.eq_top_of_nonempty_interior'
      (Set.nonempty_iff_ne_empty.mpr hne))
  have hdense : Dense ((W : Set PlaneNormal)ᶜ) :=
    interior_eq_empty_iff_dense_compl.mp hinterior
  obtain ⟨normal', hnW, hnpat⟩ :=
    hdense.exists_mem_open (isOpen_realizesPlanePattern A B offset)
      ⟨normal, hpattern⟩
  exact ⟨normal', hnW, hnpat⟩

/-- Simultaneously avoid a proper subspace and finitely many nonzero
polynomial-linear genericity equations while preserving all finite signs. -/
private theorem exists_pattern_normal_not_mem_avoiding
    (A B : Finset (Point 3)) (offset : ℝ)
    (W : Submodule ℝ PlaneNormal) (hW : W ≠ ⊤)
    (C : Finset PlaneConstraint) (hC : ∀ L ∈ C, L ≠ 0)
    (normal : PlaneNormal) (hpattern : RealizesPlanePattern A B normal offset) :
    ∃ normal' : PlaneNormal,
      normal' ∉ W ∧ RealizesPlanePattern A B normal' offset ∧
        ∀ L ∈ C, L normal' ≠ 0 := by
  obtain ⟨witness, hwW, hwpattern⟩ :=
    exists_pattern_normal_not_mem A B offset W hW normal hpattern
  let O : Set PlaneNormal :=
    {normal | RealizesPlanePattern A B normal offset} ∩ (W : Set PlaneNormal)ᶜ
  have hO : IsOpen O :=
    (isOpen_realizesPlanePattern A B offset).inter
      (Submodule.closed_of_finiteDimensional W).isOpen_compl
  have hOne : O.Nonempty := ⟨witness, hwpattern, hwW⟩
  obtain ⟨normal', hnO, hnC⟩ :=
    exists_mem_open_avoiding_constraints hO hOne C hC
  exact ⟨normal', hnO.2, hnO.1, hnC⟩

private theorem exists_high_level {B : Finset (Point 3)} (hB : B.Nonempty)
    (normal : PlaneNormal) (offset : ℝ)
    (hpositive : ∀ x ∈ B, offset < normal x) :
    ∃ high : ℝ, offset < high ∧ ∀ x ∈ B, high < normal x := by
  classical
  have himage : (B.image normal).Nonempty := hB.image normal
  let m : ℝ := (B.image normal).min' himage
  have hoffset_m : offset < m := by
    obtain ⟨x, hxB, hxm⟩ := Finset.mem_image.mp
      (Finset.min'_mem (B.image normal) himage)
    subst m
    exact hpositive x hxB
  refine ⟨(offset + m) / 2, by linarith, ?_⟩
  intro x hxB
  have hm_le : m ≤ normal x :=
    Finset.min'_le _ _ (Finset.mem_image_of_mem normal hxB)
  linarith

theorem pointDifferenceConstraint_ne_zero {x y : Point 3} (hxy : x ≠ y) :
    pointDifferenceConstraint x y ≠ 0 := by
  intro hzero
  have h := congrArg (fun L : PlaneConstraint => L (innerSL ℝ (x - y))) hzero
  simp only [pointDifferenceConstraint, LinearMap.zero_apply,
    innerSL_apply_apply] at h
  have hinner : ⟪x - y, x - y⟫_ℝ = 0 := by
    calc
      ⟪x - y, x - y⟫_ℝ =
          ⟪x - y, x⟫_ℝ - ⟪x - y, y⟫_ℝ := by rw [inner_sub_right]
      _ = 0 := h
  exact (inner_self_ne_zero.mpr (sub_ne_zero.mpr hxy)) hinner

theorem pointDifferenceConstraints_nonzero (U : Finset (Point 3)) :
    ∀ L ∈ pointDifferenceConstraints U, L ≠ 0 := by
  classical
  intro L hL
  simp only [pointDifferenceConstraints, Finset.mem_image] at hL
  obtain ⟨p, hp, rfl⟩ := hL
  exact pointDifferenceConstraint_ne_zero (Finset.mem_filter.mp hp).2

theorem realizes_pointDifferenceConstraints_iff
    {U : Finset (Point 3)} {normal : PlaneNormal} :
    (∀ L ∈ pointDifferenceConstraints U, L normal ≠ 0) ↔
      ∀ x ∈ U, ∀ y ∈ U, x ≠ y → normal x ≠ normal y := by
  classical
  constructor
  · intro h x hx y hy hxy hEq
    have hmem : pointDifferenceConstraint x y ∈ pointDifferenceConstraints U := by
      simp [pointDifferenceConstraints, hx, hy, hxy]
    exact h _ hmem (by simp [pointDifferenceConstraint, hEq])
  · intro h L hL
    simp only [pointDifferenceConstraints, Finset.mem_image] at hL
    obtain ⟨p, hp, rfl⟩ := hL
    have hp' := Finset.mem_filter.mp hp
    simpa [pointDifferenceConstraint] using h p.1 hp'.1.1 p.2 hp'.1.2 hp'.2

private theorem planarOrientationConstraint_ne_zero
    {U : Finset (Point 3)} (htriple : NoThreeCollinear U)
    {first : PlaneNormal}
    (hfirst : ∀ x ∈ U, ∀ y ∈ U, x ≠ y → first x ≠ first y)
    {x y z : Point 3} (hx : x ∈ U) (hy : y ∈ U) (hz : z ∈ U)
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    planarOrientationConstraint first x y z ≠ 0 := by
  intro hzero
  let a : ℝ := first y - first x
  let b : ℝ := first z - first x
  let v : Point 3 := y - x
  let w : Point 3 := z - x
  let q : Point 3 := a • w - b • v
  have ha : a ≠ 0 := sub_ne_zero.mpr (hfirst y hy x hx hxy.symm)
  have hb : b ≠ 0 := sub_ne_zero.mpr (hfirst z hz x hx hxz.symm)
  have hqinner := LinearMap.congr_fun hzero (innerSL ℝ q)
  have hqzero : q = 0 := by
    apply (inner_self_eq_zero.mp ?_)
    calc
      ⟪q, q⟫_ℝ =
          a * (innerSL ℝ q z - innerSL ℝ q x) -
            b * (innerSL ℝ q y - innerSL ℝ q x) := by
        simp only [q, v, w, innerSL_apply_apply, inner_sub_right,
          inner_sub_left, real_inner_smul_right]
        ring
      _ = 0 := by
        simpa only [planarOrientationConstraint, a, b,
          LinearMap.zero_apply] using hqinner
  have hrel : a • w = b • v := sub_eq_zero.mp hqzero
  have hvw : (a / b) • w = v := by
    calc
      (a / b) • w = b⁻¹ • (a • w) := by
        simp only [div_eq_mul_inv, smul_smul]
        congr 1
        ring
      _ = b⁻¹ • (b • v) := congrArg (fun t : Point 3 => b⁻¹ • t) hrel
      _ = v := by simp [smul_smul, hb]
  have hlin := htriple x hx y hy z hz hxy hyz hxz
  exact (linearIndependent_fin2.mp hlin).2 (a / b) hvw

theorem planarOrientationConstraints_nonzero
    {U : Finset (Point 3)} (htriple : NoThreeCollinear U)
    {first : PlaneNormal}
    (hfirst : ∀ x ∈ U, ∀ y ∈ U, x ≠ y → first x ≠ first y) :
    ∀ L ∈ planarOrientationConstraints U first, L ≠ 0 := by
  classical
  intro L hL
  simp only [planarOrientationConstraints, Finset.mem_image] at hL
  obtain ⟨p, hp, rfl⟩ := hL
  have hp' := Finset.mem_filter.mp hp
  have hpU := Finset.mem_product.mp hp'.1
  exact planarOrientationConstraint_ne_zero htriple hfirst
    p.1 hpU.1 p.2.1 (Finset.mem_product.mp hpU.2).1
      p.2.2 (Finset.mem_product.mp hpU.2).2
    hp'.2.1 hp'.2.2.1 hp'.2.2.2

theorem realizes_planarOrientationConstraints_iff
    {U : Finset (Point 3)} {first second : PlaneNormal} :
    (∀ L ∈ planarOrientationConstraints U first, L second ≠ 0) ↔
      ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U,
        x ≠ y → y ≠ z → x ≠ z →
          (first y - first x) * (second z - second x) -
            (first z - first x) * (second y - second x) ≠ 0 := by
  classical
  constructor
  · intro h x hx y hy z hz hxy hyz hxz
    apply h (planarOrientationConstraint first x y z)
    simp [planarOrientationConstraints, hx, hy, hz, hxy, hyz, hxz]
  · intro h L hL
    simp only [planarOrientationConstraints, Finset.mem_image] at hL
    obtain ⟨p, hp, rfl⟩ := hL
    have hp' := Finset.mem_filter.mp hp
    have hpU := Finset.mem_product.mp hp'.1
    exact h p.1 hpU.1 p.2.1 (Finset.mem_product.mp hpU.2).1
      p.2.2 (Finset.mem_product.mp hpU.2).2
      hp'.2.1 hp'.2.2.1 hp'.2.2.2

private theorem exists_strictPlaneSplit_avoiding
    (A B : Finset (Point 3)) (hB : B.Nonempty)
    (hdisj : Disjoint (convexHull ℝ (A : Set (Point 3)))
      (convexHull ℝ (B : Set (Point 3))))
    (W : Submodule ℝ PlaneNormal) (hW : W ≠ ⊤) :
    ∃ split : StrictPlaneSplit A B, split.normal ∉ W := by
  obtain ⟨normal, offset, hleft, hright⟩ :=
    finite_sets_strictly_separated_point3 A B hdisj
  obtain ⟨normal', hnW, hpattern⟩ :=
    exists_pattern_normal_not_mem A B offset W hW normal ⟨hleft, hright⟩
  obtain ⟨high, hoffset_high, hhigh⟩ :=
    exists_high_level hB normal' offset hpattern.2
  exact ⟨⟨normal', offset, high, hoffset_high, hpattern.1, hhigh⟩, hnW⟩

private theorem exists_strictPlaneSplit_avoiding_generic
    (A B : Finset (Point 3)) (hB : B.Nonempty)
    (hdisj : Disjoint (convexHull ℝ (A : Set (Point 3)))
      (convexHull ℝ (B : Set (Point 3))))
    (W : Submodule ℝ PlaneNormal) (hW : W ≠ ⊤)
    (C : Finset PlaneConstraint) (hC : ∀ L ∈ C, L ≠ 0) :
    ∃ split : StrictPlaneSplit A B,
      split.normal ∉ W ∧ ∀ L ∈ C, L split.normal ≠ 0 := by
  obtain ⟨normal, offset, hleft, hright⟩ :=
    finite_sets_strictly_separated_point3 A B hdisj
  obtain ⟨normal', hnW, hpattern, hnC⟩ :=
    exists_pattern_normal_not_mem_avoiding A B offset W hW C hC normal
      ⟨hleft, hright⟩
  obtain ⟨high, hoffset_high, hhigh⟩ :=
    exists_high_level hB normal' offset hpattern.2
  exact ⟨⟨normal', offset, high, hoffset_high, hpattern.1, hhigh⟩, hnW, hnC⟩

/-! ## From an independent triple of planes to an oriented trihedral -/

private def algebraicNormal (normal : PlaneNormal) : Module.Dual ℝ (Point 3) :=
  normal.toLinearMap

private theorem algebraicNormals_linearIndependent {normal : Fin 3 → PlaneNormal}
    (h : LinearIndependent ℝ normal) :
    LinearIndependent ℝ (fun i => algebraicNormal (normal i)) := by
  let e : (Module.Dual ℝ (Point 3)) ≃ₗ[ℝ] PlaneNormal :=
    LinearMap.toContinuousLinearMap
  have hmapped := h.map' e.symm.toLinearMap (by simp)
  simpa only [Function.comp_apply, e, algebraicNormal] using hmapped

private def planeCoordinateLinearEquiv (normal : Fin 3 → PlaneNormal)
    (h : LinearIndependent ℝ normal) : Point 3 ≃ₗ[ℝ] Point 3 := by
  let an : Fin 3 → Module.Dual ℝ (Point 3) :=
    fun i => algebraicNormal (normal i)
  have han : LinearIndependent ℝ an := algebraicNormals_linearIndependent h
  have hcard : Fintype.card (Fin 3) =
      Module.finrank ℝ (Module.Dual ℝ (Point 3)) := by
    rw [Module.dual_finrank_eq, finrank_euclideanSpace_fin]
    simp
  let b : Basis (Fin 3) ℝ (Module.Dual ℝ (Point 3)) :=
    basisOfLinearIndependentOfCardEqFinrank' an han hcard
  let eFun : Point 3 ≃ₗ[ℝ] (Fin 3 → ℝ) :=
    (Module.evalEquiv ℝ (Point 3)).trans b.dualBasis.equivFun
  exact eFun.trans (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm

private theorem planeCoordinateLinearEquiv_apply
    (normal : Fin 3 → PlaneNormal) (h : LinearIndependent ℝ normal)
    (x : Point 3) (i : Fin 3) :
    planeCoordinateLinearEquiv normal h x i = normal i x := by
  simp only [planeCoordinateLinearEquiv, LinearEquiv.trans_apply,
    WithLp.linearEquiv_symm_apply, WithLp.toLp_apply,
    Basis.dualBasis_equivFun, Module.evalEquiv_apply, Module.Dual.eval_apply,
    algebraicNormal]
  rw [coe_basisOfLinearIndependentOfCardEqFinrank']
  rfl

/-- The oriented trihedral whose normalized coordinates are the prescribed
independent affine functionals `normal i x - offset i`. -/
def orientedTrihedralOfIndependentPlanes
    (normal : Fin 3 → PlaneNormal) (offset : Fin 3 → ℝ)
    (h : LinearIndependent ℝ normal) : OrientedTrihedral where
  normalization :=
    (planeCoordinateLinearEquiv normal h).toAffineEquiv.trans
      (AffineEquiv.constVAdd ℝ (Point 3) (-(WithLp.toLp 2 offset)))

@[simp] theorem orientedTrihedralOfIndependentPlanes_functional
    (normal : Fin 3 → PlaneNormal) (offset : Fin 3 → ℝ)
    (h : LinearIndependent ℝ normal) (i : Fin 3) (x : Point 3) :
    (orientedTrihedralOfIndependentPlanes normal offset h).functional i x =
      normal i x - offset i := by
  simp [orientedTrihedralOfIndependentPlanes, OrientedTrihedral.functional,
    planeCoordinateLinearEquiv_apply]

private theorem secantSlope_ne_of_orientation
    {ax ay az bx by bz : ℝ}
    (haxy : ax ≠ ay) (hayz : ay ≠ az)
    (horient : (ay - ax) * (bz - bx) - (az - ax) * (by - bx) ≠ 0) :
    (by - bx) / (ay - ax) ≠ (bz - by) / (az - ay) := by
  intro hslope
  have hcross := (div_eq_div_iff
    (sub_ne_zero.mpr haxy.symm) (sub_ne_zero.mpr hayz.symm)).mp hslope
  apply horient
  nlinarith

/-- The canonical edge projections are fully generic on `X` if each of the
three normalized affine coordinates is injective on `X` and every pair of
their linear parts has nonzero oriented area on every distinct triple. -/
private def genericProjectionFamilyOfIndependentPlanes
    (normal : Fin 3 → PlaneNormal) (offset : Fin 3 → ℝ)
    (h : LinearIndependent ℝ normal) (X : Finset (Point 3))
    (hinjective : ∀ i {x y : Point 3}, x ∈ X → y ∈ X → x ≠ y →
      normal i x ≠ normal i y)
    (horient01 : ∀ {x y z : Point 3},
      x ∈ X → y ∈ X → z ∈ X →
      x ≠ y → y ≠ z → x ≠ z →
        (normal 0 y - normal 0 x) * (normal 1 z - normal 1 x) -
          (normal 0 z - normal 0 x) * (normal 1 y - normal 1 x) ≠ 0)
    (horient02 : ∀ {x y z : Point 3},
      x ∈ X → y ∈ X → z ∈ X →
      x ≠ y → y ≠ z → x ≠ z →
        (normal 0 y - normal 0 x) * (normal 2 z - normal 2 x) -
          (normal 0 z - normal 0 x) * (normal 2 y - normal 2 x) ≠ 0)
    (horient12 : ∀ {x y z : Point 3},
      x ∈ X → y ∈ X → z ∈ X →
      x ≠ y → y ≠ z → x ≠ z →
        (normal 1 y - normal 1 x) * (normal 2 z - normal 2 x) -
          (normal 1 z - normal 1 x) * (normal 2 y - normal 2 x) ≠ 0) :
    (orientedTrihedralOfIndependentPlanes normal offset h).GenericProjectionFamily X := by
  let T := orientedTrihedralOfIndependentPlanes normal offset h
  refine {
    projection := T.edgeProjection
    image_carrier := T.edgeProjection_image_carrier
    separated := fun hfree _ _ hxy => T.projectionOrders_separated hfree hxy
    planeX_ne := ?_
    planeY_ne := ?_
    slope_ne := ?_ }
  · intro i x y hx hy hxy
    fin_cases i
    · simpa [T, OrientedTrihedral.edgeProjection, dropCoordinate3,
        dropCoordinate0, planeX] using hinjective 1 hx hy hxy
    · simpa [T, OrientedTrihedral.edgeProjection, dropCoordinate3,
        dropCoordinate1, planeX] using hinjective 0 hx hy hxy
    · simpa [T, OrientedTrihedral.edgeProjection, dropCoordinate3,
        dropCoordinate2, planeX] using hinjective 0 hx hy hxy
  · intro i x y hx hy hxy
    fin_cases i
    · simpa [T, OrientedTrihedral.edgeProjection, dropCoordinate3,
        dropCoordinate0, planeY] using hinjective 2 hx hy hxy
    · simpa [T, OrientedTrihedral.edgeProjection, dropCoordinate3,
        dropCoordinate1, planeY] using hinjective 2 hx hy hxy
    · simpa [T, OrientedTrihedral.edgeProjection, dropCoordinate3,
        dropCoordinate2, planeY] using hinjective 1 hx hy hxy
  · intro i x y z hx hy hz hxy hyz hxz
    fin_cases i
    · have ho := horient12 hx hy hz hxy hyz hxz
      have hs := secantSlope_ne_of_orientation
        (hinjective 1 hx hy hxy) (hinjective 1 hy hz hyz) ho
      simpa [T, OrientedTrihedral.edgeProjection, dropCoordinate3,
        dropCoordinate0, secantSlope, planeX, planeY] using hs
    · have ho := horient02 hx hy hz hxy hyz hxz
      have hs := secantSlope_ne_of_orientation
        (hinjective 0 hx hy hxy) (hinjective 0 hy hz hyz) ho
      simpa [T, OrientedTrihedral.edgeProjection, dropCoordinate3,
        dropCoordinate1, secantSlope, planeX, planeY] using hs
    · have ho := horient01 hx hy hz hxy hyz hxz
      have hs := secantSlope_ne_of_orientation
        (hinjective 0 hx hy hxy) (hinjective 0 hy hz hyz) ho
      simpa [T, OrientedTrihedral.edgeProjection, dropCoordinate3,
        dropCoordinate2, secantSlope, planeX, planeY] using hs

/-! ## The geometric output -/

/-- Three sets are in the strong three-object convex-position configuration
needed in the second Dilworth step.  Each object misses the convex hull of
the other two. -/
def ThreeSetsInConvexPosition (A B C : Set (Point 3)) : Prop :=
  Disjoint A (convexHull ℝ (B ∪ C)) ∧
    Disjoint B (convexHull ℝ (A ∪ C)) ∧
      Disjoint C (convexHull ℝ (A ∪ B))

/-- The complete Proposition 3.1 gadget attached to a middle cluster. -/
structure TrihedralClusterGadget {k : ℕ} (X : Fin k → Finset (Point 3))
    (j₁ j₂ j₃ : Fin k) where
  first : OrientedTrihedral
  second : OrientedTrihedral
  first_region_subset :
    (↑(clusterUnion X (firstTrihedralIndices j₁ j₂ j₃)) : Set (Point 3)) ⊆
      first.carrier
  second_region_subset :
    (↑(clusterUnion X (secondTrihedralIndices j₁ j₂ j₃)) : Set (Point 3)) ⊆
      second.carrier
  convex_position : ThreeSetsInConvexPosition first.carrier second.carrier
    (convexHull ℝ (↑(X j₂) : Set (Point 3)))
  first_line_comparable : ∀ {x}, x ∈ X j₂ → ∀ {y}, y ∈ X j₂ → x ≠ y →
    ¬ Disjoint (lineThrough x y) first.carrier →
      sourcePolytopeLE first.carrier x y ∨
        sourcePolytopeLE first.carrier y x
  comparable_line_second : ∀ {x}, x ∈ X j₂ → ∀ {y}, y ∈ X j₂ → x ≠ y →
    (sourcePolytopeLE first.carrier x y ∨
      sourcePolytopeLE first.carrier y x) →
        Disjoint (lineThrough x y) second.carrier
  first_generic : first.GenericProjectionFamily (X j₂)
  second_generic : second.GenericProjectionFamily (X j₂)

namespace TrihedralClusterGadget

theorem middle_disjoint_first {k : ℕ} {X : Fin k → Finset (Point 3)}
    {j₁ j₂ j₃ : Fin k} (G : TrihedralClusterGadget X j₁ j₂ j₃) :
    Disjoint (↑(X j₂) : Set (Point 3)) G.first.carrier := by
  apply Disjoint.symm
  apply (G.convex_position.1.mono_right convexHull_mono ?_).mono_right
    (subset_convexHull ℝ _)
  exact Set.subset_union_right

theorem middle_disjoint_second {k : ℕ} {X : Fin k → Finset (Point 3)}
    {j₁ j₂ j₃ : Fin k} (G : TrihedralClusterGadget X j₁ j₂ j₃) :
    Disjoint (↑(X j₂) : Set (Point 3)) G.second.carrier := by
  apply Disjoint.symm
  apply (G.convex_position.2.1.mono_right convexHull_mono ?_).mono_right
    (subset_convexHull ℝ _)
  exact Set.subset_union_right

/-- The exact input consumed by the second Dilworth--Ramsey step.  All free-
set conclusions are derived by `ofLineSeparation`; none is a field of the
trihedral construction. -/
def toMiddleTripleGadget {k : ℕ} {X : Fin k → Finset (Point 3)}
    {j₁ j₂ j₃ : Fin k} (G : TrihedralClusterGadget X j₁ j₂ j₃) :
    MiddleTripleGadget :=
  MiddleTripleGadget.ofLineSeparation (X j₂) G.first.carrier G.second.carrier
    G.middle_disjoint_first G.middle_disjoint_second
    G.first_line_comparable G.comparable_line_second

end TrihedralClusterGadget

private theorem convex_plane_le (normal : PlaneNormal) (c : ℝ) :
    Convex ℝ {x : Point 3 | normal x ≤ c} := by
  exact convex_halfSpace_le normal.toLinearMap.isLinear c

private theorem convex_plane_ge (normal : PlaneNormal) (c : ℝ) :
    Convex ℝ {x : Point 3 | c ≤ normal x} := by
  exact convex_halfSpace_ge normal.toLinearMap.isLinear c

private theorem convexHull_subset_plane_le {S : Set (Point 3)}
    {normal : PlaneNormal} {c : ℝ} (hS : ∀ x ∈ S, normal x ≤ c) :
    convexHull ℝ S ⊆ {x : Point 3 | normal x ≤ c} :=
  convexHull_min hS (convex_plane_le normal c)

private theorem convexHull_subset_plane_ge {S : Set (Point 3)}
    {normal : PlaneNormal} {c : ℝ} (hS : ∀ x ∈ S, c ≤ normal x) :
    convexHull ℝ S ⊆ {x : Point 3 | c ≤ normal x} :=
  convexHull_min hS (convex_plane_ge normal c)

private theorem disjoint_of_plane_gap {A B : Set (Point 3)}
    {normal : PlaneNormal} {low high : ℝ} (hlh : low < high)
    (hA : ∀ x ∈ A, high ≤ normal x)
    (hB : ∀ x ∈ B, normal x ≤ low) : Disjoint A B := by
  rw [Set.disjoint_left]
  intro x hxA hxB
  exact (not_le_of_gt hlh) ((hA x hxA).trans (hB x hxB))

/-! ## The source-poset line implications -/

/-- A line through two points of a convex set which meets a disjoint convex
background makes one of the two points lie in the convex hull of the other
point and the background.  The proof is the one-dimensional parameter
calculation used immediately after Proposition 3.1 in the source. -/
private theorem source_comparable_of_line_meets
    {P C : Set (Point 3)} (hC : Convex ℝ C) (hPC : Disjoint P C)
    {x y : Point 3} (hx : x ∈ C) (hy : y ∈ C) (hxy : x ≠ y)
    (hmeet : ¬ Disjoint (lineThrough x y) P) :
    sourcePolytopeLE P x y ∨ sourcePolytopeLE P y x := by
  obtain ⟨p, hpline, hpP⟩ := Set.not_disjoint_iff.mp hmeet
  rw [lineThrough, mem_affineSpan_pair_iff_exists_lineMap_eq] at hpline
  obtain ⟨t, ht⟩ := hpline
  have htout : t ∉ Set.Icc (0 : ℝ) 1 := by
    intro htI
    apply Set.disjoint_left.mp hPC hpP
    rw [← ht]
    exact hC.lineMap_mem hx hy htI
  have htcase : t < 0 ∨ 1 < t := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using htout
  rcases htcase with htneg | htpos
  · left
    let s : ℝ := -t / (1 - t)
    have hden : 0 < 1 - t := by linarith
    have hs : s ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (by linarith) hden.le
      · exact (div_le_one hden).mpr (by linarith)
    have heq : AffineMap.lineMap p y s = x := by
      rw [← ht]
      ext i
      simp only [AffineMap.lineMap_apply_module', s]
      field_simp
      ring
    rw [sourcePolytopeLE, ← heq]
    apply (convex_convexHull ℝ _).lineMap_mem
    · exact subset_convexHull ℝ _ (Or.inr hpP)
    · exact subset_convexHull ℝ _ (Or.inl (Set.mem_singleton y))
    · exact hs
  · right
    let s : ℝ := 1 / t
    have ht0 : 0 < t := by linarith
    have hs : s ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg zero_le_one ht0.le
      · exact (div_le_one ht0).mpr (by linarith)
    have heq : AffineMap.lineMap x p s = y := by
      rw [← ht]
      ext i
      simp only [AffineMap.lineMap_apply_module', s]
      field_simp
      ring
    rw [sourcePolytopeLE, ← heq]
    apply (convex_convexHull ℝ _).lineMap_mem
    · exact subset_convexHull ℝ _ (Or.inl (Set.mem_singleton x))
    · exact subset_convexHull ℝ _ (Or.inr hpP)
    · exact hs

private theorem line_meets_of_sourcePolytopeLE
    {P : Set (Point 3)} (hPconv : Convex ℝ P) (hPne : P.Nonempty)
    {x y : Point 3} (hxy : x ≠ y) (hxP : x ∉ P)
    (hrel : sourcePolytopeLE P x y) :
    ¬ Disjoint (lineThrough x y) P := by
  rw [sourcePolytopeLE,
    (convex_singleton y).convexHull_union hPconv
      (Set.singleton_nonempty y) hPne, mem_convexJoin] at hrel
  obtain ⟨q, hq, p, hpP, hxseg⟩ := hrel
  rw [Set.mem_singleton_iff] at hq
  subst q
  have hpLine : p ∈ lineThrough x y := by
    rw [lineThrough]
    exact ((mem_segment_iff_wbtw.mp hxseg).symm).left_mem_affineSpan_of_right_ne
      hxy.symm
  exact Set.not_disjoint_iff.mpr ⟨p, hpLine, hpP⟩

/-- If two sets lie strictly on one side of a linear functional while two
points lie on the other side, their common affine line cannot meet both sets
when each set is exposed from the convex hull of the other set and the high
side.  This is the collinear three-object argument in an explicit scalar
parameter form. -/
private theorem line_disjoint_of_two_low_exposed
    {P Q C : Set (Point 3)} (normal : PlaneNormal) {low high : ℝ}
    (hlh : low < high)
    (hP : ∀ p ∈ P, normal p ≤ low) (hQ : ∀ q ∈ Q, normal q ≤ low)
    (hC : ∀ c ∈ C, high ≤ normal c)
    (hPexposed : Disjoint P (convexHull ℝ (Q ∪ C)))
    (hQexposed : Disjoint Q (convexHull ℝ (P ∪ C)))
    {x y : Point 3} (hx : x ∈ C) (hy : y ∈ C) :
    ¬ Disjoint (lineThrough x y) P → Disjoint (lineThrough x y) Q := by
  intro hlineP
  by_contra hlineQ
  obtain ⟨p, hpline, hpP⟩ := Set.not_disjoint_iff.mp hlineP
  obtain ⟨q, hqline, hqQ⟩ := Set.not_disjoint_iff.mp hlineQ
  rw [lineThrough, mem_affineSpan_pair_iff_exists_lineMap_eq] at hpline hqline
  obtain ⟨t, ht⟩ := hpline
  obtain ⟨u, hu⟩ := hqline
  have htout : t < 0 ∨ 1 < t := by
    have htI : t ∉ Set.Icc (0 : ℝ) 1 := by
      intro htI
      have hpHigh : high ≤ normal p := by
        rw [← ht]
        simp only [AffineMap.lineMap_apply_module', map_add, map_smul]
        rcases htI with ⟨ht0, ht1⟩
        nlinarith [hC x hx, hC y hy]
      exact (not_le_of_gt hlh) (hpHigh.trans (hP p hpP))
    simpa only [Set.mem_Icc, not_and_or, not_le] using htI
  have huout : u < 0 ∨ 1 < u := by
    have huI : u ∉ Set.Icc (0 : ℝ) 1 := by
      intro huI
      have hqHigh : high ≤ normal q := by
        rw [← hu]
        simp only [AffineMap.lineMap_apply_module', map_add, map_smul]
        rcases huI with ⟨hu0, hu1⟩
        nlinarith [hC x hx, hC y hy]
      exact (not_le_of_gt hlh) (hqHigh.trans (hQ q hqQ))
    simpa only [Set.mem_Icc, not_and_or, not_le] using huI
  have hpformula : normal p = (1 - t) * normal x + t * normal y := by
    rw [← ht]
    simp [AffineMap.lineMap_apply_module']
  have hqformula : normal q = (1 - u) * normal x + u * normal y := by
    rw [← hu]
    simp [AffineMap.lineMap_apply_module']
  have hsame : (t < 0 ∧ u < 0) ∨ (1 < t ∧ 1 < u) := by
    rcases htout with htneg | htpos <;> rcases huout with huneg | hupos
    · exact Or.inl ⟨htneg, huneg⟩
    · exfalso
      nlinarith [hP p hpP, hQ q hqQ, hC x hx, hC y hy,
        hpformula, hqformula]
    · exfalso
      nlinarith [hP p hpP, hQ q hqQ, hC x hx, hC y hy,
        hpformula, hqformula]
    · exact Or.inr ⟨htpos, hupos⟩
  rcases hsame with hneg | hpos
  · rcases le_total t u with htu | hut
    · have ht0 : t ≠ 0 := ne_of_lt hneg.1
      let s : ℝ := 1 - u / t
      have hs : s ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · have : u / t ≤ 1 := (div_le_one_of_neg hneg.1).2 htu
          linarith
        · have : 0 ≤ u / t := div_nonneg_of_nonpos hneg.2.le hneg.1.le
          linarith
      have heq : AffineMap.lineMap p x s = q := by
        rw [← ht, ← hu]
        ext i
        simp only [AffineMap.lineMap_apply_module', s]
        field_simp
        ring
      apply Set.disjoint_left.mp hQexposed hqQ
      rw [← heq]
      apply (convex_convexHull ℝ _).lineMap_mem
      · exact subset_convexHull ℝ _ (Or.inl hpP)
      · exact subset_convexHull ℝ _ (Or.inr hx)
      · exact hs
    · have hu0 : u ≠ 0 := ne_of_lt hneg.2
      let s : ℝ := 1 - t / u
      have hs : s ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · have : t / u ≤ 1 := (div_le_one_of_neg hneg.2).2 hut
          linarith
        · have : 0 ≤ t / u := div_nonneg_of_nonpos hneg.1.le hneg.2.le
          linarith
      have heq : AffineMap.lineMap q x s = p := by
        rw [← hu, ← ht]
        ext i
        simp only [AffineMap.lineMap_apply_module', s]
        field_simp
        ring
      apply Set.disjoint_left.mp hPexposed hpP
      rw [← heq]
      apply (convex_convexHull ℝ _).lineMap_mem
      · exact subset_convexHull ℝ _ (Or.inl hqQ)
      · exact subset_convexHull ℝ _ (Or.inr hx)
      · exact hs
  · rcases le_total t u with htu | hut
    · have hu1 : u - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hpos.2)
      let s : ℝ := (t - 1) / (u - 1)
      have hs : s ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · exact div_nonneg (by linarith) (by linarith)
        · exact (div_le_one (by linarith)).mpr (by linarith)
      have heq : AffineMap.lineMap y q s = p := by
        rw [← hu, ← ht]
        ext i
        simp only [AffineMap.lineMap_apply_module', s]
        field_simp
        ring
      apply Set.disjoint_left.mp hPexposed hpP
      rw [← heq]
      apply (convex_convexHull ℝ _).lineMap_mem
      · exact subset_convexHull ℝ _ (Or.inr hy)
      · exact subset_convexHull ℝ _ (Or.inl hqQ)
      · exact hs
    · have ht1 : t - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hpos.1)
      let s : ℝ := (u - 1) / (t - 1)
      have hs : s ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · exact div_nonneg (by linarith) (by linarith)
        · exact (div_le_one (by linarith)).mpr (by linarith)
      have heq : AffineMap.lineMap y p s = q := by
        rw [← ht, ← hu]
        ext i
        simp only [AffineMap.lineMap_apply_module', s]
        field_simp
        ring
      apply Set.disjoint_left.mp hQexposed hqQ
      rw [← heq]
      apply (convex_convexHull ℝ _).lineMap_mem
      · exact subset_convexHull ℝ _ (Or.inr hy)
      · exact subset_convexHull ℝ _ (Or.inl hpP)
      · exact hs
/-!
The following is the literal construction.  Its two separation hypotheses
are exactly the full-cluster conclusions produced by applying Proposition
2.7 to the two alternating representative-plane patterns.  No polyhedron,
poset, free-set, or cap conclusion is assumed.
-/

/-- Pohoata--Zakharov Proposition 3.1: two alternating-block separations and
strong convex position of the support clusters produce the two trihedral
polyhedra with the containments (4.8) and the required three-object convex
position. -/
theorem pohoata_zakharov_prop_three_one {k : ℕ}
    (X : Fin k → Finset (Point 3)) (j₁ j₂ j₃ : Fin k)
    (h₁₂ : j₁ < j₂) (h₂₃ : j₂ < j₃)
    (hne : ∀ i, (X i).Nonempty)
    (htriple : NoThreeCollinear (X j₂))
    (hstrong : StrongConvexPositionClusters X)
    (hfirst : Disjoint
      (convexHull ℝ
        (↑(clusterUnion X (firstTrihedralIndices j₁ j₂ j₃)) : Set (Point 3)))
      (convexHull ℝ
        (↑(clusterUnion X
          (secondTrihedralIndices j₁ j₂ j₃ ∪ {j₂})) : Set (Point 3))))
    (hsecond : Disjoint
      (convexHull ℝ
        (↑(clusterUnion X
          (firstTrihedralIndices j₁ j₂ j₃ ∪ {j₂})) : Set (Point 3)))
      (convexHull ℝ
        (↑(clusterUnion X (secondTrihedralIndices j₁ j₂ j₃)) : Set (Point 3)))) :
    Nonempty (TrihedralClusterGadget X j₁ j₂ j₃) := by
  classical
  let I₁ := firstTrihedralIndices j₁ j₂ j₃
  let I₂ := secondTrihedralIndices j₁ j₂ j₃
  let A₀ := clusterUnion X (Finset.univ.erase j₂)
  let B₀ := X j₂
  let A₁ := clusterUnion X (I₂ ∪ {j₂})
  let B₁ := clusterUnion X I₁
  let A₂ := clusterUnion X I₂
  let B₂ := clusterUnion X (I₁ ∪ {j₂})

  have hB₀ : B₀.Nonempty := hne j₂
  have hj₃I₁ : j₃ ∈ I₁ := by
    simp [I₁, h₂₃]
  have hB₁ : B₁.Nonempty := by
    obtain ⟨x, hx⟩ := hne j₃
    exact ⟨x, by
      simp only [B₁, clusterUnion, Finset.mem_biUnion]
      exact ⟨j₃, hj₃I₁, hx⟩⟩
  have hB₂ : B₂.Nonempty := by
    obtain ⟨x, hx⟩ := hne j₂
    exact ⟨x, by
      simp only [B₂, clusterUnion, Finset.mem_biUnion]
      exact ⟨j₂, by simp, hx⟩⟩

  have hsep₀ : Disjoint (convexHull ℝ (A₀ : Set (Point 3)))
      (convexHull ℝ (B₀ : Set (Point 3))) := by
    simpa [A₀, B₀] using (hstrong j₂).symm
  have hsep₁ : Disjoint (convexHull ℝ (A₁ : Set (Point 3)))
      (convexHull ℝ (B₁ : Set (Point 3))) := by
    simpa [A₁, B₁, I₁, I₂] using hfirst.symm
  have hsep₂ : Disjoint (convexHull ℝ (A₂ : Set (Point 3)))
      (convexHull ℝ (B₂ : Set (Point 3))) := by
    simpa [A₂, B₂, I₁, I₂] using hsecond.symm

  let emptyNormals : Fin 0 → PlaneNormal := fun i => Fin.elim0 i
  let W₀ : Submodule ℝ PlaneNormal :=
    Submodule.span ℝ (Set.range emptyNormals)
  have hW₀ : W₀ ≠ ⊤ := span_planeNormals_ne_top (by omega) emptyNormals
  let C₀ := pointDifferenceConstraints B₀
  have hC₀ : ∀ L ∈ C₀, L ≠ 0 := by
    simpa [C₀] using pointDifferenceConstraints_nonzero B₀
  obtain ⟨S₀, hS₀W, hS₀C⟩ :=
    exists_strictPlaneSplit_avoiding_generic A₀ B₀ hB₀ hsep₀ W₀ hW₀ C₀ hC₀
  have hS₀inj : ∀ x ∈ B₀, ∀ y ∈ B₀, x ≠ y → S₀.normal x ≠ S₀.normal y := by
    exact realizes_pointDifferenceConstraints_iff.mp (by simpa [C₀] using hS₀C)

  let normals₁ : Fin 1 → PlaneNormal := Fin.snoc emptyNormals S₀.normal
  let W₁ : Submodule ℝ PlaneNormal :=
    Submodule.span ℝ (Set.range normals₁)
  have hW₁ : W₁ ≠ ⊤ := span_planeNormals_ne_top (by omega) normals₁
  let C₁ := pointDifferenceConstraints B₀ ∪ planarOrientationConstraints B₀ S₀.normal
  have hC₁ : ∀ L ∈ C₁, L ≠ 0 := by
    intro L hL
    rw [Finset.mem_union] at hL
    exact hL.elim (pointDifferenceConstraints_nonzero B₀ L)
      (planarOrientationConstraints_nonzero htriple hS₀inj L)
  obtain ⟨S₁, hS₁W, hS₁C⟩ :=
    exists_strictPlaneSplit_avoiding_generic A₁ B₁ hB₁ hsep₁ W₁ hW₁ C₁ hC₁
  have hS₁inj : ∀ x ∈ B₀, ∀ y ∈ B₀, x ≠ y → S₁.normal x ≠ S₁.normal y := by
    apply realizes_pointDifferenceConstraints_iff.mp
    intro L hL
    exact hS₁C L (by simp [C₁, hL])
  have hS₀S₁orient :
      ∀ x ∈ B₀, ∀ y ∈ B₀, ∀ z ∈ B₀,
        x ≠ y → y ≠ z → x ≠ z →
          (S₀.normal y - S₀.normal x) * (S₁.normal z - S₁.normal x) -
            (S₀.normal z - S₀.normal x) * (S₁.normal y - S₁.normal x) ≠ 0 := by
    apply realizes_planarOrientationConstraints_iff.mp
    intro L hL
    exact hS₁C L (by simp [C₁, hL])

  let normals₂ : Fin 2 → PlaneNormal := Fin.snoc normals₁ S₁.normal
  let W₂ : Submodule ℝ PlaneNormal :=
    Submodule.span ℝ (Set.range normals₂)
  have hW₂ : W₂ ≠ ⊤ := span_planeNormals_ne_top (by omega) normals₂
  let C₂ := pointDifferenceConstraints B₀ ∪
    (planarOrientationConstraints B₀ S₀.normal ∪
      planarOrientationConstraints B₀ S₁.normal)
  have hC₂ : ∀ L ∈ C₂, L ≠ 0 := by
    intro L hL
    simp only [C₂, Finset.mem_union] at hL
    rcases hL with hL | hL | hL
    · exact pointDifferenceConstraints_nonzero B₀ L hL
    · exact planarOrientationConstraints_nonzero htriple hS₀inj L hL
    · exact planarOrientationConstraints_nonzero htriple hS₁inj L hL
  obtain ⟨S₂, hS₂W, hS₂C⟩ :=
    exists_strictPlaneSplit_avoiding_generic A₂ B₂ hB₂ hsep₂ W₂ hW₂ C₂ hC₂
  have hS₂inj : ∀ x ∈ B₀, ∀ y ∈ B₀, x ≠ y → S₂.normal x ≠ S₂.normal y := by
    apply realizes_pointDifferenceConstraints_iff.mp
    intro L hL
    exact hS₂C L (by simp [C₂, hL])
  have hS₀S₂orient :
      ∀ x ∈ B₀, ∀ y ∈ B₀, ∀ z ∈ B₀,
        x ≠ y → y ≠ z → x ≠ z →
          (S₀.normal y - S₀.normal x) * (S₂.normal z - S₂.normal x) -
            (S₀.normal z - S₀.normal x) * (S₂.normal y - S₂.normal x) ≠ 0 := by
    apply realizes_planarOrientationConstraints_iff.mp
    intro L hL
    exact hS₂C L (by simp [C₂, hL])
  have hS₁S₂orient :
      ∀ x ∈ B₀, ∀ y ∈ B₀, ∀ z ∈ B₀,
        x ≠ y → y ≠ z → x ≠ z →
          (S₁.normal y - S₁.normal x) * (S₂.normal z - S₂.normal x) -
            (S₁.normal z - S₁.normal x) * (S₂.normal y - S₂.normal x) ≠ 0 := by
    apply realizes_planarOrientationConstraints_iff.mp
    intro L hL
    exact hS₂C L (by simp [C₂, hL])

  let normals : Fin 3 → PlaneNormal := Fin.snoc normals₂ S₂.normal
  have hempty : LinearIndependent ℝ emptyNormals := linearIndependent_empty_type
  have hnormals₁ : LinearIndependent ℝ normals₁ := by
    exact hempty.finSnoc hS₀W
  have hnormals₂ : LinearIndependent ℝ normals₂ := by
    exact hnormals₁.finSnoc hS₁W
  have hnormals : LinearIndependent ℝ normals := by
    exact hnormals₂.finSnoc hS₂W

  let signs : Fin 3 → ℝˣ := ![(1 : ℝˣ), (-1 : ℝˣ), (-1 : ℝˣ)]
  let firstNormals : Fin 3 → PlaneNormal := signs • normals
  have hfirstNormals : LinearIndependent ℝ firstNormals := by
    exact hnormals.units_smul signs
  let firstOffsets : Fin 3 → ℝ := ![S₀.low, -S₁.high, -S₂.high]
  let secondOffsets : Fin 3 → ℝ := ![S₀.low, S₁.low, S₂.low]
  let P₁ : OrientedTrihedral :=
    orientedTrihedralOfIndependentPlanes firstNormals firstOffsets hfirstNormals
  let P₂ : OrientedTrihedral :=
    orientedTrihedralOfIndependentPlanes normals secondOffsets hnormals

  have hnormals0 : normals 0 = S₀.normal := by simp [normals, normals₂, normals₁]
  have hnormals1 : normals 1 = S₁.normal := by simp [normals, normals₂, normals₁]
  have hnormals2 : normals 2 = S₂.normal := by simp [normals, normals₂, normals₁]
  have hnormalsinj : ∀ i {x y : Point 3}, x ∈ B₀ → y ∈ B₀ → x ≠ y →
      normals i x ≠ normals i y := by
    intro i x y hx hy hxy
    fin_cases i
    · simpa [hnormals0] using hS₀inj x hx y hy hxy
    · simpa [hnormals1] using hS₁inj x hx y hy hxy
    · simpa [hnormals2] using hS₂inj x hx y hy hxy
  have hnormals01 : ∀ {x y z : Point 3},
      x ∈ B₀ → y ∈ B₀ → z ∈ B₀ →
      x ≠ y → y ≠ z → x ≠ z →
        (normals 0 y - normals 0 x) * (normals 1 z - normals 1 x) -
          (normals 0 z - normals 0 x) * (normals 1 y - normals 1 x) ≠ 0 := by
    simpa [hnormals0, hnormals1] using hS₀S₁orient
  have hnormals02 : ∀ {x y z : Point 3},
      x ∈ B₀ → y ∈ B₀ → z ∈ B₀ →
      x ≠ y → y ≠ z → x ≠ z →
        (normals 0 y - normals 0 x) * (normals 2 z - normals 2 x) -
          (normals 0 z - normals 0 x) * (normals 2 y - normals 2 x) ≠ 0 := by
    simpa [hnormals0, hnormals2] using hS₀S₂orient
  have hnormals12 : ∀ {x y z : Point 3},
      x ∈ B₀ → y ∈ B₀ → z ∈ B₀ →
      x ≠ y → y ≠ z → x ≠ z →
        (normals 1 y - normals 1 x) * (normals 2 z - normals 2 x) -
          (normals 1 z - normals 1 x) * (normals 2 y - normals 2 x) ≠ 0 := by
    simpa [hnormals1, hnormals2] using hS₁S₂orient
  have hfirstNormalsinj : ∀ i {x y : Point 3}, x ∈ B₀ → y ∈ B₀ → x ≠ y →
      firstNormals i x ≠ firstNormals i y := by
    intro i x y hx hy hxy
    fin_cases i
    · simpa [firstNormals, signs] using hnormalsinj (i := 0) hx hy hxy
    · simpa [firstNormals, signs] using hnormalsinj (i := 1) hx hy hxy
    · simpa [firstNormals, signs] using hnormalsinj (i := 2) hx hy hxy
  have hfirstNormals01 : ∀ {x y z : Point 3},
      x ∈ B₀ → y ∈ B₀ → z ∈ B₀ →
      x ≠ y → y ≠ z → x ≠ z →
        (firstNormals 0 y - firstNormals 0 x) *
            (firstNormals 1 z - firstNormals 1 x) -
          (firstNormals 0 z - firstNormals 0 x) *
            (firstNormals 1 y - firstNormals 1 x) ≠ 0 := by
    intro x y z hx hy hz hxy hyz hxz hzero
    apply hnormals01 hx hy hz hxy hyz hxz
    simp [firstNormals, signs] at hzero
    nlinarith
  have hfirstNormals02 : ∀ {x y z : Point 3},
      x ∈ B₀ → y ∈ B₀ → z ∈ B₀ →
      x ≠ y → y ≠ z → x ≠ z →
        (firstNormals 0 y - firstNormals 0 x) *
            (firstNormals 2 z - firstNormals 2 x) -
          (firstNormals 0 z - firstNormals 0 x) *
            (firstNormals 2 y - firstNormals 2 x) ≠ 0 := by
    intro x y z hx hy hz hxy hyz hxz hzero
    apply hnormals02 hx hy hz hxy hyz hxz
    simp [firstNormals, signs] at hzero
    nlinarith
  have hfirstNormals12 : ∀ {x y z : Point 3},
      x ∈ B₀ → y ∈ B₀ → z ∈ B₀ →
      x ≠ y → y ≠ z → x ≠ z →
        (firstNormals 1 y - firstNormals 1 x) *
            (firstNormals 2 z - firstNormals 2 x) -
          (firstNormals 1 z - firstNormals 1 x) *
            (firstNormals 2 y - firstNormals 2 x) ≠ 0 := by
    intro x y z hx hy hz hxy hyz hxz hzero
    apply hnormals12 hx hy hz hxy hyz hxz
    simp [firstNormals, signs] at hzero
    nlinarith
  let P₁generic := genericProjectionFamilyOfIndependentPlanes
    firstNormals firstOffsets hfirstNormals B₀ hfirstNormalsinj
      hfirstNormals01 hfirstNormals02 hfirstNormals12
  let P₂generic := genericProjectionFamilyOfIndependentPlanes
    normals secondOffsets hnormals B₀ hnormalsinj
      hnormals01 hnormals02 hnormals12
  have hP₁mem (x : Point 3)
      (h₀ : S₀.normal x ≤ S₀.low)
      (h₁ : S₁.high ≤ S₁.normal x)
      (h₂ : S₂.high ≤ S₂.normal x) : x ∈ P₁.carrier := by
    rw [OrientedTrihedral.mem_carrier_iff]
    intro i
    fin_cases i
    · simpa [P₁, firstNormals, firstOffsets, signs, hnormals0]
    · simpa [P₁, firstNormals, firstOffsets, signs, hnormals1] using (neg_le_neg h₁)
    · simpa [P₁, firstNormals, firstOffsets, signs, hnormals2] using (neg_le_neg h₂)
  have hP₂mem (x : Point 3)
      (h₀ : S₀.normal x ≤ S₀.low)
      (h₁ : S₁.normal x ≤ S₁.low)
      (h₂ : S₂.normal x ≤ S₂.low) : x ∈ P₂.carrier := by
    rw [OrientedTrihedral.mem_carrier_iff]
    intro i
    fin_cases i <;>
      simp [P₂, secondOffsets, hnormals0, hnormals1, hnormals2, *]

  have hfirst_subset : (↑(clusterUnion X I₁) : Set (Point 3)) ⊆ P₁.carrier := by
    intro x hx
    have hxB₁ : x ∈ B₁ := by simpa [B₁]
    have hxB₂ : x ∈ B₂ := by
      simp only [B₂, clusterUnion, Finset.mem_biUnion]
      obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
      exact ⟨i, by simp [hi], hxi⟩
    have hxA₀ : x ∈ A₀ := by
      simp only [A₀, clusterUnion, Finset.mem_biUnion]
      obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
      have hij : i ≠ j₂ := by
        intro h
        subst i
        simp [I₁, h₁₂, h₂₃] at hi
      exact ⟨i, by simp [hij], hxi⟩
    exact hP₁mem x (S₀.left_lt_low x hxA₀).le
      (S₁.high_lt_right x hxB₁).le
      (S₂.high_lt_right x hxB₂).le
  have hsecond_subset : (↑(clusterUnion X I₂) : Set (Point 3)) ⊆ P₂.carrier := by
    intro x hx
    have hxA₁ : x ∈ A₁ := by
      simp only [A₁, clusterUnion, Finset.mem_biUnion]
      obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
      exact ⟨i, by simp [hi], hxi⟩
    have hxA₂ : x ∈ A₂ := by simpa [A₂]
    have hxA₀ : x ∈ A₀ := by
      simp only [A₀, clusterUnion, Finset.mem_biUnion]
      obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
      have hij : i ≠ j₂ := by
        intro h
        subst i
        simp [I₂, h₁₂, h₂₃] at hi
      exact ⟨i, by simp [hij], hxi⟩
    exact hP₂mem x (S₀.left_lt_low x hxA₀).le
      (S₁.left_lt_low x hxA₁).le
      (S₂.left_lt_low x hxA₂).le

  have hP₁bounds (x : Point 3) (hx : x ∈ P₁.carrier) :
      S₀.normal x ≤ S₀.low ∧
        S₁.high ≤ S₁.normal x ∧
          S₂.high ≤ S₂.normal x := by
    rw [OrientedTrihedral.mem_carrier_iff] at hx
    have h0 := hx 0
    have h1 := hx 1
    have h2 := hx 2
    simp only [P₁, orientedTrihedralOfIndependentPlanes_functional,
      firstNormals, firstOffsets, signs, Pi.smul_apply, Units.smul_def,
      hnormals0, hnormals1, hnormals2] at h0 h1 h2
    constructor
    · linarith
    · constructor <;> linarith
  have hP₂bounds (x : Point 3) (hx : x ∈ P₂.carrier) :
      S₀.normal x ≤ S₀.low ∧
        S₁.normal x ≤ S₁.low ∧
          S₂.normal x ≤ S₂.low := by
    rw [OrientedTrihedral.mem_carrier_iff] at hx
    have h0 := hx 0
    have h1 := hx 1
    have h2 := hx 2
    simp only [P₂, orientedTrihedralOfIndependentPlanes_functional,
      secondOffsets, hnormals0, hnormals1, hnormals2] at h0 h1 h2
    exact ⟨h0, h1, h2⟩
  have hM₀ (x : Point 3) (hx : x ∈ X j₂) :
      S₀.high ≤ S₀.normal x :=
    (S₀.high_lt_right x (by simpa [B₀] using hx)).le
  have hM₁ (x : Point 3) (hx : x ∈ X j₂) :
      S₁.normal x ≤ S₁.low := by
    apply (S₁.left_lt_low x ?_).le
    simp only [A₁, clusterUnion, Finset.mem_biUnion]
    exact ⟨j₂, by simp, hx⟩
  have hM₂ (x : Point 3) (hx : x ∈ X j₂) :
      S₂.high ≤ S₂.normal x := by
    apply (S₂.high_lt_right x ?_).le
    simp only [B₂, clusterUnion, Finset.mem_biUnion]
    exact ⟨j₂, by simp, hx⟩

  let M : Set (Point 3) := convexHull ℝ (↑(X j₂) : Set (Point 3))
  have hM₀hull : ∀ x ∈ M, S₀.high ≤ S₀.normal x := by
    exact convexHull_subset_plane_ge (fun x hx => hM₀ x hx)
  have hM₁hull : ∀ x ∈ M, S₁.normal x ≤ S₁.low := by
    exact convexHull_subset_plane_le (fun x hx => hM₁ x hx)
  have hM₂hull : ∀ x ∈ M, S₂.high ≤ S₂.normal x := by
    exact convexHull_subset_plane_ge (fun x hx => hM₂ x hx)

  have hconv₁ : Disjoint P₁.carrier (convexHull ℝ (P₂.carrier ∪ M)) := by
    apply disjoint_of_plane_gap S₁.low_lt_high
    · exact fun x hx => (hP₁bounds x hx).2.1
    · apply convexHull_subset_plane_le
      intro x hx
      rcases hx with hx | hx
      · exact (hP₂bounds x hx).2.1
      · exact hM₁hull x hx
  have hconv₂ : Disjoint P₂.carrier (convexHull ℝ (P₁.carrier ∪ M)) := by
    apply (disjoint_of_plane_gap S₂.low_lt_high).symm
    · apply convexHull_subset_plane_ge
      intro x hx
      rcases hx with hx | hx
      · exact (hP₁bounds x hx).2.2
      · exact hM₂hull x hx
    · exact fun x hx => (hP₂bounds x hx).2.2
  have hconvM : Disjoint M (convexHull ℝ (P₁.carrier ∪ P₂.carrier)) := by
    apply disjoint_of_plane_gap S₀.low_lt_high
    · exact hM₀hull
    · apply convexHull_subset_plane_le
      intro x hx
      exact hx.elim (fun h => (hP₁bounds x h).1) (fun h => (hP₂bounds x h).1)

  have hP₁M : Disjoint P₁.carrier M := by
    apply hconv₁.mono_right
    intro x hx
    exact subset_convexHull ℝ _ (Or.inr hx)
  have hP₂M : Disjoint P₂.carrier M := by
    apply hconv₂.mono_right
    intro x hx
    exact subset_convexHull ℝ _ (Or.inr hx)
  have hP₁ne : P₁.carrier.Nonempty := by
    obtain ⟨x, hx⟩ := hB₁
    exact ⟨x, hfirst_subset (by simpa [B₁])⟩
  have hfirstLine : ∀ {x}, x ∈ X j₂ → ∀ {y}, y ∈ X j₂ → x ≠ y →
      ¬ Disjoint (lineThrough x y) P₁.carrier →
        sourcePolytopeLE P₁.carrier x y ∨
          sourcePolytopeLE P₁.carrier y x := by
    intro x hx y hy hxy hmeet
    apply source_comparable_of_line_meets (convex_convexHull ℝ _) hP₁M
      (subset_convexHull ℝ _ hx) (subset_convexHull ℝ _ hy) hxy hmeet
  have hsecondLine : ∀ {x}, x ∈ X j₂ → ∀ {y}, y ∈ X j₂ → x ≠ y →
      (sourcePolytopeLE P₁.carrier x y ∨
        sourcePolytopeLE P₁.carrier y x) →
          Disjoint (lineThrough x y) P₂.carrier := by
    intro x hx y hy hxy hrel
    have hxM : x ∈ M := subset_convexHull ℝ _ hx
    have hyM : y ∈ M := subset_convexHull ℝ _ hy
    have hmeet : ¬ Disjoint (lineThrough x y) P₁.carrier := by
      rcases hrel with hrel | hrel
      · exact line_meets_of_sourcePolytopeLE P₁.convex_carrier hP₁ne hxy
          (Set.disjoint_left.mp hP₁M · hxM) hrel
      · have hmeet' := line_meets_of_sourcePolytopeLE
          P₁.convex_carrier hP₁ne hxy.symm
          (Set.disjoint_left.mp hP₁M · hyM) hrel
        simpa [lineThrough, Set.pair_comm] using hmeet'
    exact line_disjoint_of_two_low_exposed S₀.normal S₀.low_lt_high
      (fun p hp => (hP₁bounds p hp).1) (fun q hq => (hP₂bounds q hq).1)
      hM₀hull hconv₁ hconv₂ hxM hyM hmeet

  exact ⟨⟨P₁, P₂, by simpa [I₁], by simpa [I₂],
    ⟨hconv₁, hconv₂, hconvM⟩, hfirstLine, hsecondLine,
      by simpa [P₁generic, P₁, B₀],
      by simpa [P₂generic, P₂, B₀]⟩⟩

end

end Erdos651
