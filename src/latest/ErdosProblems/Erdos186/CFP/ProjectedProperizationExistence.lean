/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.ProjectedProperization
import ErdosProblems.Erdos186.CFP.HDimension
import ErdosProblems.Erdos186.CFP.Bilu.Section92ShortKernel

/-!
# Existence lemmas for projected properization

This module contains the geometric part of the Appendix projection step.
The bookkeeping which transports an existing fixed-scale witness is kept in
`ProjectedProperization`.
-/

namespace Erdos186.CFP.ProjectedProperization

open scoped BigOperators
open NoCarryEmbedding

noncomputable section

/-! ## The rank-one kernel of box dehomogenization -/

/-- The primitive generator of the kernel of box dehomogenization.  Its
leading coordinate is one, so no separate content/gcd normalization is
needed. -/
def boxKernelGenerator {d : ℕ} (B : IntegerBox d) :
    LatticePoint (d + 1) :=
  Fin.cases 1 fun i ↦ -B.lower i

@[simp]
theorem boxKernelGenerator_zero {d : ℕ} (B : IntegerBox d) :
    boxKernelGenerator B 0 = 1 :=
  rfl

@[simp]
theorem boxKernelGenerator_succ {d : ℕ} (B : IntegerBox d)
    (i : Fin d) :
    boxKernelGenerator B i.succ = -B.lower i := by
  simp [boxKernelGenerator]

@[simp]
theorem boxDehomogenizeHom_boxKernelGenerator {d : ℕ}
    (B : IntegerBox d) :
    AppendixEncoding.boxDehomogenizeHom B (boxKernelGenerator B) = 0 := by
  ext i
  simp [AppendixEncoding.boxDehomogenizeHom, boxKernelGenerator]

/-- Every integral vector killed by box dehomogenization is the multiple,
specified by its leading coordinate, of the canonical primitive kernel
generator. -/
theorem eq_zero_apply_smul_boxKernelGenerator_of_boxDehomogenize_eq_zero
    {d : ℕ} (B : IntegerBox d) (y : LatticePoint (d + 1))
    (hy : AppendixEncoding.boxDehomogenizeHom B y = 0) :
    y = y 0 • boxKernelGenerator B := by
  funext j
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · simp
  · have hi := congrFun hy i
    simp only [AppendixEncoding.boxDehomogenizeHom, AddMonoidHom.coe_mk,
      ZeroHom.coe_mk, Pi.zero_apply] at hi
    simp only [Pi.smul_apply, smul_eq_mul, boxKernelGenerator_succ]
    linear_combination hi

/-- A projected collision in a proper source GAP cannot disappear in the
source.  For box dehomogenization its difference is therefore a nonzero
multiple of the single primitive kernel direction. -/
structure BoxProjectedCollision {d r k : ℕ}
    (B : IntegerBox d) (P : GAP (d + 1) r) where
  left : (P.dilate k).Coord
  right : (P.dilate k).Coord
  distinct : left ≠ right
  projected_eq :
    AppendixEncoding.boxDehomogenizeHom B
        ((P.dilate k).coordPoint left) =
      AppendixEncoding.boxDehomogenizeHom B
        ((P.dilate k).coordPoint right)
  sourceDifference : LatticePoint (d + 1)
  sourceDifference_eq :
    sourceDifference =
      (P.dilate k).coordPoint left - (P.dilate k).coordPoint right
  sourceDifference_ne_zero : sourceDifference ≠ 0
  sourceDifference_kernel :
    sourceDifference =
      sourceDifference 0 • boxKernelGenerator B
  leading_ne_zero : sourceDifference 0 ≠ 0

/-- Failure of projected properness, together with properness before
projection, produces the canonical nonzero rank-one-kernel collision
certificate. -/
theorem exists_boxProjectedCollision_of_not_proper
    {d r k : ℕ} (B : IntegerBox d) (P : GAP (d + 1) r)
    (hsource : (P.dilate k).Proper)
    (hprojected : ¬
      (mapGAP (AppendixEncoding.boxDehomogenizeHom B) P |>.dilate k).Proper) :
    Nonempty (BoxProjectedCollision (k := k) B P) := by
  have hmap :
      (mapGAP (AppendixEncoding.boxDehomogenizeHom B) P).dilate k =
        mapGAP (AppendixEncoding.boxDehomogenizeHom B) (P.dilate k) := by
    exact (mapGAP_dilate _ _ _).symm
  rw [hmap, GAP.Proper, Function.Injective] at hprojected
  push Not at hprojected
  obtain ⟨a, b, hab, hne⟩ := hprojected
  let x := (P.dilate k).coordPoint a
  let y := (P.dilate k).coordPoint b
  let q := x - y
  have hxy : x ≠ y := by
    intro h
    exact hne (hsource h)
  have hq0 : q ≠ 0 := sub_ne_zero.mpr hxy
  have hqMap : AppendixEncoding.boxDehomogenizeHom B q = 0 := by
    dsimp only [q]
    rw [map_sub]
    have hmapped :
        AppendixEncoding.boxDehomogenizeHom B x =
          AppendixEncoding.boxDehomogenizeHom B y := by
      simpa only [x, y, mapGAP_coordPoint] using hab
    rw [hmapped, sub_self]
  have hqKernel : q = q 0 • boxKernelGenerator B :=
    eq_zero_apply_smul_boxKernelGenerator_of_boxDehomogenize_eq_zero B q hqMap
  have hqLeading : q 0 ≠ 0 := by
    intro hzero
    apply hq0
    rw [hqKernel, hzero, zero_smul]
  exact ⟨{
    left := a
    right := b
    distinct := hne
    projected_eq := by
      simpa only [x, y, mapGAP_coordPoint] using hab
    sourceDifference := q
    sourceDifference_eq := rfl
    sourceDifference_ne_zero := hq0
    sourceDifference_kernel := hqKernel
    leading_ne_zero := hqLeading }⟩

/-! ## Coefficient-lattice rank descent -/

/-- The coefficient boxes of a GAP and its image are canonically the same,
although their dependent `Coord` types are not definitionally equal. -/
def castMapGAPCoord {d e r : ℕ}
    (f : LatticePoint d →+ LatticePoint e) (P : GAP d r)
    (n : P.Coord) : (mapGAP f P).Coord :=
  fun i ↦ ⟨n i, by simpa [mapGAP] using (n i).isLt⟩

@[simp]
theorem castMapGAPCoord_apply {d e r : ℕ}
    (f : LatticePoint d →+ LatticePoint e) (P : GAP d r)
    (n : P.Coord) (i : Fin r) :
    (castMapGAPCoord f P n i : ℕ) = n i :=
  rfl

@[simp]
theorem mapGAP_coordPoint_castMapGAPCoord {d e r : ℕ}
    (f : LatticePoint d →+ LatticePoint e) (P : GAP d r)
    (n : P.Coord) :
    (mapGAP f P).coordPoint (castMapGAPCoord f P n) =
      f (P.coordPoint n) := by
  exact mapGAP_coordPoint f P (castMapGAPCoord f P n)

/-- The additive homomorphism which evaluates an integral coefficient tuple
against a tuple of lattice vectors. -/
def stepCombinationHom {d r : ℕ} (steps : Fin r → LatticePoint d) :
    LatticePoint r →+ LatticePoint d where
  toFun := fun z j ↦ ∑ i, z i * steps i j
  map_zero' := by
    funext j
    simp
  map_add' x y := by
    funext j
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

@[simp]
theorem stepCombinationHom_apply {d r : ℕ}
    (steps : Fin r → LatticePoint d) (z : LatticePoint r) :
    stepCombinationHom steps z = fun j ↦ ∑ i, z i * steps i j :=
  rfl

/-- Difference of the two coefficient tuples in a projected collision. -/
def BoxProjectedCollision.coefficientDifference
    {d r k : ℕ} {B : IntegerBox d} {P : GAP (d + 1) r}
    (C : BoxProjectedCollision (k := k) B P) : LatticePoint r :=
  fun i ↦ (C.left i : ℤ) - (C.right i : ℤ)

theorem BoxProjectedCollision.coefficientDifference_ne_zero
    {d r k : ℕ} {B : IntegerBox d} {P : GAP (d + 1) r}
    (C : BoxProjectedCollision (k := k) B P) :
    C.coefficientDifference ≠ 0 := by
  intro hzero
  apply C.distinct
  funext i
  apply Fin.ext
  have hi := congrFun hzero i
  simp only [coefficientDifference, Pi.zero_apply] at hi
  exact_mod_cast sub_eq_zero.mp hi

/-- The coefficient difference is a genuine relation among the projected
steps. -/
theorem BoxProjectedCollision.coefficientDifference_mem_ker
    {d r k : ℕ} {B : IntegerBox d} {P : GAP (d + 1) r}
    (C : BoxProjectedCollision (k := k) B P) :
    stepCombinationHom
        (mapGAP (AppendixEncoding.boxDehomogenizeHom B) P).steps
        C.coefficientDifference = 0 := by
  let Q := mapGAP (AppendixEncoding.boxDehomogenizeHom B) P
  have hpoint :
      (mapGAP (AppendixEncoding.boxDehomogenizeHom B)
          (P.dilate k)).coordPoint
            (castMapGAPCoord (AppendixEncoding.boxDehomogenizeHom B)
              (P.dilate k) C.left) =
        (mapGAP (AppendixEncoding.boxDehomogenizeHom B)
          (P.dilate k)).coordPoint
            (castMapGAPCoord (AppendixEncoding.boxDehomogenizeHom B)
              (P.dilate k) C.right) := by
    rw [mapGAP_coordPoint_castMapGAPCoord,
      mapGAP_coordPoint_castMapGAPCoord]
    exact C.projected_eq
  change (fun j ↦ ∑ i, C.coefficientDifference i * Q.steps i j) = 0
  funext j
  have hj := congrFun hpoint j
  simp only [GAP.coordPoint, GAP.dilate_offset, GAP.dilate_steps, mapGAP,
    Pi.add_apply, castMapGAPCoord_apply] at hj
  simp only [coefficientDifference, sub_mul, Finset.sum_sub_distrib,
    Pi.zero_apply, Q, mapGAP]
  linear_combination hj

/-- A projected collision supplies the exact primitive quotient data used
for one strict coefficient-rank drop. -/
theorem BoxProjectedCollision.exists_primitiveIntegralQuotient
    {d r k : ℕ} {B : IntegerBox d} {P : GAP (d + 1) r}
    (C : BoxProjectedCollision (k := k) B P) :
    Nonempty
      (Bilu.Section92ShortKernel.PrimitiveIntegralQuotient
        (stepCombinationHom
          (mapGAP (AppendixEncoding.boxDehomogenizeHom B) P).steps)
        C.coefficientDifference) := by
  apply Bilu.Section92ShortKernel.exists_primitiveIntegralQuotient
  · exact C.coefficientDifference_ne_zero
  · exact C.coefficientDifference_mem_ker

/-! ## The collision-free branch -/

/-- An additive homomorphism commutes with an integral combination of a
finite tuple of lattice vectors. -/
theorem map_stepCombination {d e r : ℕ}
    (f : LatticePoint d →+ LatticePoint e)
    (steps : Fin r → LatticePoint d) (z : Fin r → ℤ) :
    f (fun j ↦ ∑ i, z i * steps i j) =
      fun j ↦ ∑ i, z i * f (steps i) j := by
  have hsource : (fun j ↦ ∑ i, z i * steps i j) =
      ∑ i, z i • steps i := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsource, map_sum]
  simp only [map_zsmul]
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- Mapping a centered presentation through an additive homomorphism
preserves its centered coefficient box. -/
theorem mapGAP_centered {d e r : ℕ}
    (f : LatticePoint d →+ LatticePoint e) (P : GAP d r)
    {radii : Fin r → ℕ} (hP : P.Centered radii) :
    (mapGAP f P).Centered radii := by
  constructor
  · exact hP.widths_eq
  · change f P.offset =
      fun j ↦ -∑ i, (radii i : ℤ) * f (P.steps i) j
    rw [hP.offset_eq]
    calc
      f (fun j ↦ -∑ i, (radii i : ℤ) * P.steps i j) =
          f (fun j ↦ ∑ i, (-(radii i : ℤ)) * P.steps i j) := by
            congr 1
            funext j
            simp only [neg_mul, Finset.sum_neg_distrib]
      _ = (fun j ↦ ∑ i, (-(radii i : ℤ)) * f (P.steps i) j) :=
        map_stepCombination f P.steps fun i ↦ -(radii i : ℤ)
      _ = fun j ↦ -∑ i, (radii i : ℤ) * f (P.steps i) j := by
        funext j
        simp only [neg_mul, Finset.sum_neg_distrib]

/-- If the projection is injective on the covered dilation, no rank drop is
needed: the mapped GAP itself is the projected-properization output. -/
noncomputable def dataOfInjOnDilate
    {d e s D k loss : ℕ} {H : Finset (LatticePoint d)}
    (f : LatticePoint d →+ LatticePoint e)
    (W : EnhancedCFPWitness H s D k loss)
    (hinjective : Set.InjOn f (W.progression.dilate k).carrier) :
    Data (factor := 1) f W := by
  let Q := mapGAP f W.progression
  have hQk : (Q.dilate k).Proper := by
    rw [← mapGAP_dilate]
    exact mapGAP_proper_of_injOn_carrier f (W.progression.dilate k)
      W.dilate_proper hinjective
  have hQ : Q.Proper := by
    exact GAP.SProper.proper (Q.sProper_of_dilate_proper k hQk)
      (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt W.k_pos))
  let radii := Classical.choose W.progression_symmetric
  have hcentered : W.progression.Centered radii :=
    Classical.choose_spec W.progression_symmetric
  have hQcentered : Q.Centered radii := mapGAP_centered f W.progression hcentered
  refine
    { scale := k
      scale_pos := W.k_pos
      scale_le_source := le_rfl
      source_le_factor_mul_scale := by simp
      rank := W.rank
      rank_le := le_rfl
      progression := Q
      progression_proper := hQ
      dilate_proper := hQk
      progression_symmetric := ⟨radii, hQcentered⟩
      progression_nondegenerate := ?_
      homogeneous := hQcentered.homogeneous
      base_image_subset := ?_
      translatePoint := f W.translatePoint
      covered_subset := ?_
      covered_translate_homogeneous := ?_ }
  · intro i
    exact W.progression_nondegenerate i
  · rw [← mapGAP_carrier]
  · dsimp only [Q]
    rw [← mapGAP_dilate]
  · obtain ⟨z, hz⟩ := W.covered_translate_homogeneous
    refine ⟨z, ?_⟩
    have hmapped := congrArg f hz
    rw [map_add] at hmapped
    have hoff := congrArg GAP.offset
      (mapGAP_dilate f W.progression k)
    change f (W.progression.dilate k).offset =
      (Q.dilate k).offset at hoff
    rw [hoff, map_stepCombination f W.progression.steps z] at hmapped
    exact hmapped

/-- Collision-free properization at any advertised factor at least one.
This is the terminal branch used after selecting a single factor uniformly
in the source rank bound. -/
noncomputable def dataOfInjOnDilateWithFactor
    {d e s D k loss factor : ℕ} {H : Finset (LatticePoint d)}
    (f : LatticePoint d →+ LatticePoint e)
    (W : EnhancedCFPWitness H s D k loss)
    (hfactor : 0 < factor)
    (hinjective : Set.InjOn f (W.progression.dilate k).carrier) :
    Data (factor := factor) f W :=
  (dataOfInjOnDilate f W hinjective).monoFactor
    (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hfactor))

end

end Erdos186.CFP.ProjectedProperization

#print axioms Erdos186.CFP.ProjectedProperization.dataOfInjOnDilate
#print axioms Erdos186.CFP.ProjectedProperization.dataOfInjOnDilateWithFactor
