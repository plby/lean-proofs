/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Proposition75Case2Branch
import ErdosProblems.Erdos186.CFP.Bilu.Section8PresentationNormalization

/-!
# Geometry of the normalized Proposition 7.5 section

This file records the elementary balanced, convex, compact, and interior
properties of `coordinateB0`.  They are the source-independent input for
the sharp Section 9.1 gauge construction.
-/

namespace Erdos186.CFP.Bilu.Section91CoordinateBodyGeometry

open scoped Pointwise RealInnerProductSpace
open Set Module
open CFP.BiluFreiman
open Proposition75Data Proposition75Case2 Proposition75Case2Branch
open Section8PresentationNormalization Section92PresentationDescent

noncomputable section

set_option autoImplicit false

/-- The distortion body is balanced when its head body is balanced. -/
theorem balanced_distortionBody {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    (hB : Balanced ℝ B)
    (a : Fin r → EuclideanSpace ℝ (Fin m)) :
    Balanced ℝ (distortionBody B a) := by
  apply balanced_iff_smul_mem.mpr
  intro c hc z hz
  rw [mem_distortionBody] at hz ⊢
  constructor
  · exact (hB.smul (2 : ℝ)).smul_mem hc hz.1
  · intro i
    change |⟪(WithLp.ofLp (c • z)).1, a i⟫ -
      (WithLp.ofLp (c • z)).2 i| ≤ 1
    rw [WithLp.ofLp_smul]
    simp only [Prod.smul_fst, Prod.smul_snd, WithLp.ofLp_smul,
      Pi.smul_apply, smul_eq_mul, inner_smul_left]
    change |c * ⟪head z, a i⟫ - c * tail z i| ≤ 1
    rw [← mul_sub, abs_mul]
    have hcabs : |c| ≤ 1 := by
      simpa [Real.norm_eq_abs] using hc
    calc
      |c| * |⟪head z, a i⟫ - tail z i| ≤ 1 * 1 := by
        exact mul_le_mul hcabs (hz.2 i) (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num

/-- The intrinsic section inherits balancedness from the distortion body. -/
theorem balanced_B0 {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    (hB : Balanced ℝ B)
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a) :
    Balanced ℝ D.B0 := by
  apply balanced_iff_smul_mem.mpr
  intro c hc z hz
  change ((c • z : D.C0) : Ambient m r) ∈ distortionBody B a
  change c • (z : Ambient m r) ∈ distortionBody B a
  exact (balanced_distortionBody hB a).smul_mem hc hz

/-- The canonical coordinate copy of the intrinsic section is balanced. -/
theorem balanced_coordinateB0 {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    (hB : Balanced ℝ B)
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a) :
    Balanced ℝ (coordinateB0 D) := by
  apply balanced_iff_smul_mem.mpr
  intro c hc z hz
  obtain ⟨x, hx, rfl⟩ := hz
  refine ⟨c • x, (balanced_B0 hB D).smul_mem hc hx, ?_⟩
  exact map_smul (coordinateC0Equiv D) c x

/-- Convexity of the intrinsic section. -/
theorem convex_B0 {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    (hB : Convex ℝ B)
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a) :
    Convex ℝ D.B0 := by
  exact (convex_distortionBody hB a).linear_preimage D.C0.subtype

/-- Convexity is preserved by the canonical coordinate identification. -/
theorem convex_coordinateB0 {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    (hB : Convex ℝ B)
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a) :
    Convex ℝ (coordinateB0 D) := by
  exact (convex_B0 hB D).linear_image (coordinateC0Equiv D).toLinearMap

/-- Compactness of the intrinsic section. -/
theorem isCompact_B0 {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    (hB : IsCompact B)
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a) :
    IsCompact D.B0 := by
  have hclosed : IsClosed (D.C0 : Set (Ambient m r)) := by
    rw [← D.C0.orthogonal_orthogonal]
    exact D.C0.orthogonal.isClosed_orthogonal
  change IsCompact (D.C0.subtype ⁻¹' distortionBody B a)
  exact (D.C0.isClosedEmbedding_subtype hclosed).isCompact_preimage
    (isCompact_distortionBody hB a)

/-- Compactness is preserved by the canonical coordinate identification. -/
theorem isCompact_coordinateB0 {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    (hB : IsCompact B)
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a) :
    IsCompact (coordinateB0 D) := by
  exact (isCompact_B0 hB D).image (coordinateC0Equiv D).continuous

/-- The section spans its intrinsic space even after forgetting the lattice
condition in `GeometricData.spans`. -/
theorem span_B0_eq_top {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a) :
    Submodule.span ℝ D.B0 = ⊤ := by
  apply top_unique
  rw [← D.spans]
  exact Submodule.span_mono inter_subset_left

/-- The coordinate section spans the whole coordinate subspace. -/
theorem span_coordinateB0_eq_top {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a) :
    Submodule.span ℝ (coordinateB0 D) = ⊤ := by
  have h := congrArg
    (fun L : Submodule ℝ D.C0 ↦
      L.map (coordinateC0Equiv D).toLinearMap) (span_B0_eq_top D)
  rw [Submodule.map_span] at h
  simpa [coordinateB0] using h

/-- A balanced nonempty source body puts the origin in its coordinate
section. -/
theorem zero_mem_coordinateB0 {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    (hB : Balanced ℝ B) (hBne : B.Nonempty)
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a) :
    (0 : coordinateC0 D) ∈ coordinateB0 D := by
  have hzeroB : (0 : EuclideanSpace ℝ (Fin m)) ∈ B := hB.zero_mem hBne
  have hzeroOmega : (0 : Ambient m r) ∈ distortionBody B a := by
    rw [mem_distortionBody]
    constructor
    · exact ⟨0, hzeroB, by simp⟩
    · simp
  refine ⟨0, hzeroOmega, ?_⟩
  exact map_zero (coordinateC0Equiv D)

/-- The full-dimensional balanced convex coordinate section contains the
origin in its interior. -/
theorem zero_mem_interior_coordinateB0 {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    (hbalanced : Balanced ℝ B) (hconvex : Convex ℝ B)
    (hBne : B.Nonempty)
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a) :
    (0 : coordinateC0 D) ∈ interior (coordinateB0 D) := by
  have hzero := zero_mem_coordinateB0 hbalanced hBne D
  have hvector : vectorSpan ℝ (coordinateB0 D) = ⊤ := by
    rw [vectorSpan_eq_span_vsub_set_right ℝ hzero]
    simpa using span_coordinateB0_eq_top D
  have haff : affineSpan ℝ (coordinateB0 D) = ⊤ := by
    apply (AffineSubspace.direction_eq_top_iff_of_nonempty
      ⟨0, subset_affineSpan ℝ (coordinateB0 D) hzero⟩).mp
    simpa only [direction_affineSpan] using hvector
  have hconv := convex_coordinateB0 hconvex D
  obtain ⟨x, hx⟩ :=
    hconv.interior_nonempty_iff_affineSpan_eq_top.mpr haff
  have hneg : -x ∈ coordinateB0 D :=
    (balanced_coordinateB0 hbalanced D).neg_mem_iff.mpr
      (interior_subset hx)
  have hmid := hconv.add_smul_sub_mem_interior hneg hx
    (show (1 / 2 : ℝ) ∈ Set.Ioc 0 1 by norm_num)
  convert hmid using 1 <;> module

/-! Specializations to the normalized body used by the presentation
replacement. -/

theorem balanced_normalized_coordinateB0 {A : Finset ℤ}
    (X : RankedBodyPresentation A) {r : ℕ}
    {a : Fin r → EuclideanSpace ℝ (Fin X.1)}
    (D : GeometricData (normalizedEuclideanBody X) a) :
    Balanced ℝ (coordinateB0 D) :=
  balanced_coordinateB0 (balanced_normalizedEuclideanBody X) D

theorem convex_normalized_coordinateB0 {A : Finset ℤ}
    (X : RankedBodyPresentation A) {r : ℕ}
    {a : Fin r → EuclideanSpace ℝ (Fin X.1)}
    (D : GeometricData (normalizedEuclideanBody X) a) :
    Convex ℝ (coordinateB0 D) :=
  convex_coordinateB0 (convex_normalizedEuclideanBody X) D

theorem isCompact_normalized_coordinateB0 {A : Finset ℤ}
    (X : RankedBodyPresentation A) {r : ℕ}
    {a : Fin r → EuclideanSpace ℝ (Fin X.1)}
    (D : GeometricData (normalizedEuclideanBody X) a) :
    IsCompact (coordinateB0 D) :=
  isCompact_coordinateB0 (isCompact_normalizedEuclideanBody X) D

theorem zero_mem_interior_normalized_coordinateB0 {A : Finset ℤ}
    (X : RankedBodyPresentation A) {r : ℕ}
    {a : Fin r → EuclideanSpace ℝ (Fin X.1)}
    (D : GeometricData (normalizedEuclideanBody X) a) :
    (0 : coordinateC0 D) ∈ interior (coordinateB0 D) := by
  apply zero_mem_interior_coordinateB0
    (balanced_normalizedEuclideanBody X)
    (convex_normalizedEuclideanBody X)
  refine ⟨0, ?_⟩
  rw [normalizedEuclideanBody, Seminorm.mem_closedBall]
  simp

end

end Erdos186.CFP.Bilu.Section91CoordinateBodyGeometry

#print axioms
  Erdos186.CFP.Bilu.Section91CoordinateBodyGeometry.zero_mem_interior_normalized_coordinateB0
#print axioms
  Erdos186.CFP.Bilu.Section91CoordinateBodyGeometry.isCompact_normalized_coordinateB0
