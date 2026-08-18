/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.BadlyApproximable
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Polar separation in Bilu's Section 8

The badly-approximable system in Proposition 8.3 is chosen relative to
the polar body `B*`.  In Case 2, non-membership in `C • B*` is unpacked
as a vector of `B` whose scalar product is larger than `C`; this is the
source of equation (8.7).
-/

namespace Erdos186.CFP.Bilu.PolarSeparation

open Set
open BadlyApproximable
open scoped BigOperators Pointwise

/-- The standard Euclidean pairing on the bare coordinate function type
used by `BadlyApproximable`. -/
def euclideanPairing {n : ℕ} (x z : Fin n → ℝ) : ℝ :=
  ∑ i, x i * z i

/-- The absolute Euclidean polar of a set.  For Bilu's symmetric bodies
this agrees with the usual one-sided definition. -/
def euclideanPolar {n : ℕ} (B : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {z | ∀ x ∈ B, |euclideanPairing x z| ≤ 1}

theorem mem_euclideanPolar_iff {n : ℕ} {B : Set (Fin n → ℝ)}
    {z : Fin n → ℝ} :
    z ∈ euclideanPolar B ↔ ∀ x ∈ B, |euclideanPairing x z| ≤ 1 :=
  Iff.rfl

/-- Non-membership in a positive dilate of the polar produces the exact
strict separating inequality used by Bilu. -/
theorem exists_inner_gt_of_notMem_smul_euclideanPolar
    {n : ℕ} (B : Set (Fin n → ℝ)) {C : ℝ} (hC : 0 < C)
    {z : Fin n → ℝ} (hz : z ∉ C • euclideanPolar B) :
    ∃ x ∈ B, C < |euclideanPairing x z| := by
  have hscaled : C⁻¹ • z ∉ euclideanPolar B := by
    intro hmem
    apply hz
    refine Set.mem_smul_set.mpr ⟨C⁻¹ • z, hmem, ?_⟩
    simp [smul_smul, hC.ne']
  rw [mem_euclideanPolar_iff] at hscaled
  push Not at hscaled
  obtain ⟨x, hxB, hx⟩ := hscaled
  refine ⟨x, hxB, ?_⟩
  have hpair : euclideanPairing x (C⁻¹ • z) =
      C⁻¹ * euclideanPairing x z := by
    simp [euclideanPairing, Finset.mul_sum, mul_left_comm]
  have hscale : |euclideanPairing x (C⁻¹ • z)| =
      C⁻¹ * |euclideanPairing x z| := by
    rw [hpair, abs_mul, abs_inv, abs_of_pos hC]
  rw [hscale, inv_mul_eq_div] at hx
  simpa using (lt_div_iff₀ hC).mp hx

/-- Definition 6.7, specialized to a polar body, gives the separating
vector required in equation (8.7). -/
theorem exists_inner_gt_of_badlyApproximable
    {n r : ℕ} {B : Set (Fin n → ℝ)} {X C : ℝ}
    {a : Fin r → Fin n → ℝ}
    (ha : IsBadlyApproximable (euclideanPolar B) X C a)
    (hC : 0 < C) (x : Fin n → ℤ) (y : Fin r → ℤ)
    (hx : CoordBound X x) (hy0 : ∃ i, y i ≠ 0)
    (hy : CoordBound X y) :
    ∃ b ∈ B,
      C < |euclideanPairing b (integerCombination a y - integerPoint x)| := by
  exact exists_inner_gt_of_notMem_smul_euclideanPolar B hC
    (ha x y hx hy0 hy)

/-- Elementary last step from polar separation to the normalized form of
equation (8.7). -/
theorem two_mul_mul_lt_of_gauge_le_half
    {C gauge innerAbs : ℝ} (hC : 0 < C)
    (hgauge : 2 * gauge ≤ 1) (hinner : C < innerAbs) :
    2 * C * gauge < innerAbs := by
  calc
    2 * C * gauge = C * (2 * gauge) := by ring
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left hgauge hC.le
    _ < innerAbs := by simpa using hinner

end Erdos186.CFP.Bilu.PolarSeparation

#print axioms Erdos186.CFP.Bilu.PolarSeparation.exists_inner_gt_of_badlyApproximable
