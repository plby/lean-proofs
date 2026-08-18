/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.SlabCandidateSelection
import ErdosProblems.Erdos186.PZ.Intersection.SourceAnisotropicCoreBounds

/-!
# The source coefficient control box as a convex body

The CFP reduction and the continuous PZ argument use two definitionally
separate integer-box structures.  This file gives the source control box in
the public PZ structure and proves that, when the source GAP has genuine
coordinate width, its real realization is a full-dimensional convex body.
-/

namespace Erdos186.PZ.Intersection

open Set

noncomputable section

set_option autoImplicit false

/-- The public-integer-box copy of the fixed source coefficient control box. -/
def publicControlIntegerBox {ambient d : ℕ} (Q : GAP ambient d) (m : ℕ) :
    IntegerBox d where
  lower i := -((m * (Q.widths i - 1) : ℕ) : ℤ)
  upper i := ((m * (Q.widths i - 1) : ℕ) : ℤ)

/-- The public and CFP versions of the source control box have the same
finite lattice carrier. -/
@[simp]
theorem publicControlIntegerBox_carrier {ambient d : ℕ}
    (Q : GAP ambient d) (m : ℕ) :
    (publicControlIntegerBox Q m).carrier =
      (controlIntegerBox Q m).carrier := by
  rfl

/-- The origin lies in every symmetric source control box. -/
theorem zero_mem_publicControlIntegerBox {ambient d : ℕ}
    (Q : GAP ambient d) (m : ℕ) :
    (0 : LatticePoint d) ∈ (publicControlIntegerBox Q m).carrier := by
  rw [IntegerBox.mem_carrier_iff]
  intro i
  constructor
  · change -((m * (Q.widths i - 1) : ℕ) : ℤ) ≤ 0
    exact neg_nonpos.mpr (Int.natCast_nonneg _)
  · change 0 ≤ ((m * (Q.widths i - 1) : ℕ) : ℤ)
    exact Int.natCast_nonneg _

/-- Every positive dilation of a coordinate-nondegenerate source GAP gives
a full-dimensional public convex body. -/
theorem isConvexBody_boxRealization_publicControlIntegerBox
    {ambient d : ℕ} (Q : GAP ambient d) (m : ℕ)
    (hm : 0 < m) (hwidth : ∀ i, 2 ≤ Q.widths i) :
    ConvexDensity.IsConvexBody
      (OneStepAssembly.boxRealization (publicControlIntegerBox Q m)) := by
  let lower : Fin d → ℝ := fun i ↦
    -((m * (Q.widths i - 1) : ℕ) : ℝ)
  let upper : Fin d → ℝ := fun i ↦
    ((m * (Q.widths i - 1) : ℕ) : ℝ)
  have hrealization :
      OneStepAssembly.boxRealization (publicControlIntegerBox Q m) =
        ConvexDensity.closedAxisBox lower upper := by
    ext x
    change (∀ i,
      ((-((m * (Q.widths i - 1) : ℕ) : ℤ) : ℤ) : ℝ) ≤ x.ofLp i ∧
        x.ofLp i ≤ (((m * (Q.widths i - 1) : ℕ) : ℤ) : ℝ)) ↔
      ∀ i, lower i ≤ x.ofLp i ∧ x.ofLp i ≤ upper i
    simp only [Int.cast_neg, Int.cast_natCast, lower, upper]
  rw [hrealization]
  refine ⟨ConvexDensity.convex_closedAxisBox lower upper, ?_, ?_⟩
  · rw [ConvexDensity.closedAxisBox_eq_preimage_Icc]
    exact (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin d ↦ ℝ)).toHomeomorph.isCompact_preimage.mpr isCompact_Icc
  · refine ⟨0, ?_⟩
    rw [ConvexDensity.closedAxisBox_eq_preimage_Icc]
    apply preimage_interior_subset_interior_preimage
      (PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : Fin d ↦ ℝ)).continuous
    change (0 : Fin d → ℝ) ∈ interior (Set.Icc lower upper)
    rw [← Set.pi_univ_Icc, interior_pi_set Set.finite_univ]
    intro i _hi
    have hwidthi := hwidth i
    have hwidthPos : 0 < Q.widths i - 1 := by omega
    have hprod : 0 < m * (Q.widths i - 1) :=
      Nat.mul_pos hm hwidthPos
    change (0 : ℝ) ∈ interior (Set.Icc (lower i) (upper i))
    rw [interior_Icc]
    change lower i < 0 ∧ 0 < upper i
    dsimp only [lower, upper]
    have hprodReal : (0 : ℝ) < (m * (Q.widths i - 1) : ℕ) := by
      exact_mod_cast hprod
    exact ⟨neg_lt_zero.mpr hprodReal, hprodReal⟩

end

end Erdos186.PZ.Intersection
