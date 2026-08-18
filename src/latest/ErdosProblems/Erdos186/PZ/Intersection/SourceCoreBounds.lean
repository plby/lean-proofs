/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.ProgressionContainment

/-!
# Coordinate bounds for selected side cores

Every side input is a translate of points in the reference coefficient box,
so it lies in the standard coefficient-difference GAP.  This gives a
uniform coordinate bound for every point of the selected CFP core without
introducing a new geometric hypothesis.
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators

noncomputable section

set_option autoImplicit false

/-- A convenient uniform coordinate width for the reference coefficient
box.  The sum is used rather than a maximum so the empty-rank case needs no
default convention. -/
def sourceCoordinateWidth {ambient r : ℕ} (P : GAP ambient r) : ℕ :=
  ∑ i, (P.widths i - 1)

/-- Every point of the coefficient-difference GAP is bounded coordinatewise
by the source coordinate width. -/
theorem abs_coordinate_le_sourceCoordinateWidth_of_mem_difference
    {ambient r : ℕ} (P : GAP ambient r) (z : LatticePoint r)
    (hz : z ∈ (Reduction.GAP.differenceCoefficientGAP P).carrier)
    (i : Fin r) :
    |(z i : ℝ)| ≤ (sourceCoordinateWidth P : ℝ) := by
  obtain ⟨n, hn⟩ := GAP.mem_carrier_iff.mp hz
  have hncoord := congrFun hn i
  rw [Reduction.GAP.differenceCoefficientGAP_coordPoint] at hncoord
  have hnlt := (n i).isLt
  change (n i : ℕ) < 2 * (P.widths i - 1) + 1 at hnlt
  have hi : -((P.widths i - 1 : ℕ) : ℤ) ≤ z i ∧
      z i ≤ ((P.widths i - 1 : ℕ) : ℤ) := by
    have hwidth := P.width_pos i
    rw [← hncoord]
    rw [Nat.cast_sub (by omega : 1 ≤ P.widths i)]
    push_cast at hnlt ⊢
    constructor <;> omega
  have habs : |z i| ≤ ((P.widths i - 1 : ℕ) : ℤ) := by
    simpa using (abs_le.mpr hi)
  have hterm : P.widths i - 1 ≤ sourceCoordinateWidth P := by
    unfold sourceCoordinateWidth
    exact Finset.single_le_sum
      (f := fun j : Fin r ↦ P.widths j - 1)
      (fun j _ ↦ Nat.zero_le _) (Finset.mem_univ i)
  have habs' : |z i| ≤ (sourceCoordinateWidth P : ℤ) :=
    habs.trans (by exact_mod_cast hterm)
  exact_mod_cast habs'

/-- The structured core of a CFP witness selected on a translated
coefficient candidate inherits the reference coordinate bound. -/
theorem enhancedCore_coordinateBound_of_identifiedTranslate
    {ambient r s D k loss : ℕ}
    (P : GAP ambient r) {X : Finset (LatticePoint r)}
    {x : LatticePoint r}
    (hX : X ⊆ (gapCoefficientBox P).carrier)
    (hx : x ∈ (gapCoefficientBox P).carrier)
    (W : CFP.EnhancedCFPWitness (Reduction.identifiedTranslate X x)
      s D k loss) :
    ∀ y ∈ W.core, ∀ i,
      |(y i : ℝ)| ≤ (sourceCoordinateWidth P : ℝ) := by
  have hinput : Reduction.identifiedTranslate X x ⊆
      (Reduction.GAP.differenceCoefficientGAP P).carrier := by
    exact Reduction.GAP.translate_subset_differenceCoefficientGAP P hX hx
  intro y hy i
  exact abs_coordinate_le_sourceCoordinateWidth_of_mem_difference P y
    (hinput (W.core_subset hy)) i

end

end Erdos186.PZ.Intersection
