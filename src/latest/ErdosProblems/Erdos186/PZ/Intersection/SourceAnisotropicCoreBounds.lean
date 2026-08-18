/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.CanonicalRoundingCore

/-!
# Anisotropic coordinate bounds for selected source cores

The coefficient-difference GAP remembers the width of each source
coordinate separately.  Consequently, witnesses selected on a translate
inside the source coefficient box inherit the exact coordinatewise bounds,
without replacing them by the sum of all source widths.
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

/-- Every point of the coefficient-difference GAP satisfies the exact
source bound in each coordinate. -/
theorem abs_coordinate_le_width_sub_one_of_mem_difference
    {ambient r : ℕ} (P : GAP ambient r) (z : LatticePoint r)
    (hz : z ∈ (Reduction.GAP.differenceCoefficientGAP P).carrier)
    (i : Fin r) :
    |z i| ≤ (P.widths i - 1 : ℕ) := by
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
  simpa using (abs_le.mpr hi)

/-- The enhanced core of a witness selected on a translated coefficient
candidate satisfies the exact integral source bound in every coordinate. -/
theorem enhancedCore_abs_coordinate_le_width_sub_one_of_identifiedTranslate
    {ambient r s D k loss : ℕ}
    (P : GAP ambient r) {X : Finset (LatticePoint r)}
    {x : LatticePoint r}
    (hX : X ⊆ (gapCoefficientBox P).carrier)
    (hx : x ∈ (gapCoefficientBox P).carrier)
    (W : CFP.EnhancedCFPWitness (Reduction.identifiedTranslate X x)
      s D k loss) :
    ∀ y ∈ W.core, ∀ i,
      |y i| ≤ (P.widths i - 1 : ℕ) := by
  have hinput : Reduction.identifiedTranslate X x ⊆
      (Reduction.GAP.differenceCoefficientGAP P).carrier :=
    Reduction.GAP.translate_subset_differenceCoefficientGAP P hX hx
  intro y hy i
  exact abs_coordinate_le_width_sub_one_of_mem_difference P y
    (hinput (W.core_subset hy)) i

/-- Real-valued form of the exact enhanced-core coordinate bound, ready for
anisotropic zonotope rounding. -/
theorem enhancedCore_anisotropic_coordinateBound_of_identifiedTranslate
    {ambient r s D k loss : ℕ}
    (P : GAP ambient r) {X : Finset (LatticePoint r)}
    {x : LatticePoint r}
    (hX : X ⊆ (gapCoefficientBox P).carrier)
    (hx : x ∈ (gapCoefficientBox P).carrier)
    (W : CFP.EnhancedCFPWitness (Reduction.identifiedTranslate X x)
      s D k loss) :
    ∀ y ∈ W.core, ∀ i,
      |(y i : ℝ)| ≤ ((P.widths i - 1 : ℕ) : ℝ) := by
  intro y hy i
  exact_mod_cast
    enhancedCore_abs_coordinate_le_width_sub_one_of_identifiedTranslate
      P hX hx W y hy i

/-- The canonical rounding core satisfies the exact integral source bound
coordinatewise. -/
theorem canonicalRoundingCore_abs_coordinate_le_width_sub_one_of_identifiedTranslate
    {ambient r s D k loss : ℕ}
    (P : GAP ambient r) {X : Finset (LatticePoint r)}
    {x : LatticePoint r}
    (hX : X ⊆ (gapCoefficientBox P).carrier)
    (hx : x ∈ (gapCoefficientBox P).carrier)
    (W : CFP.EnhancedCFPWitness (Reduction.identifiedTranslate X x)
      s D k loss) :
    ∀ y ∈ canonicalRoundingCore W, ∀ i,
      |y i| ≤ (P.widths i - 1 : ℕ) := by
  intro y hy i
  exact enhancedCore_abs_coordinate_le_width_sub_one_of_identifiedTranslate
    P hX hx W y (canonicalRoundingCore_subset_core W hy) i

/-- Real-valued form of the exact canonical-rounding-core coordinate bound. -/
theorem canonicalRoundingCore_anisotropic_coordinateBound_of_identifiedTranslate
    {ambient r s D k loss : ℕ}
    (P : GAP ambient r) {X : Finset (LatticePoint r)}
    {x : LatticePoint r}
    (hX : X ⊆ (gapCoefficientBox P).carrier)
    (hx : x ∈ (gapCoefficientBox P).carrier)
    (W : CFP.EnhancedCFPWitness (Reduction.identifiedTranslate X x)
      s D k loss) :
    ∀ y ∈ canonicalRoundingCore W, ∀ i,
      |(y i : ℝ)| ≤ ((P.widths i - 1 : ℕ) : ℝ) := by
  intro y hy i
  exact_mod_cast
    canonicalRoundingCore_abs_coordinate_le_width_sub_one_of_identifiedTranslate
      P hX hx W y hy i

end

end Erdos186.PZ.Intersection
