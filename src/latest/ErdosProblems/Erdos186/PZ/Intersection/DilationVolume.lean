/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.SymmetricGAP

/-!
# Quantitative growth of nondegenerate GAP dilates

For a nondegenerate GAP every displayed width is at least two, and hence
`width <= 2 * (width - 1)`.  Multiplying this elementary estimate over the
coordinates shows that replacing widths by their active lengths costs at
most `2 ^ r`.  Since the `k`-dilate has width
`k * (width - 1) + 1`, its displayed volume is consequently at least
`k ^ r / 2 ^ r` times the original volume.

This is the lower-volume half of the projection-cardinality contradiction
used to prove that the side progressions in the Pham--Zakharov intersection
argument have full-rank step lattices.
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators

noncomputable section

set_option autoImplicit false

/-- Replacing every nondegenerate width by its active length `width - 1`
loses at most a factor `2` in each coordinate. -/
theorem volume_le_two_pow_mul_prod_width_sub_one {d r : ℕ}
    (P : GAP d r) (hP : P.Nondegenerate) :
    P.volume ≤ 2 ^ r * ∏ i, (P.widths i - 1) := by
  rw [GAP.volume]
  calc
    (∏ i, P.widths i) ≤ ∏ i, (2 * (P.widths i - 1)) := by
      exact Finset.prod_le_prod (fun _i _hi ↦ Nat.zero_le _) fun i _hi ↦ by
        have hi : 2 ≤ P.widths i := hP i
        have hone : 1 ≤ P.widths i := by omega
        have hsub : P.widths i - 1 + 1 = P.widths i :=
          Nat.sub_add_cancel hone
        omega
    _ = (∏ _i : Fin r, 2) * ∏ i, (P.widths i - 1) := by
      rw [Finset.prod_mul_distrib]
    _ = 2 ^ r * ∏ i, (P.widths i - 1) := by simp

/-- The product of the active lengths, scaled by `k` in every coordinate,
is bounded by the displayed volume of the `k`-dilate. -/
theorem pow_mul_prod_width_sub_one_le_dilate_volume {d r k : ℕ}
    (P : GAP d r) :
    k ^ r * ∏ i, (P.widths i - 1) ≤ (P.dilate k).volume := by
  rw [GAP.volume]
  calc
    k ^ r * ∏ i, (P.widths i - 1) =
        ∏ i, (k * (P.widths i - 1)) := by
      calc
        k ^ r * ∏ i, (P.widths i - 1) =
            (∏ _i : Fin r, k) * ∏ i, (P.widths i - 1) := by simp
        _ = ∏ i, (k * (P.widths i - 1)) :=
          Finset.prod_mul_distrib.symm
    _ ≤ ∏ i, (P.dilate k).widths i := by
      exact Finset.prod_le_prod (fun _i _hi ↦ Nat.zero_le _) fun i _hi ↦ by
        simp only [GAP.dilate_widths]
        omega

/-- Quantitative displayed-volume growth of a nondegenerate GAP dilation.
The division-free form is convenient for exact natural-number counting. -/
theorem pow_mul_volume_le_two_pow_mul_dilate_volume {d r k : ℕ}
    (P : GAP d r) (hP : P.Nondegenerate) :
    k ^ r * P.volume ≤ 2 ^ r * (P.dilate k).volume := by
  calc
    k ^ r * P.volume ≤
        k ^ r * (2 ^ r * ∏ i, (P.widths i - 1)) :=
      Nat.mul_le_mul_left _ (volume_le_two_pow_mul_prod_width_sub_one P hP)
    _ = 2 ^ r * (k ^ r * ∏ i, (P.widths i - 1)) := by ac_rfl
    _ ≤ 2 ^ r * (P.dilate k).volume :=
      Nat.mul_le_mul_left _ (pow_mul_prod_width_sub_one_le_dilate_volume P)

/-- Actual carrier-cardinality form when the dilation is proper. -/
theorem pow_mul_volume_le_two_pow_mul_dilate_card {d r k : ℕ}
    (P : GAP d r) (hP : P.Nondegenerate) (hproper : (P.dilate k).Proper) :
    k ^ r * P.volume ≤ 2 ^ r * (P.dilate k).carrier.card := by
  rw [(P.dilate k).card_carrier_eq_volume hproper]
  exact pow_mul_volume_le_two_pow_mul_dilate_volume P hP

end

end Erdos186.PZ.Intersection
