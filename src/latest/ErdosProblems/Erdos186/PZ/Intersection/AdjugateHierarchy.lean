/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.AdjugateBounds

/-!
# Source hierarchy for displayed-step inversion

The anisotropic cofactor estimate cancels against the retained progression
volume.  The result is the exact integral coefficient capacity consumed by
`ActualStepInverse`, with no free adjugate bound.
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators

noncomputable section

set_option autoImplicit false

/-- A nondegenerate centered progression has volume at most `3^d` times
one chosen radius and the product of the other active widths. -/
theorem centered_volume_le_three_pow_mul_radius_mul_widthProductExcept
    {d : ℕ} (P : GAP d d) {radii : Fin d → ℕ}
    (hcentered : P.Centered radii) (hnondegenerate : P.Nondegenerate)
    (i : Fin d) :
    P.volume ≤ 3 ^ d * radii i * widthProductExcept P i := by
  have hradii : ∀ j, 0 < radii j :=
    hcentered.nondegenerate_iff.mp hnondegenerate
  rw [hcentered.volume_eq]
  calc
    (∏ j, (2 * radii j + 1)) ≤ ∏ j, 3 * radii j := by
      exact Finset.prod_le_prod (fun _j _hj ↦ Nat.zero_le _)
        (fun j _hj ↦ by
          have hj := hradii j
          omega)
    _ = 3 ^ d * ∏ j, radii j := by
      rw [Finset.prod_mul_distrib]
      simp
    _ = 3 ^ d * (radii i *
        ∏ j ∈ Finset.univ.erase i, radii j) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    _ ≤ 3 ^ d * (radii i * widthProductExcept P i) := by
      apply Nat.mul_le_mul_left
      apply Nat.mul_le_mul_left
      unfold widthProductExcept
      exact Finset.prod_le_prod (fun _j _hj ↦ Nat.zero_le _)
        (fun j _hj ↦ by
          rw [hcentered.width_sub_one]
          omega)
    _ = 3 ^ d * radii i * widthProductExcept P i := by ring

/-- Controlled-box and volume-retention data bound the whole adjugate column
after cancellation of the other centered widths. -/
theorem gamma_mul_sum_adjugate_le_controlled_radius
    {d ambient rank Q : ℕ}
    (P : GAP d d) (S : GAP ambient rank) (B : CFP.IntegerBox d)
    (t : LatticePoint d) {radii : Fin d → ℕ}
    (hcentered : P.Centered radii) (hnondegenerate : P.Nondegenerate)
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hcontain : P.carrier ⊆ CFP.translate t B.carrier)
    (hbox : B.carrier.card ≤ Q * S.volume)
    (hvolume : gamma * (S.volume : ℝ) ≤ (P.volume : ℝ))
    (i : Fin d) :
    gamma * (∑ j, ((stepMatrix P).adjugate j i).natAbs : ℕ) ≤
      ((d * (d.factorial * Q) * 3 ^ d : ℕ) : ℝ) * radii i := by
  let adjSum : ℕ := ∑ j, ((stepMatrix P).adjugate j i).natAbs
  let otherWidths : ℕ := widthProductExcept P i
  let coefficient : ℕ := d * (d.factorial * Q)
  have hsum : adjSum * otherWidths ≤ coefficient * S.volume := by
    calc
      adjSum * otherWidths ≤ d * (d.factorial * B.carrier.card) := by
        simpa only [adjSum, otherWidths] using
          sum_adjugate_mul_widthProductExcept_le P B t hcontain i
      _ ≤ d * (d.factorial * (Q * S.volume)) := by
        exact Nat.mul_le_mul_left d
          (Nat.mul_le_mul_left d.factorial hbox)
      _ = coefficient * S.volume := by
        simp only [coefficient]
        ring
  have hvolume' : P.volume ≤ 3 ^ d * radii i * otherWidths := by
    simpa only [otherWidths] using
      centered_volume_le_three_pow_mul_radius_mul_widthProductExcept
        P hcentered hnondegenerate i
  have hotherWidths : 0 < otherWidths := by
    simp only [otherWidths, widthProductExcept]
    exact Finset.prod_pos fun j _hj ↦ by
      rw [hcentered.width_sub_one]
      have hjpos := hcentered.nondegenerate_iff.mp hnondegenerate j
      omega
  have hgamma_nonneg : 0 ≤ gamma := le_of_lt hgamma
  have hmul :
      (gamma * (adjSum : ℝ)) * (otherWidths : ℝ) ≤
        (((coefficient * 3 ^ d : ℕ) : ℝ) * radii i) *
          (otherWidths : ℝ) := by
    calc
      (gamma * (adjSum : ℝ)) * (otherWidths : ℝ) =
          gamma * ((adjSum * otherWidths : ℕ) : ℝ) := by
        push_cast
        ring
      _ ≤ gamma * ((coefficient * S.volume : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hsum) hgamma_nonneg
      _ = (coefficient : ℝ) *
          (gamma * (S.volume : ℝ)) := by
        push_cast
        ring
      _ ≤ (coefficient : ℝ) * (P.volume : ℝ) :=
        mul_le_mul_of_nonneg_left hvolume (by positivity)
      _ ≤ (coefficient : ℝ) *
          ((3 ^ d * radii i * otherWidths : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hvolume') (by positivity)
      _ = (((coefficient * 3 ^ d : ℕ) : ℝ) * radii i) *
          (otherWidths : ℝ) := by
        push_cast
        ring
  have hotherWidthsReal : (0 : ℝ) < otherWidths := by
    exact_mod_cast hotherWidths
  have hcancel : gamma * (adjSum : ℝ) ≤
      (((coefficient * 3 ^ d : ℕ) : ℝ) * radii i) := by
    nlinarith
  simpa only [adjSum, coefficient, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat] using hcancel

/-- A scalar hierarchy dominating the controlled-box constant gives exactly
the integral inverse-coordinate capacity required by `ActualStepInverse`.
The determinant only contributes the harmless factor `1 ≤ |det|`. -/
theorem adjugate_capacity_of_controlled_box_gamma_hierarchy
    {d ambient rank Q E margin : ℕ} (hd : 0 < d) (hQ : 0 < Q)
    (P : GAP d d) (S : GAP ambient rank) (B : CFP.IntegerBox d)
    (t : LatticePoint d) {radii : Fin d → ℕ}
    (hcentered : P.Centered radii) (hnondegenerate : P.Nondegenerate)
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hcontain : P.carrier ⊆ CFP.translate t B.carrier)
    (hbox : B.carrier.card ≤ Q * S.volume)
    (hvolume : gamma * (S.volume : ℝ) ≤ (P.volume : ℝ))
    (hdet : (stepMatrix P).det ≠ 0)
    (hhierarchy :
      (E : ℝ) * ((d * (d.factorial * Q) * 3 ^ d : ℕ) : ℝ) ≤
        gamma * margin) :
    ∀ i,
      E * ∑ j, ((stepMatrix P).adjugate j i).natAbs ≤
        (stepMatrix P).det.natAbs * (margin * radii i) := by
  intro i
  let adjSum : ℕ := ∑ j, ((stepMatrix P).adjugate j i).natAbs
  let constant : ℕ := d * (d.factorial * Q) * 3 ^ d
  have hadj : gamma * (adjSum : ℝ) ≤ (constant : ℝ) * radii i := by
    simpa only [adjSum, constant] using
      gamma_mul_sum_adjugate_le_controlled_radius P S B t hcentered
        hnondegenerate gamma hgamma hcontain hbox hvolume i
  have hconstant : 0 < constant := by
    simp only [constant]
    positivity
  have hmargin : (0 : ℝ) ≤ margin := by positivity
  have hadj' := mul_le_mul_of_nonneg_right hadj hmargin
  have hsum : (0 : ℝ) ≤ adjSum := by positivity
  have hhierarchy' : (E : ℝ) * (constant : ℝ) ≤ gamma * margin := by
    simpa only [constant] using hhierarchy
  have hhierarchy'' := mul_le_mul_of_nonneg_right hhierarchy' hsum
  have hcapacityReal : (E : ℝ) * (adjSum : ℝ) ≤
      (margin : ℝ) * radii i := by
    have hconstantReal : (0 : ℝ) < constant := by
      exact_mod_cast hconstant
    have hmulCapacity :
        ((E : ℝ) * (adjSum : ℝ)) * (constant : ℝ) ≤
          (((margin : ℝ) * radii i) * (constant : ℝ)) := by
      calc
      ((E : ℝ) * (adjSum : ℝ)) * (constant : ℝ) =
          ((E : ℝ) * (constant : ℝ)) * (adjSum : ℝ) := by ring
      _ ≤ (gamma * margin) * (adjSum : ℝ) := hhierarchy''
      _ = (gamma * (adjSum : ℝ)) * margin := by ring
      _ ≤ ((constant : ℝ) * radii i) * margin := hadj'
      _ = ((margin : ℝ) * radii i) * (constant : ℝ) := by ring
    nlinarith
  have hcapacity : E * adjSum ≤ margin * radii i := by
    exact_mod_cast hcapacityReal
  calc
    E * ∑ j, ((stepMatrix P).adjugate j i).natAbs = E * adjSum := rfl
    _ ≤ margin * radii i := hcapacity
    _ = 1 * (margin * radii i) := by simp
    _ ≤ (stepMatrix P).det.natAbs * (margin * radii i) :=
      Nat.mul_le_mul_right _ (Int.natAbs_pos.mpr hdet)

end

end Erdos186.PZ.Intersection
