/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.DeterminantBounds
import ErdosProblems.Erdos186.PZ.Intersection.SideLattice
import ErdosProblems.Erdos186.StructureTheorem

/-!
# Step bounds for a progression contained in an integer box

Comparing the zero vertex with the endpoint in one progression direction
shows that `(width i - 1) * step i` fits inside the difference box.  This is
the entrywise estimate used before the weighted Bombieri--Vaaler argument.
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators

noncomputable section

set_option autoImplicit false

/-- Containment of a GAP in a translated integer box bounds each scaled step
coordinate by the corresponding box side length. -/
theorem scaled_step_abs_le_box_side {d : ℕ}
    (P : GAP d d) (B : CFP.IntegerBox d) (t : LatticePoint d)
    (hcontain : P.carrier ⊆ CFP.translate t B.carrier)
    (i j : Fin d) :
    ((P.widths i - 1 : ℕ) : ℤ) * |P.steps i j| ≤
      B.upper j - B.lower j := by
  let n : P.Coord := fun k ↦
    if hki : k = i then
      ⟨P.widths i - 1, by
        subst k
        exact Nat.sub_lt (P.width_pos i) (by omega)⟩
    else ⟨0, P.width_pos k⟩
  have hzero := hcontain (P.coordPoint_mem_carrier P.zeroCoord)
  have hn := hcontain (P.coordPoint_mem_carrier n)
  obtain ⟨b0, hb0B, hb0⟩ := CFP.mem_translate_iff.mp hzero
  obtain ⟨b1, hb1B, hb1⟩ := CFP.mem_translate_iff.mp hn
  have hb0bounds := CFP.IntegerBox.mem_carrier_iff.mp hb0B j
  have hb1bounds := CFP.IntegerBox.mem_carrier_iff.mp hb1B j
  have heq : ((P.widths i - 1 : ℕ) : ℤ) * P.steps i j =
      b1 j - b0 j := by
    have h0 := congrFun hb0 j
    have h1 := congrFun hb1 j
    have hsum0 :
        (∑ k, (P.zeroCoord k : ℤ) * P.steps k j) = 0 := by
      simp [GAP.zeroCoord]
    have hsum :
        (∑ k, (n k : ℤ) * P.steps k j) =
          ((P.widths i - 1 : ℕ) : ℤ) * P.steps i j := by
      rw [Finset.sum_eq_single i]
      · simp [n]
      · intro k _ hki
        simp [n, hki]
      · simp
    simp only [GAP.coordPoint, hsum0, add_zero, Pi.add_apply] at h0
    simp only [GAP.coordPoint, hsum, Pi.add_apply] at h1
    omega
  have habs :
      |((P.widths i - 1 : ℕ) : ℤ) * P.steps i j| ≤
        B.upper j - B.lower j := by
    rw [heq, abs_le]
    constructor <;> omega
  simpa [abs_mul] using habs

/-- Real-cast form consumed by `natAbs_det_mul_prod_le`. -/
theorem scaled_step_abs_cast_le_box_side {d : ℕ}
    (P : GAP d d) (B : CFP.IntegerBox d) (t : LatticePoint d)
    (hcontain : P.carrier ⊆ CFP.translate t B.carrier)
    (i j : Fin d) :
    ((P.widths i - 1 : ℕ) : ℝ) * |(P.steps i j : ℝ)| ≤
      ((B.upper j - B.lower j : ℤ) : ℝ) := by
  exact_mod_cast scaled_step_abs_le_box_side P B t hcontain i j

/-- Determinant/volume estimate for a square GAP in a translated integer
box.  It is deliberately stated before any lower-volume cancellation. -/
theorem stepMatrix_det_scaledVolume_le_boxVolume {d : ℕ}
    (P : GAP d d) (B : CFP.IntegerBox d) (t : LatticePoint d)
    (hcontain : P.carrier ⊆ CFP.translate t B.carrier) :
    ((stepMatrix P).det.natAbs : ℝ) *
        (∏ i, ((P.widths i - 1 : ℕ) : ℝ)) ≤
      (d.factorial : ℝ) *
        ∏ j, ((B.upper j - B.lower j : ℤ) : ℝ) := by
  apply natAbs_det_mul_prod_le (stepMatrix P)
  · intro i
    positivity
  · intro i j
    exact scaled_step_abs_cast_le_box_side P B t hcontain i j

end

end Erdos186.PZ.Intersection
