/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.SideLattice

/-!
# Bounded step relations are detected by a proper GAP dilation

Properness of a finite GAP presentation only detects relations which fit
inside its coefficient box.  This file records the exact capacity statement
used in the full-rank branch of the Pham--Zakharov intersection argument.

For a relation `z`, put its positive and negative parts in two coordinate
tuples.  If `|z i|` is smaller than the corresponding dilated width, both
tuples are admissible.  The relation makes their displayed points equal, so
properness makes the tuples equal and hence forces `z = 0`.
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators

noncomputable section

set_option autoImplicit false

/-- The positive part of an integer is bounded by its natural absolute
value. -/
theorem toNat_le_natAbs (z : ℤ) : z.toNat ≤ z.natAbs := by
  by_cases hz : 0 ≤ z
  · simpa [Int.natAbs_of_nonneg hz] using Int.toNat_of_nonneg hz
  · have hneg : z < 0 := lt_of_not_ge hz
    simp [Int.toNat_of_nonpos hneg.le]

/-- The negative part of an integer is bounded by its natural absolute
value. -/
theorem neg_toNat_le_natAbs (z : ℤ) : (-z).toNat ≤ z.natAbs := by
  rw [← Int.natAbs_neg]
  exact toNat_le_natAbs (-z)

/-- Decomposition of an integer into its natural positive and negative
parts. -/
theorem toNat_sub_neg_toNat (z : ℤ) :
    (z.toNat : ℤ) - ((-z).toNat : ℤ) = z := by
  by_cases hz : 0 ≤ z
  · simp [Int.toNat_of_nonneg hz, Int.toNat_of_nonpos (neg_nonpos.mpr hz)]
  · have hneg : z < 0 := lt_of_not_ge hz
    rw [Int.toNat_of_nonpos hneg.le, Int.toNat_of_nonneg (neg_nonneg.mpr hneg.le)]
    simp

/-- A proper GAP has no nonzero integral step relation whose positive and
negative parts both fit inside its displayed coefficient box. -/
theorem step_relation_eq_zero_of_natAbs_lt_widths
    {d r : ℕ} (P : GAP d r) (hproper : P.Proper)
    (z : Fin r → ℤ)
    (hbound : ∀ i, (z i).natAbs < P.widths i)
    (hrel : (∑ i, z i • P.steps i) = 0) :
    z = 0 := by
  let positive : P.Coord := fun i ↦
    ⟨(z i).toNat, (toNat_le_natAbs (z i)).trans_lt (hbound i)⟩
  let negative : P.Coord := fun i ↦
    ⟨(-(z i)).toNat, (neg_toNat_le_natAbs (z i)).trans_lt (hbound i)⟩
  have hpoint : P.coordPoint positive = P.coordPoint negative := by
    funext j
    have hrelj := congrFun hrel j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at hrelj
    simp only [GAP.coordPoint]
    dsimp only [positive, negative]
    have hdecomp : ∀ i,
        ((z i).toNat : ℤ) = z i + ((-(z i)).toNat : ℤ) := by
      intro i
      have hi := toNat_sub_neg_toNat (z i)
      omega
    simp_rw [hdecomp]
    simp only [add_mul]
    rw [Finset.sum_add_distrib]
    rw [hrelj]
    simp
  have hcoord : positive = negative := hproper hpoint
  funext i
  have hi := congrArg (fun n : P.Coord ↦ (n i : ℕ)) hcoord
  change (z i).toNat = (-(z i)).toNat at hi
  have hdecomp := toNat_sub_neg_toNat (z i)
  rw [hi] at hdecomp
  simpa using hdecomp.symm

/-- Capacity form for a positive dilation: a step relation bounded by
`k * (width i - 1)` is zero. -/
theorem step_relation_eq_zero_of_dilate_proper
    {d r k : ℕ} (P : GAP d r) (hproper : (P.dilate k).Proper)
    (z : Fin r → ℤ)
    (hbound : ∀ i, (z i).natAbs ≤ k * (P.widths i - 1))
    (hrel : (∑ i, z i • P.steps i) = 0) :
    z = 0 := by
  apply step_relation_eq_zero_of_natAbs_lt_widths (P.dilate k) hproper z
  · intro i
    simpa only [GAP.dilate_widths] using Nat.lt_succ_of_le (hbound i)
  · simpa only [GAP.dilate_steps] using hrel

/-- A bounded nonzero step relation contradicts properness of the indicated
dilation.  This is the direct interface consumed by a quantitative
determinant-kernel estimate. -/
theorem not_dilate_proper_of_nonzero_bounded_step_relation
    {d r k : ℕ} (P : GAP d r) (z : Fin r → ℤ)
    (hz : z ≠ 0)
    (hbound : ∀ i, (z i).natAbs ≤ k * (P.widths i - 1))
    (hrel : (∑ i, z i • P.steps i) = 0) :
    ¬ (P.dilate k).Proper := by
  intro hproper
  exact hz (step_relation_eq_zero_of_dilate_proper P hproper z hbound hrel)

/-- Determinant wrapper for the square-step case.  Any quantitative kernel
construction that supplies a bounded nonzero integral relation when the
step matrix is singular can feed this theorem directly. -/
theorem det_ne_zero_of_bounded_step_relation
    {d k : ℕ} (P : GAP d d) (hproper : (P.dilate k).Proper)
    (hkernel : (stepMatrix P).det = 0 →
      ∃ z : Fin d → ℤ,
        z ≠ 0 ∧
        (∑ i, z i • P.steps i) = 0 ∧
        ∀ i, (z i).natAbs ≤ k * (P.widths i - 1)) :
    (stepMatrix P).det ≠ 0 := by
  intro hdet
  obtain ⟨z, hz, hrel, hbound⟩ := hkernel hdet
  exact hz (step_relation_eq_zero_of_dilate_proper P hproper z hbound hrel)

end

end Erdos186.PZ.Intersection
