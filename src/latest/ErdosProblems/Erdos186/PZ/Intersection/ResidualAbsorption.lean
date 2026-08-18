/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.Equation15
import ErdosProblems.Erdos186.Zonotope

/-!
# Turning zonotope rounding into residual absorption

This is the formal bridge between the rounding lemma and the residual-error
predicate used in equation (15).  The only geometric input left to a caller
is that every integer vector in the coordinate error box belongs to the CFP
error progression.
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators

noncomputable section

set_option autoImplicit false

/-- If each target lattice point lies in the zonotope of `core`, and the
coordinate error box produced by rounding is contained in `errors`, then the
target has the exact residual-absorption property needed by equation (15). -/
theorem roundingErrorsAbsorbedBy_of_zonotope {d : ℕ}
    (target core errors : Finset (LatticePoint d)) (width : ℝ)
    (hwidth : 0 ≤ width)
    (hcore : ∀ x ∈ core, ∀ i, |(x i : ℝ)| ≤ width)
    (htarget : ∀ z ∈ target,
      Zonotope.IsZonotopePoint core (fun i ↦ (z i : ℝ)))
    (herrors : ∀ e : LatticePoint d,
      (∀ i, |(e i : ℝ)| ≤
        Real.sqrt (((d * core.card : ℕ) : ℝ)) * width) →
      e ∈ errors) :
    RoundingErrorsAbsorbedBy target core errors := by
  intro z hz
  obtain ⟨T, hTcore, hTerror⟩ :=
    Zonotope.zonotope_rounding core (fun i ↦ (z i : ℝ)) width
      (htarget z hz) hwidth hcore
  refine ⟨T, hTcore, herrors (z - ∑ x ∈ T, x) ?_⟩
  intro i
  simpa [Finset.sum_apply] using hTerror i

/-- Minkowski-sum version of `roundingErrorsAbsorbedBy_of_zonotope`.

This is the form occurring in equation (15): a target point is first split
as a point of a structured progression plus an *integral* point of the
rounding zonotope.  Rounding the latter leaves a small coordinate error;
the sole remaining numerical obligation is that adding such an error to a
structured point stays in the larger error progression. -/
theorem roundingErrorsAbsorbedBy_of_zonotope_add {d : ℕ}
    (target core structured errors : Finset (LatticePoint d)) (width : ℝ)
    (hwidth : 0 ≤ width)
    (hcore : ∀ x ∈ core, ∀ i, |(x i : ℝ)| ≤ width)
    (htarget : ∀ z ∈ target, ∃ p ∈ structured,
      ∃ x : LatticePoint d,
        Zonotope.IsZonotopePoint core (fun i ↦ (x i : ℝ)) ∧ z = p + x)
    (habsorb : ∀ p ∈ structured, ∀ e : LatticePoint d,
      (∀ i, |(e i : ℝ)| ≤
        Real.sqrt (((d * core.card : ℕ) : ℝ)) * width) →
      p + e ∈ errors) :
    RoundingErrorsAbsorbedBy target core errors := by
  intro z hz
  obtain ⟨p, hp, x, hx, rfl⟩ := htarget z hz
  obtain ⟨T, hTcore, hTerror⟩ :=
    Zonotope.zonotope_rounding core (fun i ↦ (x i : ℝ)) width hx
      hwidth hcore
  refine ⟨T, hTcore, ?_⟩
  rw [add_sub_assoc]
  apply habsorb p hp
  intro i
  simpa [Finset.sum_apply] using hTerror i

/-- A version where the CFP progression is supplied directly as the error
set.  This is the precise numerical obligation in Lemma 13. -/
theorem roundingErrorsAbsorbedBy_cfpTranslate {d r k : ℕ}
    (target core : Finset (LatticePoint d)) (width : ℝ)
    (P : GAP d r) (translatePoint : LatticePoint d)
    (hwidth : 0 ≤ width)
    (hcore : ∀ x ∈ core, ∀ i, |(x i : ℝ)| ≤ width)
    (htarget : ∀ z ∈ target,
      Zonotope.IsZonotopePoint core (fun i ↦ (z i : ℝ)))
    (herrorBox : ∀ e : LatticePoint d,
      (∀ i, |(e i : ℝ)| ≤
        Real.sqrt (((d * core.card : ℕ) : ℝ)) * width) →
      e ∈ CFP.translate translatePoint (P.dilate k).carrier) :
    RoundingErrorsAbsorbedBy target core
      (CFP.translate translatePoint (P.dilate k).carrier) := by
  exact roundingErrorsAbsorbedBy_of_zonotope target core _ width hwidth
    hcore htarget herrorBox

/-- CFP specialization of the Minkowski-sum rounding lemma.  The
`habsorb` hypothesis is the explicit error-box estimate usually discharged
by comparing the rounding scale with the available progression dilation. -/
theorem roundingErrorsAbsorbedBy_cfpTranslate_add {d r k : ℕ}
    (target core structured : Finset (LatticePoint d)) (width : ℝ)
    (P : GAP d r) (translatePoint : LatticePoint d)
    (hwidth : 0 ≤ width)
    (hcore : ∀ x ∈ core, ∀ i, |(x i : ℝ)| ≤ width)
    (htarget : ∀ z ∈ target, ∃ p ∈ structured,
      ∃ x : LatticePoint d,
        Zonotope.IsZonotopePoint core (fun i ↦ (x i : ℝ)) ∧ z = p + x)
    (habsorb : ∀ p ∈ structured, ∀ e : LatticePoint d,
      (∀ i, |(e i : ℝ)| ≤
        Real.sqrt (((d * core.card : ℕ) : ℝ)) * width) →
      p + e ∈ CFP.translate translatePoint (P.dilate k).carrier) :
    RoundingErrorsAbsorbedBy target core
      (CFP.translate translatePoint (P.dilate k).carrier) := by
  exact roundingErrorsAbsorbedBy_of_zonotope_add target core structured _
    width hwidth hcore htarget habsorb

end

end Erdos186.PZ.Intersection
