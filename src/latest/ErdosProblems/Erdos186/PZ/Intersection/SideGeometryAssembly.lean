/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.Main
import ErdosProblems.Erdos186.PZ.Intersection.ResidualAbsorption

/-!
# Geometric source-lemma adapters for an intersection side

These lemmas turn the literal centered-zonotope thickness and rounding-error
estimates into the two named source predicates consumed by
`Theorem4PostCFPData.ofSourceLemmas`.  They do not assume a common lattice
point or any subset-sum conclusion.
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

namespace IntersectionSideInput

variable {d : ℕ} {pool : Finset (LatticePoint d)}
    {a : LatticePoint d} {orientation : Orientation}

/-- Discharge the Lemma 13 predicate from an explicit structured-plus-
zonotope decomposition and the numerical error-box absorption estimate. -/
theorem lemma13ResidualAbsorption_of_zonotope_add
    (I : IntersectionSideInput pool a orientation)
    (structured : Finset (LatticePoint d)) (width : ℝ)
    (hwidth : 0 ≤ width)
    (hcore : ∀ x ∈ I.roundingCore, ∀ i, |(x i : ℝ)| ≤ width)
    (htarget : ∀ z ∈ I.target, ∃ p ∈ structured,
      ∃ x : LatticePoint d,
        Zonotope.IsZonotopePoint I.roundingCore
          (fun i ↦ (x i : ℝ)) ∧ z = p + x)
    (habsorb : ∀ p ∈ structured, ∀ e : LatticePoint d,
      (∀ i, |(e i : ℝ)| ≤
        Real.sqrt (((d * I.roundingCore.card : ℕ) : ℝ)) * width) →
      p + e ∈ CFP.translate I.witness.translatePoint
        (I.witness.progression.dilate I.dilation).carrier) :
    I.Lemma13ResidualAbsorption := by
  exact roundingErrorsAbsorbedBy_cfpTranslate_add I.target I.roundingCore
    structured width I.witness.progression I.witness.translatePoint
    hwidth hcore htarget habsorb

/-- Discharge the Lemma 14 predicate from the source's centered-zonotope
cube estimate.  `htarget` merely records how the finite target was defined:
the lattice points of the ordinary zonotope under consideration. -/
theorem lemma14TargetThickness_of_centeredZonotope_cube
    (I : IntersectionSideInput pool a orientation)
    (q : LatticePoint d → ℝ) (center : Fin d → ℝ) (radius : ℝ)
    (hcenter : center = zonotopeCenter I.roundingCore q)
    (hq : ∀ x ∈ I.roundingCore,
      0 ≤ q x ∧ q x ≤ (1 : ℝ) / 2)
    (hthick : ∀ z : Fin d → ℝ, (∀ i, |z i| ≤ radius) →
      z ∈ centeredZonotope I.roundingCore q)
    (htarget : ∀ z, z ∈ I.lattice →
      (fun i ↦ (z i : ℝ)) ∈ zonotope I.roundingCore → z ∈ I.target) :
    I.Lemma14TargetThickness center radius := by
  intro z hzL hzcube
  apply htarget z hzL
  apply mem_zonotope_of_centeredZonotope_cube I.roundingCore q radius hq hthick
  intro i
  simpa [hcenter] using hzcube i

end IntersectionSideInput

end

end Erdos186.PZ.Intersection
