/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.PlaneReduction

/-!
# Erdős Problem 232

For a measurable set in the Euclidean plane, `Erdos232.upperDensity` is its upper
asymptotic density in centered balls and `Erdos232.m1` is the supremum of those
densities over sets containing no pair of points at distance one.

The exact rational certificate formalized in the supporting modules proves the
slightly stronger bound `0.246993028`.  The published decimal conclusion `0.247`
and Erdős's requested `1 / 4` bound follow immediately.
-/

open Filter MeasureTheory Metric

namespace Erdos232

noncomputable section

/-- Almost-everywhere equal planar sets have the same density in every centred ball. -/
theorem ballDensity_congr_ae {A B : Set Plane} (h : A =ᵐ[volume] B) :
    ballDensity A = ballDensity B := by
  funext R
  unfold ballDensity
  have hmeasure : volume (A ∩ ball 0 R) = volume (B ∩ ball 0 R) := by
    apply measure_congr
    exact h.mono fun x hx =>
      congrArg (fun p : Prop => p ∧ x ∈ ball (0 : Plane) R) hx
  rw [hmeasure]

/-- Upper density is invariant under equality almost everywhere for Lebesgue measure. -/
theorem upperDensity_congr_ae {A B : Set Plane} (h : A =ᵐ[volume] B) :
    upperDensity A = upperDensity B := by
  unfold upperDensity
  rw [ballDensity_congr_ae h]

/-- The literal set of densities of Lebesgue-measurable unit-distance-free sets.

For Mathlib's Borel measurable space, Lebesgue measurability is expressed by
`NullMeasurableSet A volume`. -/
noncomputable def lebesgueAdmissibleDensities : Set ℝ :=
  {d | ∃ A : Set Plane,
    NullMeasurableSet A volume ∧ UnitDistanceFree A ∧ upperDensity A = d}

/-- The literal Lebesgue-measurable extremal density from Erdős Problem 232. -/
noncomputable def lebesgueM1 : ℝ :=
  sSup lebesgueAdmissibleDensities

/-- Passing to a Borel subset equal almost everywhere preserves admissibility and density. -/
theorem lebesgueAdmissibleDensities_eq_admissibleDensities :
    lebesgueAdmissibleDensities = admissibleDensities := by
  ext d
  constructor
  · rintro ⟨A, hA, hfree, rfl⟩
    obtain ⟨B, hBA, hB, hEq⟩ := hA.exists_measurable_subset_ae_eq
    refine ⟨B, hB, ?_, ?_⟩
    · intro x hx y hy
      exact hfree (hBA hx) (hBA hy)
    · exact upperDensity_congr_ae hEq
  · rintro ⟨A, hA, hfree, rfl⟩
    exact ⟨A, hA.nullMeasurableSet, hfree, rfl⟩

/-- The Borel-representative and literal Lebesgue formulations of `m₁` agree. -/
theorem lebesgueM1_eq_m1 : lebesgueM1 = m1 := by
  rw [lebesgueM1, m1, lebesgueAdmissibleDensities_eq_admissibleDensities]

theorem lebesgueAdmissibleDensities_nonempty : lebesgueAdmissibleDensities.Nonempty := by
  rw [lebesgueAdmissibleDensities_eq_admissibleDensities]
  exact admissibleDensities_nonempty

/-- Direct Lebesgue-measurable-set form of the exact certificate bound. -/
theorem erdos_232_set_exact {A : Set Plane} (hA : NullMeasurableSet A volume)
    (hfree : UnitDistanceFree A) :
    upperDensity A ≤ (246993028 / 1000000000 : ℝ) := by
  obtain ⟨B, hBA, hB, hEq⟩ := hA.exists_measurable_subset_ae_eq
  have hfreeB : UnitDistanceFree B := by
    intro x hx y hy
    exact hfree (hBA hx) (hBA hy)
  have hbound := upperDensity_le_dualTarget hB hfreeB
  rw [upperDensity_congr_ae hEq] at hbound
  exact hbound

/-- Direct measurable-set form of the published `0.247` conclusion. -/
theorem erdos_232_set {A : Set Plane} (hA : NullMeasurableSet A volume)
    (hfree : UnitDistanceFree A) :
    upperDensity A ≤ (247 / 1000 : ℝ) := by
  exact (erdos_232_set_exact hA hfree).trans (by norm_num)

/-- Exact rational bound for the literal Lebesgue-measurable supremum. -/
theorem erdos_232_lebesgue_exact :
    lebesgueM1 ≤ (246993028 / 1000000000 : ℝ) := by
  rw [lebesgueM1]
  apply csSup_le lebesgueAdmissibleDensities_nonempty
  rintro d ⟨A, hA, hfree, rfl⟩
  exact erdos_232_set_exact hA hfree

/-- Exact rational form of the formalized dual-certificate bound. -/
theorem erdos_232_exact :
    m1 ≤ (246993028 / 1000000000 : ℝ) := by
  rw [← lebesgueM1_eq_m1]
  exact erdos_232_lebesgue_exact

/-- Ambrus--Csiszárik--Matolcsi--Varga--Zsámboki's resolution of Erdős Problem 232. -/
theorem erdos_232 :
    m1 ≤ (247 / 1000 : ℝ) := by
  exact erdos_232_exact.trans (by norm_num)

/-- Published decimal bound in the literal Lebesgue-measurable formulation. -/
theorem erdos_232_lebesgue :
    lebesgueM1 ≤ (247 / 1000 : ℝ) := by
  exact erdos_232_lebesgue_exact.trans (by norm_num)

/-- In particular, the answer to Erdős's question `m₁ ≤ 1 / 4` is yes. -/
theorem erdos_232_quarter :
    m1 ≤ (1 / 4 : ℝ) := by
  exact erdos_232.trans (by norm_num)

/-- Erdős's `1 / 4` question for the literal Lebesgue-measurable supremum. -/
theorem erdos_232_lebesgue_quarter :
    lebesgueM1 ≤ (1 / 4 : ℝ) := by
  exact erdos_232_lebesgue.trans (by norm_num)

end

end Erdos232
