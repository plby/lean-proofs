/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos171.Framework

/-!
# Iterating a density increment

This file contains the final, purely formal iteration in the density
Hales--Jewett argument.  The combinatorial input is isolated in
`DensityIncrementStep`: at a fixed baseline density it supplies one positive
increment, and for every requested output dimension it supplies an ambient
dimension in which every sufficiently dense family either already contains a
line or has increased pullback density on a subspace of the requested
dimension.

Starting from the last requested dimension, `backwardDimension` recursively
chooses all preceding ambient dimensions.  Thus every increment lands in
exactly the cube needed for the next increment.  After sufficiently many
iterations the density would exceed one, contradicting `density_le_one`.

There is no assumed density-increment theorem in this file.  All uses of the
combinatorial increment are explicit hypotheses to the implication theorems
at the end of the file.
-/

namespace Erdos171

open Combinatorics

/-- Density Hales--Jewett at one fixed density. -/
def FiniteDensityHJAt (t : ℕ) (delta : ℝ) : Prop :=
  ∃ n : ℕ, ∀ A : Finset (Word t n),
    delta ≤ density A → ContainsLine (A : Set (Word t n))

theorem finiteDensityHJ_iff_forall_at {t : ℕ} :
    FiniteDensityHJ t ↔ ∀ delta : ℝ, 0 < delta → FiniteDensityHJAt t delta := by
  rfl

/-- Pull an ambient family back to the parameter cube of a subspace.  This
local version keeps the iteration independent of the later quantitative
subspace-density API. -/
noncomputable def iterationPullback {d t n : ℕ}
    (U : Subspace (Fin d) (Fin t) (Fin n)) (A : Finset (Word t n)) :
    Finset (Word t d) := by
  classical
  exact Finset.univ.filter fun x ↦ U x ∈ A

@[simp] theorem mem_iterationPullback {d t n : ℕ}
    (U : Subspace (Fin d) (Fin t) (Fin n)) (A : Finset (Word t n))
    (x : Word t d) :
    x ∈ iterationPullback U A ↔ U x ∈ A := by
  classical
  simp [iterationPullback]

/-- The abstract combinatorial input required by the density-increment
iteration at one fixed baseline density.

The threshold is recorded as a function of the desired target dimension.  It
is enough to state the conclusion at that threshold itself: `FiniteDensityHJ`
only asks for one witnessing dimension.  An eventual density-increment lemma
specializes to this form by using its threshold as the ambient dimension. -/
structure DensityIncrementStep (t : ℕ) (delta : ℝ) where
  /-- The density gain, uniform over all current densities at least `delta`. -/
  increment : ℝ
  increment_pos : 0 < increment
  /-- An ambient dimension for each desired output dimension. -/
  threshold : ℕ → ℕ
  /-- Either a line is already present, or restriction to a subspace raises
  the current density by at least `increment`. -/
  force :
    ∀ d : ℕ, ∀ A : Finset (Word t (threshold d)),
      delta ≤ density A →
        ContainsLine (A : Set (Word t (threshold d))) ∨
          ∃ U : Subspace (Fin d) (Fin t) (Fin (threshold d)),
            density A + increment ≤ density (iterationPullback U A)

namespace DensityIncrementStep

variable {t : ℕ} {delta : ℝ}

/-- Dimensions selected backwards from the terminal cube.  To perform
`r + 1` increments, first work in `threshold (backwardDimension r)` and ask
the increment step to return a `backwardDimension r`-dimensional subspace. -/
def backwardDimension (step : DensityIncrementStep t delta) : ℕ → ℕ
  | 0 => 0
  | r + 1 => step.threshold (backwardDimension step r)

@[simp] theorem backwardDimension_zero (step : DensityIncrementStep t delta) :
    backwardDimension step 0 = 0 := rfl

@[simp] theorem backwardDimension_succ (step : DensityIncrementStep t delta)
    (r : ℕ) :
    backwardDimension step (r + 1) =
      step.threshold (backwardDimension step r) := rfl

/-- A line in the finite pullback of a family gives a line in the family. -/
theorem containsLine_of_pullbackFinset
    {d n : ℕ} (U : Subspace (Fin d) (Fin t) (Fin n))
    (A : Finset (Word t n))
    (h : ContainsLine
      ((iterationPullback U A : Finset (Word t d)) : Set (Word t d))) :
    ContainsLine (A : Set (Word t n)) := by
  apply containsLine_of_subspace_preimage U
  have hpull :
      ((iterationPullback U A : Finset (Word t d)) : Set (Word t d)) =
        U ⁻¹' (A : Set (Word t n)) := by
    ext x
    simp
  rw [← hpull]
  exact h

/-- After `r` successful increments, either a line has appeared or a family
in the terminal zero-dimensional cube has density at least the initial
density plus `r * increment`.

This is the backward-dimension recursion.  The line branch is transported
out of every pullback immediately, so the conclusion always concerns the
family with which the recursion was started. -/
theorem iterate_or_terminal_density (step : DensityIncrementStep t delta) :
    ∀ r : ℕ, ∀ A : Finset (Word t (backwardDimension step r)),
      delta ≤ density A →
        ContainsLine
            (A : Set (Word t (backwardDimension step r))) ∨
          ∃ B : Finset (Word t (backwardDimension step 0)),
            density A + (r : ℝ) * step.increment ≤ density B := by
  intro r
  induction r with
  | zero =>
      intro A _hA
      right
      exact ⟨A, by simpa using (le_refl (density A))⟩
  | succ r ih =>
      intro A hA
      rcases step.force (backwardDimension step r) A hA with hline | ⟨U, hU⟩
      · exact Or.inl hline
      · have hBdelta : delta ≤ density (iterationPullback U A) := by
          calc
            delta ≤ density A := hA
            _ ≤ density A + step.increment :=
              le_add_of_nonneg_right step.increment_pos.le
            _ ≤ density (iterationPullback U A) := hU
        rcases ih (iterationPullback U A) hBdelta with hlineB | ⟨C, hC⟩
        · exact Or.inl (containsLine_of_pullbackFinset U A hlineB)
        · right
          refine ⟨C, ?_⟩
          calc
            density A + ((r + 1 : ℕ) : ℝ) * step.increment =
                (density A + step.increment) +
                  (r : ℝ) * step.increment := by
                    rw [Nat.cast_add, Nat.cast_one]
                    ring
            _ ≤ density (iterationPullback U A) +
                (r : ℝ) * step.increment :=
              add_le_add hU le_rfl
            _ ≤ density C := hC

/-- A uniform positive density increment at `delta` proves density
Hales--Jewett at `delta`. -/
theorem finiteDensityHJAt (step : DensityIncrementStep t delta) :
    FiniteDensityHJAt t delta := by
  obtain ⟨r, hr⟩ := exists_lt_nsmul step.increment_pos (1 - delta)
  have hr' : 1 - delta < (r : ℝ) * step.increment := by
    simpa using hr
  have hone : 1 < delta + (r : ℝ) * step.increment := by
    linarith
  refine ⟨backwardDimension step r, ?_⟩
  intro A hA
  rcases iterate_or_terminal_density step r A hA with hline | ⟨B, hB⟩
  · exact hline
  · exfalso
    have hlarge : 1 < density B := by
      calc
        1 < delta + (r : ℝ) * step.increment := hone
        _ ≤ density A + (r : ℝ) * step.increment :=
          add_le_add hA le_rfl
        _ ≤ density B := hB
    exact (not_lt_of_ge (density_le_one B)) hlarge

end DensityIncrementStep

/-- If the density-increment statement is available at every positive
density, then the finite density Hales--Jewett theorem follows. -/
theorem finiteDensityHJ_of_densityIncrement
    {t : ℕ}
    (step : ∀ delta : ℝ, 0 < delta → DensityIncrementStep t delta) :
    FiniteDensityHJ t := by
  intro delta hdelta
  exact (step delta hdelta).finiteDensityHJAt

/-- Successor-alphabet packaging of the iteration.  A proof of the
combinatorial increment for the `(k+1)`-letter alphabet at every positive
density is exactly what remains after the density-increment argument has used
the induction hypothesis for the `k`-letter alphabet. -/
theorem finiteDensityHJ_succ_of_densityIncrement
    {k : ℕ}
    (step : ∀ delta : ℝ, 0 < delta → DensityIncrementStep (k + 1) delta) :
    FiniteDensityHJ (k + 1) :=
  finiteDensityHJ_of_densityIncrement step

/-- Alphabet-induction interface in a form convenient for the eventual DKT
increment theorem: that theorem may consume the induction hypothesis and
return all successor-alphabet increment steps. -/
theorem FiniteDensityHJ.succ_of_densityIncrement
    {k : ℕ} (hk : FiniteDensityHJ k)
    (step : FiniteDensityHJ k →
      ∀ delta : ℝ, 0 < delta → DensityIncrementStep (k + 1) delta) :
    FiniteDensityHJ (k + 1) :=
  finiteDensityHJ_succ_of_densityIncrement (step hk)

end Erdos171
