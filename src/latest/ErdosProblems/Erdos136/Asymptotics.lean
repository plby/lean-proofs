/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos136.LowerBound

/-!
# Erdős Problem 136: the asymptotic squeeze

This file isolates the analytic endgame of the proof.  The finite lower bound
has a harmless `n - 1` term, while an upper construction may be supplied with
either a normalized error tending to zero or an additive error which is
`o(n)`.  No property of the construction is used beyond these bounds.
-/

namespace Erdos136

open Filter
open scoped Topology

/-- The real-valued normalized palette size attached to a natural-valued
function. -/
noncomputable def normalizedPaletteSize (f : ℕ → ℕ) (n : ℕ) : ℝ :=
  (f n : ℝ) / (n : ℝ)

/-- A normalized limit with a nonzero coefficient is the corresponding
asymptotic equivalence.  Keeping this as a separate analytic lemma lets the
main Erdős theorem expose both the ratio-limit and `~` formulations. -/
theorem isEquivalent_of_tendsto_normalized
    (f : ℕ → ℝ) (c : ℝ) (hc : c ≠ 0)
    (hf : Tendsto (fun n : ℕ => f n / (n : ℝ)) atTop (nhds c)) :
    Asymptotics.IsEquivalent atTop f (fun n : ℕ => c * (n : ℝ)) := by
  refine Asymptotics.isEquivalent_of_tendsto_one ?_
  have h := hf.div_const c
  rw [div_self hc] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  simp only [Pi.div_apply]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp

/-- The normalized form of the Erdős--Gyárfás elementary lower bound tends to
`5 / 6`. -/
private lemma tendsto_lower_model :
    Tendsto (fun n : ℕ => (5 / 6 : ℝ) * (1 - (n : ℝ)⁻¹)) atTop
      (nhds (5 / 6 : ℝ)) := by
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (nhds 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hc : Tendsto (fun _ : ℕ => (5 / 6 : ℝ)) atTop
      (nhds (5 / 6 : ℝ)) := tendsto_const_nhds
  simpa using hc.mul (hone.sub hinv)

/-- The generic asymptotic squeeze used for Erdős Problem 136.  The lower
bound is exactly the elementary finite estimate, and the upper bound permits
an arbitrary normalized error tending to zero. -/
theorem tendsto_normalizedPaletteSize_of_normalized_error
    (f : ℕ → ℕ) (error : ℕ → ℝ)
    (herror : Tendsto error atTop (nhds 0))
    (hlower : ∀ᶠ n in atTop, 5 * (n - 1) ≤ 6 * f n)
    (hupper : ∀ᶠ n in atTop,
      normalizedPaletteSize f n ≤ (5 / 6 : ℝ) + error n) :
    Tendsto (normalizedPaletteSize f) atTop (nhds (5 / 6 : ℝ)) := by
  have hlower' : ∀ᶠ n : ℕ in atTop,
      (5 / 6 : ℝ) * (1 - (n : ℝ)⁻¹) ≤ normalizedPaletteSize f n := by
    filter_upwards [hlower, eventually_ge_atTop (1 : ℕ)] with n hn hn_one
    have hn_pos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (Nat.zero_lt_of_lt hn_one)
    have hreal : (5 : ℝ) * ((n - 1 : ℕ) : ℝ) ≤ 6 * (f n : ℝ) := by
      exact_mod_cast hn
    rw [Nat.cast_sub hn_one] at hreal
    norm_num at hreal
    apply (le_div_iff₀ hn_pos).2
    calc
      (5 / 6 : ℝ) * (1 - (n : ℝ)⁻¹) * (n : ℝ) =
          (5 / 6 : ℝ) * ((n : ℝ) - 1) := by
            field_simp
      _ ≤ (f n : ℝ) := by nlinarith
  have hupper_tendsto :
      Tendsto (fun n => (5 / 6 : ℝ) + error n) atTop
        (nhds (5 / 6 : ℝ)) := by
    have hc : Tendsto (fun _ : ℕ => (5 / 6 : ℝ)) atTop
        (nhds (5 / 6 : ℝ)) := tendsto_const_nhds
    simpa using hc.add herror
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_lower_model hupper_tendsto hlower' hupper

/-- An additive upper error may be supplied before normalization, provided
that dividing it by `n` makes it tend to zero. -/
theorem tendsto_normalizedPaletteSize_of_additive_error
    (f : ℕ → ℕ) (error : ℕ → ℝ)
    (herror : Tendsto (fun n => error n / (n : ℝ)) atTop (nhds 0))
    (hlower : ∀ᶠ n in atTop, 5 * (n - 1) ≤ 6 * f n)
    (hupper : ∀ᶠ n in atTop,
      (f n : ℝ) ≤ (5 / 6 : ℝ) * (n : ℝ) + error n) :
    Tendsto (normalizedPaletteSize f) atTop (nhds (5 / 6 : ℝ)) := by
  apply tendsto_normalizedPaletteSize_of_normalized_error f
    (fun n => error n / (n : ℝ)) herror hlower
  filter_upwards [hupper, eventually_ge_atTop (1 : ℕ)] with n hn hn_one
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hn_one)
  unfold normalizedPaletteSize
  apply (div_le_iff₀ hn_pos).2
  calc
    (f n : ℝ) ≤ (5 / 6 : ℝ) * (n : ℝ) + error n := hn
    _ = ((5 / 6 : ℝ) + error n / (n : ℝ)) * (n : ℝ) := by
      field_simp

/-- Specialization of the generic squeeze to the Erdős--Gyárfás function
defined in `Definitions.lean`. -/
theorem erdos136Fun_tendsto_of_normalized_error
    (error : ℕ → ℝ)
    (herror : Tendsto error atTop (nhds 0))
    (hlower : ∀ᶠ n in atTop, 5 * (n - 1) ≤ 6 * erdos136Fun n)
    (hupper : ∀ᶠ n in atTop,
      (erdos136Fun n : ℝ) / (n : ℝ) ≤ (5 / 6 : ℝ) + error n) :
    Tendsto (fun n => (erdos136Fun n : ℝ) / (n : ℝ)) atTop
      (nhds (5 / 6 : ℝ)) := by
  exact tendsto_normalizedPaletteSize_of_normalized_error
    erdos136Fun error herror hlower hupper

/-- An eventual construction with asymptotically `5 / 6` as many colors
closes the Erdős 136 squeeze.  The lower estimate is supplied by the exact
finite theorem in `LowerBound.lean`; minimality of `erdos136Fun` supplies the
upper estimate from the given colorings. -/
theorem erdos136Fun_tendsto_of_eventually_colorable
    (palette : ℕ → ℕ)
    (hpalette : Tendsto (normalizedPaletteSize palette) atTop
      (nhds (5 / 6 : ℝ)))
    (hcolorable : ∀ᶠ n : ℕ in atTop, Colorable n (palette n)) :
    Tendsto (fun n => (erdos136Fun n : ℝ) / (n : ℝ)) atTop
      (nhds (5 / 6 : ℝ)) := by
  let error : ℕ → ℝ := fun n => normalizedPaletteSize palette n - 5 / 6
  have herror : Tendsto error atTop (nhds 0) := by
    have hc : Tendsto (fun _ : ℕ => (5 / 6 : ℝ)) atTop
        (nhds (5 / 6 : ℝ)) := tendsto_const_nhds
    simpa [error] using hpalette.sub hc
  apply erdos136Fun_tendsto_of_normalized_error error herror
  · filter_upwards [eventually_ge_atTop (4 : ℕ)] with n hn
    exact erdos136Fun_lower_bound hn
  · filter_upwards [hcolorable] with n hn
    have hmin : erdos136Fun n ≤ palette n := erdos136Fun_min hn
    have hcast : (erdos136Fun n : ℝ) ≤ palette n := by exact_mod_cast hmin
    by_cases hn0 : n = 0
    · subst n
      simp [error, normalizedPaletteSize]
    · have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
      have := (div_le_div_iff_of_pos_right hnpos).2 hcast
      simpa [error, normalizedPaletteSize] using this

end Erdos136
