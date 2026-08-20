/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos980.External.Erdos822.Assembly

/-!
# The analytic interface for Erdős Problem 822

The Gabdullin--Iudelevich--Luca argument does not need an asymptotic formula
for the range.  Its exact output is a family of finite input sets with
linear size and linear shifted-totient collision energy.  This structure
records that output without hiding any hypothesis; `lowerDensity_pos` is the
checked finite-combinatorial consequence.

The remaining number-theoretic development has to construct a value of this
structure from the sets in Section 5.1 of the paper.  Keeping the interface
separate makes it impossible to accidentally treat that analytic step as a
definition or an assumption in the final theorem.
-/

namespace Erdos822

open Filter

/-- The precise finite output required from the analytic part of the GIL
proof.  Every field is a proposition that must be proved by the eventual
structured-set construction. -/
structure LinearEnergyWitness where
  /-- The finite set of selected inputs at scale `x`. -/
  inputs : ℕ → Finset ℕ
  /-- The lower-size constant for the selected inputs. -/
  sizeConstant : ℝ
  /-- The upper-energy constant for the selected inputs. -/
  energyConstant : ℝ
  sizeConstant_pos : 0 < sizeConstant
  energyConstant_pos : 0 < energyConstant
  inputs_bounded : ∀ᶠ x : ℕ in atTop, ∀ n ∈ inputs x, n ≤ x
  inputs_linear : ∀ᶠ x : ℕ in atTop,
    sizeConstant * (x : ℝ) ≤ (inputs x).card
  energy_linear : ∀ᶠ x : ℕ in atTop,
    (collisionEnergy (inputs x) shiftedTotient : ℝ) ≤
      energyConstant * (x : ℝ)

/-- A proved GIL analytic witness implies the corrected positive-lower-density
conclusion. -/
theorem LinearEnergyWitness.lowerDensity_pos (w : LinearEnergyWitness) :
    0 < totientRange.lowerDensity := by
  exact lowerDensity_pos_of_eventually_linear_energy w.inputs
    w.sizeConstant_pos w.energyConstant_pos w.inputs_bounded
    w.inputs_linear w.energy_linear

end Erdos822
