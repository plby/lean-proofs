/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.CollisionAdmissibility
import ErdosProblems.Erdos822.OddCofactorLayers
import ErdosProblems.Erdos822.NthRootScale
import ErdosProblems.Erdos822.AnalyticInput

/-!
# Passing a filtered perfect-power family to all scales

The B5 layer is a subfamily of the odd raw cofactors.  This generic bridge
keeps the filter abstract: any eventually linear-size filtered family with
linear perfect-power energy supplies the witness used by the lower-density
assembly.
-/

namespace Erdos822

open Filter

/-- Pull a filtered odd cofactor family back from the largest sixtieth power
below the ambient scale. -/
def filteredOddPowerInputs (B : ℕ → Finset ℕ) (x : ℕ) : Finset ℕ :=
  let N := Nat.nthRoot 60 x
  outerInputs (fun _ => B N) (N ^ 60)

theorem filteredOddPowerInputs_bounded
    (B : ℕ → Finset ℕ)
    (hB : ∀ N, B N ⊆ oddRawCofactors N) (x : ℕ) :
    ∀ n ∈ filteredOddPowerInputs B x, n ≤ x := by
  intro n hn
  let N := Nat.nthRoot 60 x
  have hNpow : N ^ 60 ≤ x := nthRoot_pow_le (by norm_num)
  exact (outerInputs_bounded (fun _ => B N) (N ^ 60) n hn).trans
    hNpow

/-- Generic perfect-power bridge for a filtered odd cofactor family. -/
noncomputable def linearEnergyWitness_of_eventually_filteredOddPerfectPower_energy
    {B : ℕ → Finset ℕ} {c C : ℝ}
    (hc : 0 < c) (hC : 0 < C)
    (hB : ∀ N, B N ⊆ oddRawCofactors N)
    (hsize : ∀ᶠ N : ℕ in atTop,
      c * ((N ^ 60 : ℕ) : ℝ) ≤
        ((outerInputs (fun _ => B N) (N ^ 60)).card : ℝ))
    (henergy : ∀ᶠ N : ℕ in atTop,
      (collisionEnergy
        (outerInputs (fun _ => B N) (N ^ 60))
        shiftedTotient : ℝ) ≤ C * ((N ^ 60 : ℕ) : ℝ)) :
    LinearEnergyWitness := by
  let c' : ℝ := c / (2 : ℝ) ^ 60
  refine
    { inputs := filteredOddPowerInputs B
      sizeConstant := c'
      energyConstant := C
      sizeConstant_pos := by
        dsimp [c']
        positivity
      energyConstant_pos := hC
      inputs_bounded :=
        Filter.Eventually.of_forall (filteredOddPowerInputs_bounded B hB)
      inputs_linear := ?_
      energy_linear := ?_ }
  · obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hsize
    filter_upwards [eventually_nthRoot_ge 60 (max 1 T) (by norm_num)] with x hx
    let N := Nat.nthRoot 60 x
    have hN1 : 1 ≤ N := le_trans (le_max_left 1 T) hx
    have hNT : T ≤ N := le_trans (le_max_right 1 T) hx
    have hsizeN := hT N hNT
    have hxle : x ≤ 2 ^ 60 * N ^ 60 :=
      le_two_pow_mul_nthRoot_pow (by norm_num) hN1
    have hxleR : (x : ℝ) ≤ ((2 ^ 60 * N ^ 60 : ℕ) : ℝ) := by
      exact_mod_cast hxle
    change c' * (x : ℝ) ≤
      ((outerInputs (fun _ => B N) (N ^ 60)).card : ℝ)
    calc
      c' * (x : ℝ) ≤ c * ((N ^ 60 : ℕ) : ℝ) := by
        dsimp [c']
        have hpowpos : (0 : ℝ) < (2 : ℝ) ^ 60 := by positivity
        calc
          c / (2 : ℝ) ^ 60 * (x : ℝ) ≤
              c / (2 : ℝ) ^ 60 *
                ((2 ^ 60 * N ^ 60 : ℕ) : ℝ) := by
            gcongr
          _ = c * ((N ^ 60 : ℕ) : ℝ) := by
            push_cast
            field_simp
            ring
      _ ≤ ((outerInputs (fun _ => B N) (N ^ 60)).card : ℝ) :=
        hsizeN
  · obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp henergy
    filter_upwards [eventually_nthRoot_ge 60 T (by norm_num)] with x hx
    let N := Nat.nthRoot 60 x
    have henergyN := hT N hx
    have hNpow : N ^ 60 ≤ x := nthRoot_pow_le (by norm_num)
    change
      (collisionEnergy
        (outerInputs (fun _ => B N) (N ^ 60))
        shiftedTotient : ℝ) ≤ C * (x : ℝ)
    exact henergyN.trans (mul_le_mul_of_nonneg_left
      (by exact_mod_cast hNpow) hC.le)

end Erdos822
