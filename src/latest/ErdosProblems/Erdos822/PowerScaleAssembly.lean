/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.OuterEnergy
import ErdosProblems.Erdos822.AnalyticInput
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

/-!
# Passing from perfect-power scales to every scale

The structured construction is most convenient at x=N^60.  Choosing
N=floor(x^(1/60)) makes the perfect-power family a family at every x; the
loss is only the fixed factor 2^60.
-/

namespace Erdos822

open Filter

/-- The odd outer-input family pulled back from the largest sixtieth power
below x. -/
def oddPowerInputs (x : ℕ) : Finset ℕ :=
  let N := Nat.nthRoot 60 x
  outerInputs (fun _ => oddRawCofactors N) (N ^ 60)

theorem eventually_nthRoot_ge (k T : ℕ) (hk : k ≠ 0) :
    ∀ᶠ x : ℕ in atTop, T ≤ Nat.nthRoot k x := by
  filter_upwards [Filter.eventually_ge_atTop (T ^ k)] with x hx
  exact (Nat.le_nthRoot_iff hk).2 hx

theorem nthRoot_pow_le {k x : ℕ} (hk : k ≠ 0) :
    Nat.nthRoot k x ^ k ≤ x :=
  (Nat.pow_nthRoot_le_iff).2 (Or.inl hk)

theorem le_two_pow_mul_nthRoot_pow {k x : ℕ}
    (hk : k ≠ 0) (hroot : 1 ≤ Nat.nthRoot k x) :
    x ≤ 2 ^ k * Nat.nthRoot k x ^ k := by
  let N := Nat.nthRoot k x
  have hxlt : x < (N + 1) ^ k := Nat.lt_pow_nthRoot_add_one hk x
  have hN : N + 1 ≤ 2 * N := by
    dsimp [N] at hroot ⊢
    omega
  have hpow : (N + 1) ^ k ≤ (2 * N) ^ k :=
    Nat.pow_le_pow_left hN k
  calc
    x ≤ (N + 1) ^ k := hxlt.le
    _ ≤ (2 * N) ^ k := hpow
    _ = 2 ^ k * N ^ k := by ring

theorem oddPowerInputs_bounded (x : ℕ) :
    ∀ n ∈ oddPowerInputs x, n ≤ x := by
  intro n hn
  let N := Nat.nthRoot 60 x
  have hNpow : N ^ 60 ≤ x := nthRoot_pow_le (by norm_num)
  exact (outerInputs_bounded (fun _ => oddRawCofactors N) (N ^ 60) n hn).trans
    hNpow

/-- A linear energy estimate at perfect sixtieth powers produces the exact
eventual witness required by the lower-density assembly. -/
noncomputable def linearEnergyWitness_of_eventually_oddPerfectPower_energy
    {C : ℝ} (hC : 0 < C)
    (henergy : ∀ᶠ N : ℕ in atTop,
      (collisionEnergy
        (outerInputs (fun _ => oddRawCofactors N) (N ^ 60))
        shiftedTotient : ℝ) ≤ C * ((N ^ 60 : ℕ) : ℝ)) :
    LinearEnergyWitness := by
  let c : ℝ := 1 / (2400000 * (2 : ℝ) ^ 60)
  refine
    { inputs := oddPowerInputs
      sizeConstant := c
      energyConstant := C
      sizeConstant_pos := by
        dsimp [c]
        positivity
      energyConstant_pos := hC
      inputs_bounded := Filter.Eventually.of_forall oddPowerInputs_bounded
      inputs_linear := ?_
      energy_linear := ?_ }
  · obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
      eventually_oddRawOuterInputs_card_linear
    filter_upwards [eventually_nthRoot_ge 60 (max 1 T) (by norm_num)] with x hx
    let N := Nat.nthRoot 60 x
    have hN1 : 1 ≤ N := le_trans (le_max_left 1 T) hx
    have hNT : T ≤ N := le_trans (le_max_right 1 T) hx
    have hsize := hT N hNT
    have hxle : x ≤ 2 ^ 60 * N ^ 60 :=
      le_two_pow_mul_nthRoot_pow (by norm_num) hN1
    have hxleR : (x : ℝ) ≤ ((2 ^ 60 * N ^ 60 : ℕ) : ℝ) := by
      exact_mod_cast hxle
    change c * (x : ℝ) ≤
      ((outerInputs (fun _ => oddRawCofactors N) (N ^ 60)).card : ℝ)
    calc
      c * (x : ℝ) ≤
          (1 / 2400000 : ℝ) * ((N ^ 60 : ℕ) : ℝ) := by
        dsimp [c]
        have hpowpos : (0 : ℝ) < (2 : ℝ) ^ 60 := by positivity
        calc
          1 / (2400000 * (2 : ℝ) ^ 60) * (x : ℝ) ≤
              1 / (2400000 * (2 : ℝ) ^ 60) *
                ((2 ^ 60 * N ^ 60 : ℕ) : ℝ) := by
            gcongr
          _ = (1 / 2400000 : ℝ) * ((N ^ 60 : ℕ) : ℝ) := by
            push_cast
            field_simp
            ring
      _ ≤ ((outerInputs (fun _ => oddRawCofactors N) (N ^ 60)).card : ℝ) :=
        hsize
  · obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp henergy
    filter_upwards [eventually_nthRoot_ge 60 T (by norm_num)] with x hx
    let N := Nat.nthRoot 60 x
    have hNT : T ≤ N := hx
    have hE := hT N hNT
    have hNpow : N ^ 60 ≤ x := nthRoot_pow_le (by norm_num)
    change
      (collisionEnergy
        (outerInputs (fun _ => oddRawCofactors N) (N ^ 60))
        shiftedTotient : ℝ) ≤ C * (x : ℝ)
    exact hE.trans (mul_le_mul_of_nonneg_left
      (by exact_mod_cast hNpow) hC.le)

end Erdos822
