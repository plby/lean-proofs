/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.Asymptotic

/-!
# Terminal power absorption

The internal CFP exponent `2 * (β + 1)` has enough slack to absorb a fixed
rank factor and a terminal GAP bound of order `m^β`, even when the surviving
population is only known to exceed `m^(1-ε)` for `ε < 1/3`.
-/

namespace Erdos186.PZ.Reduction

open Filter
open scoped Topology

noncomputable section

/-- Uniform terminal absorption estimate used to verify the difference-box
cardinality guard for every dense candidate. -/
theorem exists_terminalAbsorption_threshold
    (β ε δ constant : ℝ) (R : ℕ)
    (hβ : 1 < β) (hε0 : 0 < ε) (hε1 : ε < (1 / 3 : ℝ))
    (hδ : 0 < δ) (hconstant : 0 < constant) :
    ∃ threshold : ℕ, 2 ≤ threshold ∧
      ∀ m n x v r : ℕ,
        threshold ≤ m → r ≤ R →
        Real.rpow (m : ℝ) (1 - ε) < (n : ℝ) →
        δ * (n : ℝ) ≤ (x : ℝ) →
        (v : ℝ) ≤ constant * Real.rpow (m : ℝ) β →
        (2 : ℝ) ^ r * (v : ℝ) ≤
          Real.rpow (x : ℝ) (2 * (β + 1)) := by
  let E : ℝ := 2 * (β + 1)
  let q : ℝ := (1 - ε) * E - β
  have hE : 0 < E := by
    dsimp [E]
    nlinarith
  have ha : (2 / 3 : ℝ) < 1 - ε := by linarith
  have hbasegap : β < (2 / 3 : ℝ) * E := by
    dsimp [E]
    nlinarith
  have hq : 0 < q := by
    have hmul := mul_lt_mul_of_pos_right ha hE
    dsimp [q]
    linarith
  have hδpow : 0 < Real.rpow δ E := Real.rpow_pos_of_pos hδ E
  let Q : ℝ := ((2 : ℝ) ^ R * constant) / Real.rpow δ E
  have heventual := (nat_rpow_tendsto_atTop hq).eventually_ge_atTop Q
  obtain ⟨t, ht⟩ := eventually_atTop.1 heventual
  refine ⟨max 2 t, le_max_left _ _, ?_⟩
  intro m n x v r hm hr hpop hx hv
  have htm : t ≤ m := (le_max_right 2 t).trans hm
  have hQ := ht m htm
  have hm2 : 2 ≤ m := (le_max_left 2 t).trans hm
  have hmpos : 0 < (m : ℝ) := by positivity
  have hnpos : 0 < (n : ℝ) := by
    have hp : 0 < Real.rpow (m : ℝ) (1 - ε) :=
      Real.rpow_pos_of_pos hmpos _
    linarith
  have hxpos : 0 < (x : ℝ) :=
    lt_of_lt_of_le (mul_pos hδ hnpos) hx
  have htwo : (2 : ℝ) ^ r ≤ (2 : ℝ) ^ R :=
    pow_le_pow_right₀ (by norm_num) hr
  have hcoeff : (2 : ℝ) ^ R * constant ≤
      Real.rpow δ E * Real.rpow (m : ℝ) q := by
    apply (div_le_iff₀ hδpow).mp at hQ
    simpa [Q, mul_comm] using hQ
  have hpowNonneg : 0 ≤ Real.rpow (m : ℝ) β :=
    Real.rpow_nonneg hmpos.le _
  have hcandidate : δ * Real.rpow (m : ℝ) (1 - ε) ≤ (x : ℝ) := by
    exact (mul_le_mul_of_nonneg_left hpop.le hδ.le).trans hx
  calc
    (2 : ℝ) ^ r * (v : ℝ) ≤
        (2 : ℝ) ^ r * (constant * Real.rpow (m : ℝ) β) :=
      mul_le_mul_of_nonneg_left hv (by positivity)
    _ ≤ (2 : ℝ) ^ R * (constant * Real.rpow (m : ℝ) β) :=
      mul_le_mul_of_nonneg_right htwo
        (mul_nonneg hconstant.le hpowNonneg)
    _ = ((2 : ℝ) ^ R * constant) * Real.rpow (m : ℝ) β := by ring
    _ ≤ (Real.rpow δ E * Real.rpow (m : ℝ) q) *
        Real.rpow (m : ℝ) β :=
      mul_le_mul_of_nonneg_right hcoeff hpowNonneg
    _ = Real.rpow δ E * Real.rpow (m : ℝ) ((1 - ε) * E) := by
      have hadd : Real.rpow (m : ℝ) q * Real.rpow (m : ℝ) β =
          Real.rpow (m : ℝ) (q + β) :=
        (Real.rpow_add hmpos q β).symm
      rw [mul_assoc, hadd]
      apply congrArg (Real.rpow δ E * ·)
      congr 1
      dsimp [q]
      ring
    _ = Real.rpow (δ * Real.rpow (m : ℝ) (1 - ε)) E := by
      have hpowpow : Real.rpow (m : ℝ) ((1 - ε) * E) =
          Real.rpow (Real.rpow (m : ℝ) (1 - ε)) E :=
        Real.rpow_mul hmpos.le (1 - ε) E
      rw [hpowpow]
      exact (Real.mul_rpow (x := δ)
        (y := Real.rpow (m : ℝ) (1 - ε)) (z := E)
        hδ.le (Real.rpow_nonneg hmpos.le _)).symm
    _ ≤ Real.rpow (x : ℝ) E :=
      Real.rpow_le_rpow
        (mul_nonneg hδ.le (Real.rpow_nonneg hmpos.le _)) hcandidate hE.le
    _ = Real.rpow (x : ℝ) (2 * (β + 1)) := rfl

/-- A fixed positive density fraction of a population larger than
`m^(1-ε)` eventually exceeds any prescribed natural candidate threshold. -/
theorem exists_denseCandidate_card_threshold
    (ε δ : ℝ) (candidateThreshold : ℕ)
    (_hε0 : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) :
    ∃ inputThreshold : ℕ, 2 ≤ inputThreshold ∧
      ∀ m n x : ℕ,
        inputThreshold ≤ m →
        Real.rpow (m : ℝ) (1 - ε) < (n : ℝ) →
        δ * (n : ℝ) ≤ (x : ℝ) →
        candidateThreshold ≤ x := by
  have ha : 0 < 1 - ε := sub_pos.mpr hε1
  have heventual := (nat_rpow_tendsto_atTop ha).eventually_ge_atTop
    ((candidateThreshold : ℝ) / δ)
  obtain ⟨t, ht⟩ := eventually_atTop.1 heventual
  refine ⟨max 2 t, le_max_left _ _, ?_⟩
  intro m n x hm hpopulation hdense
  have htm : t ≤ m := (le_max_right 2 t).trans hm
  have hpow := ht m htm
  have hcandidate : (candidateThreshold : ℝ) ≤
      δ * Real.rpow (m : ℝ) (1 - ε) := by
    simpa [mul_comm] using (div_le_iff₀ hδ).mp hpow
  have hstrict : δ * Real.rpow (m : ℝ) (1 - ε) < δ * (n : ℝ) :=
    mul_lt_mul_of_pos_left hpopulation hδ
  exact_mod_cast hcandidate.trans (hstrict.le.trans hdense)

end

end Erdos186.PZ.Reduction
