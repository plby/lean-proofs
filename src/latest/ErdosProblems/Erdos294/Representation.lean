/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos294.PrescribedLocalLimit
import ErdosProblems.Erdos294.MassBounds
import ErdosProblems.Erdos294.Bridge

/-!
# Prescribed rational subsums of the source good set

We apply the prescribed local limit theorem with a constant Bernoulli
parameter.  The reciprocal-mass bounds put that parameter uniformly between
`1 / log log N` and `1 / 2`.  Positivity of the exact atom then gives an
actual subset with the desired reciprocal sum.
-/

open Filter Finset Real
open scoped BigOperators Topology

namespace Erdos294.Representation

open Erdos285.RoughCounts
open Erdos297
open Erdos297.ActiveLcm Erdos297.LogisticNormalization
open Erdos297.LocalLimit
open Erdos294.MassBounds Erdos294.PrescribedLocalLimit

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A rational in the fixed interval `[1/3,1]`, whose denominator divides
the active LCM, is a reciprocal subsum of the good set. -/
theorem eventually_exists_goodSet_recSum_eq_div :
    ∀ᶠ N : ℕ in atTop, ∀ a b : ℕ,
      0 < b → b ∣ activeLcm (goodSet N) →
      (1 / 3 : ℝ) ≤ (a : ℝ) / b →
      (a : ℝ) / b ≤ 1 →
      ∃ B ⊆ goodSet N, UnitFractions.rec_sum B = (a : ℚ) / b := by
  filter_upwards [eventually_prescribed_exactReciprocalMass,
    eventually_two_le_goodSet_reciprocalMass,
    eventually_goodSet_reciprocalMass_le_logLog_div_three,
    eventually_pos_scales] with N hlocal hmassLower hmassUpper hscales
  intro a b hb hbdvd hyLower hyUpper
  let I := goodSet N
  let Q := activeLcm I
  let mass := reciprocalMass I
  let y : ℝ := (a : ℝ) / b
  let p : ℕ → ℝ := fun _ ↦ y / mass
  let z : ℕ := a * (Q / b)
  have hmassLower' : 2 ≤ mass := by simpa [mass, I] using hmassLower
  have hmassPos : 0 < mass := zero_lt_two.trans_le hmassLower'
  have hLLpos : 0 < logLogScale N := zero_lt_one.trans hscales.2.2.1
  have hpLower : ∀ n ∈ I, 1 / logLogScale N ≤ p n := by
    intro n hn
    dsimp [p]
    apply (div_le_div_iff₀ hLLpos hmassPos).2
    have hmassUpper' : mass ≤ logLogScale N / 3 := by
      simpa [mass, I] using hmassUpper
    have hyLower' : (1 / 3 : ℝ) ≤ y := by simpa [y] using hyLower
    nlinarith
  have hpUpper : ∀ n ∈ I, p n ≤ 1 / 2 := by
    intro n hn
    dsimp [p]
    apply (div_le_iff₀ hmassPos).2
    have hyUpper' : y ≤ (1 : ℝ) := by simpa [y] using hyUpper
    nlinarith
  have hmassEq : ∑ n ∈ I, (1 : ℝ) / n = mass := by
    simp only [mass, reciprocalMass, one_div]
  have hmeanY : ∑ n ∈ I, p n / n = y := by
    calc
      ∑ n ∈ I, p n / n =
          (y / mass) * ∑ n ∈ I, (1 : ℝ) / n := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        dsimp [p]
        ring
      _ = (y / mass) * mass := by rw [hmassEq]
      _ = y := by field_simp [hmassPos.ne']
  have hQpos : 0 < Q := by
    exact activeLcm_pos I
  have hbQ : b ∣ Q := by simpa [Q, I] using hbdvd
  have hQeq : Q = b * (Q / b) := by
    simpa [Nat.mul_comm] using (Nat.div_mul_cancel hbQ).symm
  have hcancelR : ((Q / b : ℕ) : ℝ) * b = Q := by
    exact_mod_cast Nat.div_mul_cancel hbQ
  have hcancelQ : ((Q / b : ℕ) : ℚ) * b = Q := by
    exact_mod_cast Nat.div_mul_cancel hbQ
  have htargetR : (z : ℝ) / Q = y := by
    dsimp [z, y]
    push_cast
    field_simp [hb.ne', (Nat.ne_of_gt hQpos)]
    calc
      (a : ℝ) * (Q / b : ℕ) * b = (a : ℝ) * ((Q / b : ℕ) * b) := by ring
      _ = (a : ℝ) * Q := by rw [hcancelR]
  have htargetQ : (z : ℚ) / Q = (a : ℚ) / b := by
    dsimp [z]
    push_cast
    field_simp [hb.ne', (Nat.ne_of_gt hQpos)]
    calc
      (a : ℚ) * (Q / b : ℕ) * b = (a : ℚ) * ((Q / b : ℕ) * b) := by ring
      _ = (a : ℚ) * Q := by rw [hcancelQ]
  have hmean : ∑ n ∈ goodSet N, p n / n =
      (z : ℝ) / activeLcm (goodSet N) := by
    simpa [I, Q, htargetR] using hmeanY
  have hmassAtom := hlocal p z
    (by simpa [I] using hpLower) (by simpa [I] using hpUpper) hmean
  have hAtomPos : 0 < exactReciprocalMass I p (z / (Q : ℚ)) := by
    have hleft : 0 < 1 / (4 * (Q : ℝ)) := by positivity
    exact hleft.trans_le (by simpa [I, Q] using hmassAtom)
  by_contra hnone
  push Not at hnone
  have hzero : exactReciprocalMass I p (z / (Q : ℚ)) = 0 := by
    unfold exactReciprocalMass
    apply Finset.sum_eq_zero
    intro B hB
    have hBI : B ⊆ I := Finset.mem_powerset.mp hB
    rw [if_neg]
    intro hrec
    exact hnone B (by simpa [I] using hBI) (by simpa [htargetQ] using hrec)
  rw [hzero] at hAtomPos
  exact lt_irrefl 0 hAtomPos

end

end Erdos294.Representation
