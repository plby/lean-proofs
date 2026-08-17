/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos294.SharpLocalLimit

/-! # Prescribed rational subsums of the constant-width good set -/

open Filter Finset Real
open scoped BigOperators Topology

namespace Erdos294.SharpRepresentation

open Erdos285.RoughCounts
open Erdos297 Erdos297.ActiveLcm Erdos297.FiniteHoeffding
open Erdos297.LocalLimit
open Erdos294.SharpDensity Erdos294.SharpLocalLimit
open Erdos294.SharpParameters

noncomputable section

attribute [local instance] Classical.propDecidable

theorem eventually_exists_sharpGoodSet_recSum_eq_div :
    ∀ᶠ N : ℕ in atTop, ∀ a b : ℕ,
      0 < b → b ∣ activeLcm (sharpGoodSet N) →
      (1 / 3 : ℝ) ≤ (a : ℝ) / b →
      (a : ℝ) / b ≤ 1 →
      ∃ B ⊆ sharpGoodSet N, UnitFractions.rec_sum B = (a : ℚ) / b := by
  filter_upwards [eventually_prescribed_exactReciprocalMass,
      eventually_two_le_sharpGoodSet_reciprocalMass,
      eventually_sharpGoodSet_reciprocalMass_le_two_hundred,
      tendsto_logLogScale.eventually_ge_atTop 600,
      eventually_pos_scales] with N hlocal hmassLower hmassUpper hLLlarge hscales
  intro a b hb hbdvd hyLower hyUpper
  let I := sharpGoodSet N
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
    have hmassUpper' : mass ≤ 200 := by simpa [mass, I] using hmassUpper
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
      ∑ n ∈ I, p n / n = (y / mass) * ∑ n ∈ I, (1 : ℝ) / n := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        dsimp [p]
        ring
      _ = (y / mass) * mass := by rw [hmassEq]
      _ = y := by field_simp [hmassPos.ne']
  have hQpos : 0 < Q := activeLcm_pos I
  have hbQ : b ∣ Q := by simpa [Q, I] using hbdvd
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
  have hmean : ∑ n ∈ sharpGoodSet N, p n / n =
      (z : ℝ) / activeLcm (sharpGoodSet N) := by
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

end Erdos294.SharpRepresentation
