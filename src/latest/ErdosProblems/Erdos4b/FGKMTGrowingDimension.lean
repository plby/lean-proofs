/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTBoundedAdmissibleTuple

/-! # The rounded growing sieve dimension and its logarithmic gain -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

def growingSieveDimension (x : ℕ) : ℕ := ⌊Real.log (x : ℝ) ^ (1 / 10 : ℝ)⌋₊

theorem growingSieveDimension_le (x : ℕ) :
    (growingSieveDimension x : ℝ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ) :=
  Nat.floor_le (Real.rpow_nonneg (Real.log_natCast_nonneg x) _)

theorem tendsto_growingSieveDimension :
    Tendsto growingSieveDimension atTop atTop := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp hlog)

theorem eventually_growingSieveDimension_log_bounds :
    ∀ᶠ x : ℕ in atTop,
      (1 / 20 : ℝ) * Real.log (Real.log (x : ℝ)) ≤
          Real.log (growingSieveDimension x : ℝ) ∧
      Real.log (growingSieveDimension x : ℝ) ≤
          (1 / 10 : ℝ) * Real.log (Real.log (x : ℝ)) := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog := Real.tendsto_log_atTop.comp hlog
  filter_upwards [hlog.eventually (eventually_ge_atTop (1 : ℝ)),
    hloglog.eventually (eventually_ge_atTop (20 * Real.log 2))] with x hL hLL
  dsimp only [Function.comp_apply] at hLL
  have hLpos : 0 < Real.log (x : ℝ) := by linarith
  let r := Real.log (x : ℝ) ^ (1 / 10 : ℝ)
  have hr1 : 1 ≤ r := Real.one_le_rpow hL (by norm_num)
  have hrpos : 0 < r := by linarith
  have hfloor : r / 2 < (growingSieveDimension x : ℝ) := Nat.div_two_lt_floor hr1
  have hkpos : (0 : ℝ) < growingSieveDimension x :=
    (by positivity : 0 < r / 2).trans hfloor
  have hlo := Real.log_le_log (by positivity : 0 < r / 2) hfloor.le
  have hhi := Real.log_le_log hkpos (growingSieveDimension_le x)
  have hlogr : Real.log r = (1 / 10 : ℝ) * Real.log (Real.log (x : ℝ)) :=
    Real.log_rpow hLpos _
  change Real.log (growingSieveDimension x : ℝ) ≤ Real.log r at hhi
  rw [Real.log_div hrpos.ne' (by norm_num), hlogr] at hlo
  rw [hlogr] at hhi
  exact ⟨by linarith, hhi⟩

theorem eventually_growingSieveDimension_profile_range :
    ∀ᶠ x : ℕ in atTop,
      2 ≤ growingSieveDimension x ∧ 10000 ≤ Real.log (growingSieveDimension x : ℝ) := by
  have hlog := Real.tendsto_log_atTop.comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp tendsto_growingSieveDimension)
  exact (tendsto_growingSieveDimension.eventually (eventually_ge_atTop (2 : ℕ))).and
    (hlog.eventually (eventually_ge_atTop (10000 : ℝ)))

theorem eventually_exists_growing_admissible_tuple :
    ∀ᶠ x : ℕ in atTop, ∃ h : Fin (growingSieveDimension x) → ℕ,
      Function.Injective h ∧ BoundedGaps.IsAdmissible (Finset.univ.image h) ∧
      (∀ i, (h i).Prime ∧ growingSieveDimension x < h i ∧
        h i < 2 * growingSieveDimension x ^ 2) :=
  tendsto_growingSieveDimension.eventually eventually_exists_bounded_admissible_tuple

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.tendsto_growingSieveDimension
#print axioms Erdos4b.FGKMT.eventually_growingSieveDimension_log_bounds
#print axioms Erdos4b.FGKMT.eventually_exists_growing_admissible_tuple
