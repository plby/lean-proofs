/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos989.Upper

/-!
# Finite probability estimates for the fixed-radius construction

This file records the elementary union-bound and exponential arithmetic used
after applying Hoeffding's inequality to the finite periodic jitter model.
-/

namespace Erdos989
namespace FixedRadiusUpper

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

/-- Counting form of the finite union bound.  No probability space is needed:
if the sum of the cardinalities of the bad sets is smaller than the outcome
space, then one outcome avoids every bad set. -/
theorem exists_avoiding_finite_bad_finsets
    {Omega Event : Type*} [Fintype Omega] [Fintype Event]
    (bad : Event -> Finset Omega)
    (hsmall : (∑ e, (bad e).card) < Fintype.card Omega) :
    exists omega : Omega, forall e, omega ∉ bad e := by
  classical
  by_contra h
  push Not at h
  have hsubset : (Finset.univ : Finset Omega) ⊆
      (Finset.univ : Finset Event).biUnion bad := by
    intro omega homega
    obtain ⟨e, he⟩ := h omega
    exact Finset.mem_biUnion.mpr ⟨e, Finset.mem_univ e, he⟩
  have hlarge : Fintype.card Omega <= ∑ e, (bad e).card := by
    calc
      Fintype.card Omega = (Finset.univ : Finset Omega).card :=
        (Finset.card_univ).symm
      _ <= ((Finset.univ : Finset Event).biUnion bad).card :=
        Finset.card_le_card hsubset
      _ <= ∑ e, (bad e).card := Finset.card_biUnion_le
  exact (Nat.not_lt_of_ge hlarge) hsmall

/-- A convenient uniform-cardinality specialization of
`exists_avoiding_finite_bad_finsets`. -/
theorem exists_avoiding_finite_bad_finsets_of_uniform_card_bound
    {Omega Event : Type*} [Fintype Omega] [Fintype Event]
    (bad : Event -> Finset Omega) (bound : ℕ)
    (hbad : forall e, (bad e).card <= bound)
    (hsmall : Fintype.card Event * bound < Fintype.card Omega) :
    exists omega : Omega, forall e, omega ∉ bad e := by
  apply exists_avoiding_finite_bad_finsets bad
  calc
    (∑ e, (bad e).card) <= ∑ _e : Event, bound :=
      Finset.sum_le_sum fun e _ => hbad e
    _ = Fintype.card Event * bound := by simp
    _ < Fintype.card Omega := hsmall

/-- Uniform version of the finite union bound: a family of `m` events, each
of probability at most `p`, can be avoided if `m * p < 1`. -/
theorem exists_avoiding_finite_events_of_uniform_bound
    {Omega Event : Type*} [Fintype Event] [Nonempty Omega]
    [MeasurableSpace Omega] (mu : Measure Omega) [IsProbabilityMeasure mu]
    (bad : Event -> Set Omega) (p : ℝ)
    (hbad : forall e, mu.real (bad e) <= p)
    (hsmall : (Fintype.card Event : ℝ) * p < 1) :
    exists omega : Omega, forall e, omega ∉ bad e := by
  apply GlobalSelection.exists_avoiding_finite_events mu bad (fun _ => p) hbad
  simpa using hsmall

/-- The numerical union-bound inequality used by a square-period construction.
There are at most `196 * r^4` net events, each with Hoeffding bound
`2 * exp (-(50/3) * log r)`.  Already for `r >= 2` their total mass is less
than one. -/
theorem periodic_net_hoeffding_total_lt_one {r : ℝ} (hr : 2 <= r) :
  196 * r ^ 4 * (2 * Real.exp (-(50 / 3) * Real.log r)) < 1 := by
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hexponent : -(50 / 3 : ℝ) * Real.log r <= -16 * Real.log r := by
    have hlog0 : 0 <= Real.log r := Real.log_nonneg (by linarith)
    nlinarith
  have hexp : Real.exp (-(50 / 3 : ℝ) * Real.log r) <= 1 / r ^ 16 := by
    calc
      Real.exp (-(50 / 3 : ℝ) * Real.log r)
          <= Real.exp (-16 * Real.log r) := Real.exp_le_exp.mpr hexponent
      _ = 1 / r ^ 16 := by
        rw [show -16 * Real.log r = -(16 * Real.log r) by ring,
          Real.exp_neg]
        change (Real.exp (((16 : ℕ) : ℝ) * Real.log r))⁻¹ = 1 / r ^ 16
        rw [Real.exp_nat_mul, Real.exp_log hr0]
        simp only [one_div]
  have hrpow : (2 : ℝ) ^ 12 <= r ^ 12 := by
    exact pow_le_pow_left₀ (by norm_num) hr 12
  have hconst : (392 : ℝ) < 2 ^ 12 := by norm_num
  have hpositive : 0 < r ^ 16 := pow_pos hr0 16
  calc
    196 * r ^ 4 * (2 * Real.exp (-(50 / 3) * Real.log r))
        <= 196 * r ^ 4 * (2 * (1 / r ^ 16)) := by
          gcongr
    _ = 392 / r ^ 12 := by
      field_simp
      ring
    _ < 1 := by
      rw [div_lt_one (pow_pos hr0 12)]
      exact hconst.trans_le hrpow

/-- Ready-to-use union bound for the periodic center net.  The geometric
part of the construction only has to establish the displayed event-count and
single-event estimates. -/
theorem exists_avoiding_periodic_net_events
    {Omega Event : Type*} [Fintype Event] [Nonempty Omega]
    [MeasurableSpace Omega] (mu : Measure Omega) [IsProbabilityMeasure mu]
    {r : ℝ} (hr : 2 <= r) (bad : Event -> Set Omega)
    (hevents : (Fintype.card Event : ℝ) <= 196 * r ^ 4)
    (hbad : forall e,
      mu.real (bad e) <= 2 * Real.exp (-(50 / 3) * Real.log r)) :
    exists omega : Omega, forall e, omega ∉ bad e := by
  apply exists_avoiding_finite_events_of_uniform_bound mu bad
    (2 * Real.exp (-(50 / 3) * Real.log r)) hbad
  apply lt_of_le_of_lt _ (periodic_net_hoeffding_total_lt_one hr)
  exact mul_le_mul_of_nonneg_right hevents
    (mul_nonneg (by norm_num) (Real.exp_pos _).le)

end

end FixedRadiusUpper
end Erdos989
