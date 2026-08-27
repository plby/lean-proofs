/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.BoundedSharpSurvivalLogarithm
import ErdosProblems.Erdos207.FineOuterCanonicalCertificates

/-!
# Sharp moment survival for the canonical outer corridor

The fixed witness order fits below the live pair floor.  The already proved
canonical corridor then gives a polynomial decay of the tracked-edge
survival product, independently of the later residual-degree cutoff.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem fineOuterCanonical_survival_pow_seven_le_clock_ratio
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (lower₀ outside t Kinc K Kpair Kglobal s : ℕ)
    (hc : FineOuterCanonicalCertificates H X lower₀ outside t
      Kinc K Kpair Kglobal)
    (hreserve : 21 ≤ fineOuterReserve outside t)
    (hsmall : 18 * s ≤ fineOuterCoarseDegreeFloor outside t) :
    let fuel := outerSharpStopFuel H X (fineOuterReserve outside t)
    let d := outerSharpLowerSchedule H X
      (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) Kinc
    let M := outerSharpUpperAvailability H X
      (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) Kinc
    cumulativeSurvival (boundedSharpSurvivalSchedule fuel M d (3 * s)) fuel ^ 7 ≤
      ((outerSharpEligiblePairs H X fuel : ℝ≥0) /
        outerSharpEligiblePairs H X 0) ^ 4 := by
  dsimp only
  let reserve := fineOuterReserve outside t
  let fuel := outerSharpStopFuel H X reserve
  let E := outerSharpEligiblePairs H X
  let d := outerSharpLowerSchedule H X
    (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) Kinc
  let u := outerSharpUpperSchedule H X
    (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) Kinc
  let M := outerSharpUpperAvailability H X
    (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) Kinc
  have hreservePos : 0 < reserve := by dsimp only [reserve]; omega
  have hEbound : ∀ i, i ≤ fuel → reserve ≤ E i := by
    intro i hi
    exact outerSharpEligiblePairs_stopFuel_floor H X hc.input.reserve_initial hi
  apply cumulativeSurvival_boundedSharp_pow_seven_le_clock_ratio
    fuel s E M d u
    (hreservePos.trans_le (hEbound 0 (Nat.zero_le _)))
    (hreservePos.trans_le (hEbound fuel le_rfl))
  · intro i hi
    exact hreserve.trans (hEbound i hi.le)
  · intro i hi
    apply outerSharpEligiblePairs_succ_eq_sub_three H X
    have hfuel := three_mul_outerSharpStopFuel_le H X reserve
    have hisucc : i + 1 ≤ fuel := by omega
    exact (Nat.mul_le_mul_left 3 hisucc).trans
      (hfuel.trans (Nat.sub_le _ _))
  · intro i hi
    exact hc.process.upper_availability_pos i hi
  · intro i hi
    exact hc.input.degree_pos.trans_le (hc.bounds i hi.le).1
  · intro i hi
    exact hc.process.degree_le_availability i hi
  · intro i _hi
    exact three_mul_outerSharpUpperAvailability_le H X
      (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) Kinc i
  · intro i hi
    exact (fineOuterCanonical_schedule_ratio_bounds H X lower₀ outside t
      Kinc i hc.input.outside_pos hc.input.t_pos hreservePos
      hc.input.reserve_initial hc.input.pair_upper hc.input.small_power
      hc.input.offset_power hc.input.clock_power hc.input.aggregate_power
      hc.input.initial_order hc.input.initial hc.input.reserve_four hi.le).2
  · intro i hi
    exact hsmall.trans (hc.bounds i hi.le).1

/-- The integral stopping error costs at most a factor two once the reserve
is at least two.  A one-third initial eligible-pair density then gives the
explicit ratio `6/t`. -/
lemma fineOuterCanonical_terminal_clock_ratio_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (outside t : ℕ)
    (ht : 0 < t) (hreserveTwo : 2 ≤ fineOuterReserve outside t)
    (hreserveInitial : fineOuterReserve outside t ≤
      outerSharpEligiblePairs H X 0)
    (hpairLower : outside ^ 2 ≤ 3 * outerSharpEligiblePairs H X 0) :
    (outerSharpEligiblePairs H X
        (outerSharpStopFuel H X (fineOuterReserve outside t)) : ℝ≥0) /
        outerSharpEligiblePairs H X 0 ≤ 6 / (t : ℝ≥0) := by
  let reserve := fineOuterReserve outside t
  let E0 := outerSharpEligiblePairs H X 0
  let Ef := outerSharpEligiblePairs H X (outerSharpStopFuel H X reserve)
  have hterminal : Ef ≤ 2 * reserve := by
    have h := outerSharpEligiblePairs_stopFuel_lt_add_three H X hreserveInitial
    dsimp only [Ef, reserve]
    omega
  have hreserveMul : t * reserve ≤ outside ^ 2 := by
    simpa only [reserve, fineOuterReserve, Nat.mul_comm] using
      Nat.div_mul_le_self (outside ^ 2) t
  have hcross : t * Ef ≤ 6 * E0 := by
    have hscaled := Nat.mul_le_mul_left t hterminal
    dsimp only [E0]
    nlinarith
  have hE0pos : (0 : ℝ≥0) < E0 := by
    have hnat : 0 < E0 := by dsimp only [E0]; omega
    exact_mod_cast hnat
  have htpos : (0 : ℝ≥0) < t := by exact_mod_cast ht
  change (Ef : ℝ≥0) / E0 ≤ 6 / (t : ℝ≥0)
  rw [div_le_div_iff₀ hE0pos htpos]
  exact_mod_cast (by simpa only [Nat.mul_comm t] using hcross)

theorem fineOuterCanonical_survival_pow_seven_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (lower₀ outside t Kinc K Kpair Kglobal s : ℕ)
    (hc : FineOuterCanonicalCertificates H X lower₀ outside t
      Kinc K Kpair Kglobal)
    (hreserve : 21 ≤ fineOuterReserve outside t)
    (hsmall : 18 * s ≤ fineOuterCoarseDegreeFloor outside t)
    (hpairLower : outside ^ 2 ≤ 3 * outerSharpEligiblePairs H X 0) :
    let fuel := outerSharpStopFuel H X (fineOuterReserve outside t)
    let d := outerSharpLowerSchedule H X
      (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) Kinc
    let M := outerSharpUpperAvailability H X
      (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) Kinc
    cumulativeSurvival (boundedSharpSurvivalSchedule fuel M d (3 * s)) fuel ^ 7 ≤
      (6 / (t : ℝ≥0)) ^ 4 := by
  apply (fineOuterCanonical_survival_pow_seven_le_clock_ratio
    H X lower₀ outside t Kinc K Kpair Kglobal s hc hreserve hsmall).trans
  apply pow_le_pow_left'
  exact fineOuterCanonical_terminal_clock_ratio_le H X outside t
    hc.input.t_pos (by omega) hc.input.reserve_initial hpairLower

end

end Erdos207
