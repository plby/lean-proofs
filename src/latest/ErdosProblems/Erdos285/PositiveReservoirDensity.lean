/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos285.PrimeReciprocalTail
import ErdosProblems.Erdos285.ProperPrimePowerTail

/-!
# Positive density of the prime-power-smooth reservoir

This file assembles the finite union bound and the two reciprocal-tail
estimates.  For every fixed `α > 0`, at least `α x / 600` integers in
`[αx/2, αx]` eventually have every prime-power divisor at most
`floor (x^(2/5))`.
-/

open Filter Finset Real Asymptotics
open scoped BigOperators Topology

namespace Erdos285.PositiveReservoir

noncomputable section

attribute [local instance] Classical.propDecidable

theorem eventually_obstructingPrimePower_reciprocal_sum_lt
    (α : ℝ) (hα : 0 < α) :
    ∀ᶠ x : ℕ in atTop,
      (∑ q ∈ obstructingPrimePowers α x, (q : ℝ)⁻¹) < (99 / 100 : ℝ) := by
  filter_upwards
    [eventually_primeReciprocalInterval_smoothCutoff_lt α hα,
      eventually_properPrimePowerReciprocalInterval_smoothCutoff_lt α hα]
      with x hprime hproper
  rw [obstructingPrimePower_reciprocal_sum_eq]
  linarith

/-- A positive-density prime-power-smooth reservoir in `[αx/2, αx]`.
The constant is intentionally loose; only positivity is used downstream. -/
theorem eventually_positiveReservoir_card_lower (α : ℝ) (hα : 0 < α) :
    ∀ᶠ x : ℕ in atTop,
      α / 600 * x ≤ ((positiveReservoir α x).card : ℝ) := by
  have herror := (obstructingPrimePowers_card_isLittleO α hα).bound
    (show 0 < α / 600 by positivity)
  have hscale : Tendsto (fun x : ℕ ↦ α * (x : ℝ) / 2) atTop atTop := by
    convert (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop
      (show 0 < α / 2 by positivity) using 1
    ext x
    ring
  have hlowerPositive : ∀ᶠ x : ℕ in atTop, 1 ≤ ⌈α * (x : ℝ) / 2⌉₊ := by
    have hceil : Tendsto (fun x : ℕ ↦ ⌈α * (x : ℝ) / 2⌉₊) atTop atTop :=
      tendsto_nat_ceil_atTop.comp hscale
    exact hceil.eventually_ge_atTop 1
  filter_upwards
    [eventually_reservoirInterval_card_lower α hα,
      eventually_obstructingPrimePower_reciprocal_sum_lt α hα,
      herror, hlowerPositive]
      with x hinterval htail herrorx hlo
  let L : ℝ := ((reservoirInterval α x).card : ℝ)
  let P : ℝ := ((positiveReservoir α x).card : ℝ)
  let E : ℝ := ((obstructingPrimePowers α x).card : ℝ)
  let U : ℝ := (((obstructingPrimePowers α x).biUnion
    (multiplesInReservoir α x)).card : ℝ)
  have herror' : E ≤ α / 600 * x := by
    simpa [E, Real.norm_natCast, Real.norm_of_nonneg (show 0 ≤ (x : ℝ) by positivity),
      abs_of_pos hα] using herrorx
  have hcompNat := reservoir_complement_card_le_union α x hlo
  have hcomp : L - P ≤ U := by
    have hsubset := positiveReservoir_subset_interval α x
    have hcard : (positiveReservoir α x).card ≤ (reservoirInterval α x).card :=
      Finset.card_le_card hsubset
    have hcast : (((reservoirInterval α x).card -
        (positiveReservoir α x).card : ℕ) : ℝ) ≤
        (((obstructingPrimePowers α x).biUnion
          (multiplesInReservoir α x)).card : ℝ) := by
      exact_mod_cast hcompNat
    simpa [L, P, U, Nat.cast_sub hcard] using hcast
  have hunion := obstructing_union_card_le α x
  have hunion' : U ≤ L * (99 / 100 : ℝ) + E := by
    calc
      U ≤ L * (∑ q ∈ obstructingPrimePowers α x, (q : ℝ)⁻¹) + E := by
        simpa [U, L, E] using hunion
      _ ≤ L * (99 / 100 : ℝ) + E := by
        have hL : 0 ≤ L := by positivity
        simpa [add_comm] using
          (add_le_add_right (mul_le_mul_of_nonneg_left htail.le hL) E)
  have hP : L - U ≤ P := by linarith
  have hL : α / 3 * x ≤ L := by simpa [L] using hinterval
  calc
    α / 600 * x ≤ L / 100 - E := by
      have hx : 0 ≤ (x : ℝ) := by positivity
      nlinarith
    _ ≤ L - U := by
      nlinarith [hunion']
    _ ≤ P := hP
    _ = ((positiveReservoir α x).card : ℝ) := rfl

end

end Erdos285.PositiveReservoir

#print axioms Erdos285.PositiveReservoir.eventually_positiveReservoir_card_lower
