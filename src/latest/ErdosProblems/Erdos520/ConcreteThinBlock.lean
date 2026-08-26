import ErdosProblems.Erdos520.Equation16Helpers
import ErdosProblems.Erdos520.ThinBlock

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory Set
open scoped BigOperators

namespace Erdos
namespace Problem520

/-!
# Concrete scheduled thin-prime blocks

This file packages an integer prime-block schedule into `ThinBlockData` and
turns the concrete equation-(16) estimate into `ThinPrimeBlockMomentBound`.
The schedule is total at `j = 0`: natural subtraction makes that block use
the equal endpoints `y ell 0`, while the moment bound itself is requested
only for `1 ≤ j`.
-/

/-- Data still supplied by the analytic schedule/paper-facing part of the
argument.  All constants are uniform in `ell`, `j`, the old sign assignment,
and the moment exponent.

The elementary inverse-square integrability conditions are proved outright
in `Equation16Helpers`, so no analytic side-condition field is retained here.
-/
structure ConcreteThinBlockSchedule where
  /-- Last prime-block index at each scale. -/
  J : ℕ → ℕ
  /-- Integer block endpoints. -/
  y : ℕ → ℕ → ℕ
  /-- Endpoints increase with the block index. -/
  y_monotone : ∀ ell, Monotone (y ell)
  /-- Every endpoint lies in the range where its logarithm is positive. -/
  two_le_y : ∀ ell j, 2 ≤ y ell j
  /-- The old-coordinate normalized Euler-product energy. -/
  I : ℕ → ℕ → Omega → ℝ
  /-- Euler-product energies are nonnegative. -/
  I_nonneg : ∀ ell j old, 0 ≤ I ell j old
  /-- Uniform constant in the Parseval/energy comparison. -/
  Cparseval : ℝ
  Cparseval_nonneg : 0 ≤ Cparseval
  /-- Uniform constant in the thin reciprocal-prime estimate. -/
  Crecip : ℝ
  Crecip_nonneg : 0 ≤ Crecip
  /-- Uniform paper-facing Parseval/normalized-energy comparison. -/
  parseval_le : ∀ ell, 1 ≤ ell →
    ∀ j, 1 ≤ j → j ≤ J ell → ∀ old,
      (∫ z in Ioi (0 : ℝ),
          |ΨReal old z (y ell (j - 1))| ^ 2 / z ^ 2) /
          Real.log (y ell j : ℝ) ≤
        Cparseval * I ell (j - 1) old
  /-- Uniform `O(1 / ell)` reciprocal-prime mass of every valid block. -/
  reciprocal_le : ∀ ell, 1 ≤ ell →
    ∀ j, 1 ≤ j → j ≤ J ell →
      freshReciprocalSum (y ell (j - 1)) (y ell j) ≤ Crecip / ell

namespace ConcreteThinBlockSchedule

/-- Left and right endpoints of a scheduled block. -/
abbrev leftEndpoint (s : ConcreteThinBlockSchedule) (ell j : ℕ) : ℕ :=
  s.y ell (j - 1)

abbrev rightEndpoint (s : ConcreteThinBlockSchedule) (ell j : ℕ) : ℕ :=
  s.y ell j

theorem leftEndpoint_le_rightEndpoint (s : ConcreteThinBlockSchedule)
    (ell j : ℕ) : s.leftEndpoint ell j ≤ s.rightEndpoint ell j := by
  exact s.y_monotone ell (Nat.sub_le j 1)

theorem log_rightEndpoint_pos (s : ConcreteThinBlockSchedule)
    (ell j : ℕ) : 0 < Real.log (s.rightEndpoint ell j : ℝ) := by
  apply Real.log_pos
  exact_mod_cast (show 1 < s.rightEndpoint ell j by
    exact lt_of_lt_of_le Nat.one_lt_two (s.two_le_y ell j))

/-- The clamped finite running maximum is nonnegative. -/
theorem realSmoothBlockMaxSq_nonneg (a b : ℕ) (omega : Omega) (z : ℝ) :
    0 ≤ realSmoothBlockMaxSq a b omega z := by
  unfold realSmoothBlockMaxSq finiteRunningMax
  exact (pow_nonneg
    (abs_nonneg (ΨReal omega z (freshCutoff a b 0))) 2).trans
      (Finset.le_sup'
        (fun k ↦ |ΨReal omega z (freshCutoff a b k)| ^ 2)
        (Finset.mem_range.mpr (Nat.zero_lt_succ b)))

/-- Every scheduled block energy is nonnegative, including the harmless
equal-endpoint block at `j = 0`. -/
theorem realSmoothBlockEnergy_nonneg (s : ConcreteThinBlockSchedule)
    (ell j : ℕ) (omega : Omega) :
    0 ≤ realSmoothBlockEnergy
      (s.leftEndpoint ell j) (s.rightEndpoint ell j) omega := by
  unfold realSmoothBlockEnergy
  apply mul_nonneg
  · exact inv_nonneg.mpr (s.log_rightEndpoint_pos ell j).le
  · exact integral_nonneg fun z ↦
      div_nonneg (realSmoothBlockMaxSq_nonneg _ _ omega z) (sq_nonneg z)

/-- The concrete `ThinBlockData` associated to an integer endpoint schedule.
At block `j`, `U` is the real smooth energy between `y(ell,j-1)` and
`y(ell,j)`, and the filtration exposes precisely the primes at most the right
endpoint. -/
noncomputable def toThinBlockData (s : ConcreteThinBlockSchedule) :
    ThinBlockData Omega where
  J := s.J
  filtration ell j :=
    Filtration.piFinset ((s.y ell j + 1).primesBelow)
  filtration_le _ell _j := Filtration.piFinset.le _
  U ell j := realSmoothBlockEnergy
    (s.leftEndpoint ell j) (s.rightEndpoint ell j)
  I := s.I

@[simp] theorem toThinBlockData_J (s : ConcreteThinBlockSchedule) :
    s.toThinBlockData.J = s.J := rfl

@[simp] theorem toThinBlockData_filtration (s : ConcreteThinBlockSchedule)
    (ell j : ℕ) :
    s.toThinBlockData.filtration ell j =
      Filtration.piFinset ((s.y ell j + 1).primesBelow) := rfl

@[simp] theorem toThinBlockData_U (s : ConcreteThinBlockSchedule)
    (ell j : ℕ) :
    s.toThinBlockData.U ell j = realSmoothBlockEnergy
      (s.leftEndpoint ell j) (s.rightEndpoint ell j) := rfl

@[simp] theorem toThinBlockData_I (s : ConcreteThinBlockSchedule) :
    s.toThinBlockData.I = s.I := rfl

/-- Every concrete integer schedule satisfying the two uniform paper-facing
estimates obeys the abstract thin-prime-block moment bound.  All finite-fiber
Doob--Bonami, Minkowski, measurability, and inverse-square integrability
obligations are discharged by `Equation16` and `Equation16Helpers`.

The witness constant is enlarged to `max 1 C₀`; this supplies the strict
positivity required by `ThinPrimeBlockMomentBound` even if both input
constants happen to be zero. -/
theorem thinPrimeBlockMomentBound (s : ConcreteThinBlockSchedule) :
    ThinPrimeBlockMomentBound μ s.toThinBlockData := by
  let C₀ : ℝ := max (4 * s.Cparseval) (2 * s.Crecip)
  let C : ℝ := max 1 C₀
  have hC₀_nonneg : 0 ≤ C₀ := by
    exact (mul_nonneg (by norm_num) s.Cparseval_nonneg).trans
      (le_max_left _ _)
  have hC₀_le_C : C₀ ≤ C := le_max_right _ _
  have hC_pos : 0 < C := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨C, hC_pos, ?_, ?_⟩
  · intro ell j omega
    exact s.realSmoothBlockEnergy_nonneg ell j omega
  · intro ell hell j hj hjJ r hr
    let a : ℕ := s.leftEndpoint ell j
    let b : ℕ := s.rightEndpoint ell j
    have hab : a ≤ b := s.leftEndpoint_le_rightEndpoint ell j
    have hlog : 0 < Real.log (b : ℝ) := s.log_rightEndpoint_pos ell j
    have h16 := concreteEquation16
      (ell := ell) (r := r) (a := a) (b := b)
      (by omega) hr (s.I ell (j - 1)) hab hlog
      s.Cparseval_nonneg s.Crecip_nonneg
      (fun old ↦ s.I_nonneg ell (j - 1) old)
      (s.parseval_le ell hell j hj hjJ)
      (s.reciprocal_le ell hell j hj hjJ)
    rcases h16 with ⟨hintegrable, hcond₀⟩
    constructor
    · change Integrable
        (fun omega : Omega ↦ realSmoothBlockEnergy a b omega ^ r) μ
      exact hintegrable
    · change ∀ᵐ old ∂μ,
        (μ[(fun omega : Omega ↦ realSmoothBlockEnergy a b omega ^ r) |
            Filtration.piFinset ((a + 1).primesBelow)] old) ^
              (1 / (r : ℝ)) ≤
          C * Real.exp (C * r / ell) * s.I ell (j - 1) old
      have hcond : ∀ᵐ old ∂μ,
          (μ[(fun omega : Omega ↦ realSmoothBlockEnergy a b omega ^ r) |
              Filtration.piFinset ((a + 1).primesBelow)] old) ^
                (1 / (r : ℝ)) ≤
            C₀ * Real.exp (C₀ * r / ell) * s.I ell (j - 1) old := by
        simpa only [C₀] using! hcond₀
      filter_upwards [hcond] with old hold
      have hexponent : C₀ * (r : ℝ) / ell ≤ C * (r : ℝ) / ell := by
        have hnum : C₀ * (r : ℝ) ≤ C * (r : ℝ) :=
          mul_le_mul_of_nonneg_right hC₀_le_C (by positivity)
        exact div_le_div_of_nonneg_right hnum (by positivity)
      have hexp : Real.exp (C₀ * r / ell) ≤
          Real.exp (C * r / ell) := Real.exp_le_exp.mpr hexponent
      have hI := s.I_nonneg ell (j - 1) old
      calc
        (μ[(fun omega : Omega ↦ realSmoothBlockEnergy a b omega ^ r) |
            Filtration.piFinset ((a + 1).primesBelow)] old) ^
              (1 / (r : ℝ)) ≤
            C₀ * Real.exp (C₀ * r / ell) * s.I ell (j - 1) old := hold
        _ ≤ C * Real.exp (C₀ * r / ell) * s.I ell (j - 1) old := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hC₀_le_C (Real.exp_pos _).le) hI
        _ ≤ C * Real.exp (C * r / ell) * s.I ell (j - 1) old := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hexp
              (hC₀_nonneg.trans hC₀_le_C)) hI

end ConcreteThinBlockSchedule

end Problem520
end Erdos
