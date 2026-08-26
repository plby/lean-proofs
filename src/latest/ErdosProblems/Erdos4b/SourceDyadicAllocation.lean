/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceDyadicAllocationScales
import ErdosProblems.Erdos4b.SourceResidualAllocationCost

/-!
# All rounded cofactor intervals fit in the auxiliary range

The density is fixed after the arbitrary interval multiplier D. A common
slack of X / (log X)^2 gives the minimum length for uniform prime counts.
-/

namespace Erdos4b.SmoothParameters

noncomputable section

open Filter
open scoped BigOperators Topology

def dyadicAllocationDensity (D : ℕ) : ℝ := 1 / (640 * (D : ℝ))

theorem dyadicAllocationDensity_pos {D : ℕ} (hD : 0 < D) :
    0 < dyadicAllocationDensity D := by unfold dyadicAllocationDensity; positivity

def dyadicAllocatedLength (a D r m : ℕ) : ℕ :=
  sourceRequestedIntervalLength (dyadicAllocationDensity D)
    (D * intervalLength a r / m : ℕ) (dyadicCompanionScale r)
    (residualCofactorLocalProduct (smoothFrontier r) m)
    ((primaryFrontier a r : ℝ) / dyadicAmbientScale a r ^ 2)

theorem eventually_sum_dyadicAllocatedLength_le_quarter
    (a : ℕ) {D : ℕ} (hD : 0 < D) :
    ∀ᶠ r in atTop, ∀ E : Finset ℕ,
      (∀ m ∈ E, 0 < m ∧ Even m ∧ m ≤ D * fullResidualCofactorCutoff r) →
      ((∑ m ∈ E, dyadicAllocatedLength a D r m : ℕ) : ℝ) ≤ (primaryFrontier a r : ℝ) / 4 := by
  filter_upwards [eventually_ge_atTop 1, eventually_dyadicAllocationPrincipalScale_le a hD,
    eventually_dyadicAllocationSlack_le a D] with r hr hprincipal hslack
  intro E hE
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hM : 1 ≤ D * fullResidualCofactorCutoff r :=
    Nat.succ_le_iff.mpr (Nat.mul_pos hD (fullResidualCofactorCutoff_pos (by omega)))
  have hL : 0 < dyadicCompanionScale r := dyadicCompanionScale_pos (by omega)
  have hρ := dyadicAllocationDensity_pos hD
  have hcount : E.card ≤ D * fullResidualCofactorCutoff r := by
    have hsub : E ⊆ Finset.Icc 1 (D * fullResidualCofactorCutoff r) := by
      intro m hm
      exact Finset.mem_Icc.mpr ⟨(hE m hm).1, (hE m hm).2.2⟩
    have hh := Finset.card_le_card hsub
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hh
  have hcost := sum_sourceRequestedIntervalLength_residual_le
    (U := D * intervalLength a r) (y := smoothFrontier r) hM hE hρ.le hL.le
    (show (0 : ℝ) ≤ (primaryFrontier a r : ℝ) / dyadicAmbientScale a r ^ 2 by positivity)
  have hmain : 8 * dyadicAllocationDensity D * (D * intervalLength a r : ℕ) /
      dyadicCompanionScale r * (1 + Real.log (D * fullResidualCofactorCutoff r : ℕ)) ≤
        (primaryFrontier a r : ℝ) / 8 := by
    calc
      _ = (8 * dyadicAllocationDensity D * D) *
          ((intervalLength a r : ℝ) * (1 + Real.log (D * fullResidualCofactorCutoff r : ℕ)) /
            dyadicCompanionScale r) := by push_cast; ring
      _ ≤ (8 * dyadicAllocationDensity D * D) * (10 * (primaryFrontier a r : ℝ)) :=
        mul_le_mul_of_nonneg_left hprincipal (by positivity)
      _ = _ := by unfold dyadicAllocationDensity; field_simp; ring
  have hextra : (E.card : ℝ) *
      ((primaryFrontier a r : ℝ) / dyadicAmbientScale a r ^ 2 + 1) ≤
        (primaryFrontier a r : ℝ) / 8 :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hcount)
      (by positivity : (0 : ℝ) ≤ (primaryFrontier a r : ℝ) / dyadicAmbientScale a r ^ 2 + 1)).trans
        hslack
  have hcost' : ((∑ m ∈ E, dyadicAllocatedLength a D r m : ℕ) : ℝ) ≤
      8 * dyadicAllocationDensity D * (D * intervalLength a r : ℕ) / dyadicCompanionScale r *
        (1 + Real.log (D * fullResidualCofactorCutoff r : ℕ)) +
        E.card * ((primaryFrontier a r : ℝ) / dyadicAmbientScale a r ^ 2 + 1) := by
    simpa only [dyadicAllocatedLength, Nat.cast_sum] using hcost
  linarith

theorem sourceAllocation_capacity_of_quarter_sum {X total : ℕ}
    (hX : 2 ≤ X) (htotal : (total : ℝ) ≤ (X : ℝ) / 4) :
    X ≤ 2 * ((X + 1) / 2) ∧ (X + 1) / 2 + total ≤ X := by
  have hbase : 4 * ((X + 1) / 2) ≤ 3 * X := by omega
  have hbase' : (4 : ℝ) * ((X + 1) / 2 : ℕ) ≤ 3 * X := by exact_mod_cast hbase
  refine ⟨by omega, ?_⟩
  have hsum : (((X + 1) / 2 : ℕ) : ℝ) + total ≤ X := by linarith
  exact_mod_cast hsum

theorem eventually_dyadicAllocated_intervals
    (a : ℕ) {D : ℕ} (hD : 0 < D) :
    ∀ᶠ r in atTop, ∀ E : Finset ℕ,
      (∀ m ∈ E, 0 < m ∧ Even m ∧ m ≤ D * fullResidualCofactorCutoff r) →
      let A := sourceAllocatedStart E (dyadicAllocatedLength a D r) ((primaryFrontier a r + 1) / 2)
      let B := sourceAllocatedEnd E (dyadicAllocatedLength a D r) ((primaryFrontier a r + 1) / 2)
      (∀ m ∈ E, primaryFrontier a r ≤ 2 * A m ∧ A m ≤ B m ∧ B m ≤ primaryFrontier a r ∧
        (primaryFrontier a r : ℝ) / dyadicAmbientScale a r ^ 2 ≤ (B m : ℝ) - A m ∧
        dyadicAllocationDensity D * (D * intervalLength a r / m : ℕ) /
          (dyadicCompanionScale r * residualCofactorLocalProduct (smoothFrontier r) m) ≤
            (B m : ℝ) - A m) ∧
      (∀ m ∈ E, ∀ n ∈ E, m ≠ n → Disjoint (auxiliaryPrimeInterval (A m) (B m))
        (auxiliaryPrimeInterval (A n) (B n))) := by
  filter_upwards [eventually_ge_atTop 1, eventually_sum_dyadicAllocatedLength_le_quarter a hD]
    with r hr hsum
  intro E hE
  dsimp only
  have hX : 2 ≤ primaryFrontier a r := by
    unfold primaryFrontier
    exact (one_lt_pow₀ (by norm_num : 1 < (2 : ℕ)) (primaryExponent_pos a r).ne')
  have hcapacity := sourceAllocation_capacity_of_quarter_sum hX (hsum E hE)
  constructor
  · intro m hm
    obtain ⟨hA, hAB, hB⟩ := sourceAllocated_upperHalf_range (dyadicAllocatedLength a D r)
      hcapacity.1 hcapacity.2 hm
    refine ⟨hA, hAB, hB, ?_, ?_⟩
    · rw [sourceAllocated_real_length]
      exact sourceRequestedIntervalLength_ge_slack (dyadicAllocationDensity_pos hD).le
        (Nat.cast_nonneg _) (dyadicCompanionScale_pos (by omega)).le
        (residualCofactorLocalProduct_pos (hE m hm).2.1).le
    · rw [sourceAllocated_real_length]
      exact sourceRequestedIntervalLength_ge_proxy (by positivity)
  · intro m hm n hn hmn
    exact sourceAllocated_primeIntervals_disjoint (dyadicAllocatedLength a D r) _ hm hn hmn

end

end Erdos4b.SmoothParameters
