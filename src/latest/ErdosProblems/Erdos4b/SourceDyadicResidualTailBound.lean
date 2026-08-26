/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceDyadicResidualFiberWeighted
import ErdosProblems.Erdos4b.SourceResidualAllocationCost
import ErdosProblems.Erdos4b.SourceDyadicAllocationScales

/-!
# Uniform residual-fibre mass over a multiplicative cofactor interval

The unconditional pointwise estimate is summed only after the cofactor
correction has been bounded by the reciprocal totient. No new error
multiplied by the number of cofactors is introduced.
-/

namespace Erdos4b.SmoothParameters

noncomputable section

open Filter
open scoped BigOperators Topology

theorem exists_uniform_sum_dyadicResidualPrimeFiber_interval_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ a D : ℕ, ∀ᶠ r in atTop,
      ∀ (A B : ℕ) (E : Finset ℕ), 0 < A → A ≤ B →
      B ≤ D * fullResidualCofactorCutoff r → E ⊆ Finset.Ioc A B → (∀ m ∈ E, Even m) →
      (∑ m ∈ E, ((residualPrimeFiber (D * intervalLength a r) (smoothFrontier r)
        (residualPrimeFrontier a r) m).card : ℝ)) ≤
        8 * C * (D * intervalLength a r : ℕ) * (1 + Real.log ((B : ℝ) / A)) /
          (dyadicAmbientScale a r * dyadicCompanionScale r) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_dyadicResidualPrimeFiber_cofactor_weighted_bound
  refine ⟨C, hC, ?_⟩
  intro a D
  filter_upwards [hbound a D, eventually_ge_atTop 1] with r hr hrpos
  intro A B E hA hAB hB hE heven
  have hV : 0 < dyadicAmbientScale a r := lt_of_lt_of_le (by norm_num)
    (one_le_dyadicAmbientScale a r)
  have hL : 0 < dyadicCompanionScale r := dyadicCompanionScale_pos (by omega)
  have hpoint : ∀ m ∈ E,
      ((residualPrimeFiber (D * intervalLength a r) (smoothFrontier r)
        (residualPrimeFrontier a r) m).card : ℝ) ≤
        (C / (dyadicAmbientScale a r * dyadicCompanionScale r)) *
          ((D * intervalLength a r / m : ℕ) /
            residualCofactorLocalProduct (smoothFrontier r) m) := by
    intro m hm
    have hd := Finset.mem_Ioc.mp (hE hm)
    have hf := hr m (hA.trans hd.1) (heven m hm) (hd.2.trans hB)
    have hR := residualCofactorLocalProduct_pos (y := smoothFrontier r) (heven m hm)
    have hdiv := (le_div_iff₀ hR).mpr (show
        ((residualPrimeFiber (D * intervalLength a r) (smoothFrontier r)
          (residualPrimeFrontier a r) m).card : ℝ) *
          residualCofactorLocalProduct (smoothFrontier r) m ≤
        C * (D * intervalLength a r / m : ℕ) /
          (dyadicAmbientScale a r * dyadicCompanionScale r) by
      simpa only [mul_comm] using hf)
    apply hdiv.trans_eq
    ring
  calc
    _ ≤ ∑ m ∈ E, (C / (dyadicAmbientScale a r * dyadicCompanionScale r)) *
        ((D * intervalLength a r / m : ℕ) / residualCofactorLocalProduct (smoothFrontier r) m) :=
      Finset.sum_le_sum hpoint
    _ = (C / (dyadicAmbientScale a r * dyadicCompanionScale r)) *
        (∑ m ∈ E, (D * intervalLength a r / m : ℕ) /
          residualCofactorLocalProduct (smoothFrontier r) m) := (Finset.mul_sum _ _ _).symm
    _ ≤ (C / (dyadicAmbientScale a r * dyadicCompanionScale r)) *
        (8 * (D * intervalLength a r : ℕ) * (1 + Real.log ((B : ℝ) / A))) :=
      mul_le_mul_of_nonneg_left (sum_residualProxyEndpoint_interval_le hA hAB hE) (by positivity)
    _ = _ := by ring

theorem exists_uniform_sum_dyadicResidualPrimeFiber_total_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ a D : ℕ, 0 < D → ∀ᶠ r in atTop, ∀ E : Finset ℕ,
      (∀ m ∈ E, 0 < m ∧ Even m ∧ m ≤ D * fullResidualCofactorCutoff r) →
      (∑ m ∈ E, ((residualPrimeFiber (D * intervalLength a r) (smoothFrontier r)
        (residualPrimeFrontier a r) m).card : ℝ)) ≤
        C * D * ((primaryFrontier a r : ℝ) / dyadicAmbientScale a r) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_sum_dyadicResidualPrimeFiber_interval_bound
  refine ⟨80 * C, by positivity, ?_⟩
  intro a D hD
  filter_upwards [hbound a D, eventually_ge_atTop 1,
    eventually_dyadicAllocationPrincipalScale_le a hD] with r hr hrpos hscale
  intro E hE
  have hB : 1 ≤ D * fullResidualCofactorCutoff r :=
    Nat.succ_le_iff.mpr (Nat.mul_pos hD (fullResidualCofactorCutoff_pos (by omega)))
  have hsub : E ⊆ Finset.Ioc 1 (D * fullResidualCofactorCutoff r) := by
    intro m hm
    have hd := hE m hm
    have hm2 : 2 ≤ m := Nat.le_of_dvd hd.1 hd.2.1.two_dvd
    exact Finset.mem_Ioc.mpr ⟨by omega, hd.2.2⟩
  have hc := hr 1 (D * fullResidualCofactorCutoff r) E (by norm_num) hB le_rfl hsub
    (fun m hm ↦ (hE m hm).2.1)
  have hV : 0 < dyadicAmbientScale a r := lt_of_lt_of_le (by norm_num)
    (one_le_dyadicAmbientScale a r)
  calc
    _ ≤ 8 * C * (D * intervalLength a r : ℕ) *
        (1 + Real.log (D * fullResidualCofactorCutoff r : ℕ)) /
        (dyadicAmbientScale a r * dyadicCompanionScale r) := by
      simpa only [Nat.cast_one, div_one] using hc
    _ = (8 * C * D / dyadicAmbientScale a r) *
        ((intervalLength a r : ℝ) * (1 + Real.log (D * fullResidualCofactorCutoff r : ℕ)) /
          dyadicCompanionScale r) := by push_cast; ring
    _ ≤ (8 * C * D / dyadicAmbientScale a r) * (10 * (primaryFrontier a r : ℝ)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = _ := by ring

end

end Erdos4b.SmoothParameters
