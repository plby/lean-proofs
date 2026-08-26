/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceDyadicResidualFiberWeighted
import ErdosProblems.Erdos4b.SourceResidualAllocationCost

/-!
# Sieve bounds for the discarded lower boundary primes

Boundary membership retains both primality and the residual coprimality
condition. The estimate is uniform in the original interval endpoint.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

def residualPrimeFiberBelow (U y z m H : ℕ) : Finset ℕ :=
  (residualPrimeFiber U y z m).filter (· < H)

theorem residualPrimeFiberBelow_subset {U y z m H : ℕ} (hm : 0 < m) :
    residualPrimeFiberBelow U y z m H ⊆ residualPrimeFiber (m * H) y z m := by
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  have hd := mem_residualPrimeFiber.mp hp'.1
  exact mem_residualPrimeFiber.mpr
    ⟨hp'.2.le.trans (Nat.le_mul_of_pos_left H hm), hd.2.1, hd.2.2.1,
      Nat.mul_le_mul_left m hp'.2.le, hd.2.2.2.2⟩

namespace SmoothParameters

open Filter
open scoped Topology

theorem exists_uniform_dyadicBoundaryPrimeCount_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℕ, ∀ᶠ r in atTop, ∀ U m H : ℕ,
      0 < m → Even m → residualPrimeFrontier a r ≤ H →
      (residualPrimeFiberBelow U (smoothFrontier r) (residualPrimeFrontier a r) m H).card ≤
        C * H / (dyadicAmbientScale a r * dyadicCompanionScale r *
          residualCofactorLocalProduct (smoothFrontier r) m) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_dyadicResidualPrimeFiber_weighted_endpoint_bound
  refine ⟨C, hC, ?_⟩
  intro a
  filter_upwards [hbound a] with r hr
  intro U m H hm heven hzH
  have hdiv : m * H / m = H := Nat.mul_div_cancel_left H hm
  have hf := hr (m * H) m hm heven (by simpa only [hdiv] using hzH)
  rw [hdiv] at hf
  have hR := residualCofactorLocalProduct_pos (y := smoothFrontier r) heven
  have hcard : ((residualPrimeFiberBelow U (smoothFrontier r)
      (residualPrimeFrontier a r) m H).card : ℝ) ≤
      (residualPrimeFiber (m * H) (smoothFrontier r) (residualPrimeFrontier a r) m).card := by
    exact_mod_cast Finset.card_le_card
      (residualPrimeFiberBelow_subset (U := U) (y := smoothFrontier r)
        (z := residualPrimeFrontier a r) (H := H) hm)
  rw [← div_div]
  apply (le_div_iff₀ hR).mpr
  simpa only [mul_comm] using (mul_le_mul_of_nonneg_left hcard hR.le).trans hf

theorem exists_uniform_sum_dyadicBoundaryPrimeCount_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℕ, ∀ᶠ r in atTop, ∀ (U H B : ℕ) (E : Finset ℕ),
      1 ≤ B → (∀ m ∈ E, 0 < m ∧ Even m ∧ m ≤ B) → residualPrimeFrontier a r ≤ H →
      (∑ m ∈ E, ((residualPrimeFiberBelow U (smoothFrontier r)
        (residualPrimeFrontier a r) m H).card : ℝ)) ≤
        8 * C * H * B * (1 + Real.log B) /
          (dyadicAmbientScale a r * dyadicCompanionScale r) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_dyadicBoundaryPrimeCount_bound
  refine ⟨C, hC, ?_⟩
  intro a
  filter_upwards [hbound a, eventually_ge_atTop 1] with r hr hrpos
  intro U H B E hB hE hzH
  have hV : 0 < dyadicAmbientScale a r := lt_of_lt_of_le (by norm_num)
    (one_le_dyadicAmbientScale a r)
  have hL : 0 < dyadicCompanionScale r := dyadicCompanionScale_pos (by omega)
  calc
    _ ≤ ∑ m ∈ E, C * H / (dyadicAmbientScale a r * dyadicCompanionScale r *
        residualCofactorLocalProduct (smoothFrontier r) m) :=
      Finset.sum_le_sum fun m hm ↦ hr U m H (hE m hm).1 (hE m hm).2.1 hzH
    _ = (C * H / (dyadicAmbientScale a r * dyadicCompanionScale r)) *
        (∑ m ∈ E, (1 : ℝ) / residualCofactorLocalProduct (smoothFrontier r) m) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      ring
    _ ≤ (C * H / (dyadicAmbientScale a r * dyadicCompanionScale r)) *
        (8 * (B : ℝ) * (1 + Real.log B)) :=
      mul_le_mul_of_nonneg_left (sum_residualCofactorInverse_le hB hE) (by positivity)
    _ = _ := by ring

end SmoothParameters

end

end Erdos4b
