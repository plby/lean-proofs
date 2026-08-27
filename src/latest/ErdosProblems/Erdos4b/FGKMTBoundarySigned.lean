/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTBoundaryMass

/-!
# The signed pre-sieve factor

The absolutely convergent sum of the boundary correction is exactly
the totient density. This identifies the small-prime contribution to
the harmonic main constant without discarding its sign.
-/

namespace Erdos4b.FGKMT

noncomputable section

open ArithmeticFunction Filter
open scoped BigOperators Topology

theorem preSieveBoundary_local_tsum (M : ℕ) {p : ℕ} (hp : p.Prime) :
    (∑' j, preSieveBoundary M (p ^ j)) =
      if p ∣ M then 1 - 1 / (p : ℝ) else 1 := by
  rw [tsum_eq_sum (s := Finset.range 2) (fun j hj => by
    have hj2 : 2 ≤ j := by simpa only [Finset.mem_range, not_lt] using hj
    exact preSieveBoundary_prime_pow_ge_two M hp hj2)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add]
  rw [(preSieveBoundary_isMultiplicative M).map_one, preSieveBoundary_prime M hp]
  split_ifs <;> ring

theorem primeFactors_eq_filtered_primesBelow {M N : ℕ} (hM : 0 < M) (hN : M < N) :
    N.primesBelow.filter (fun p => p ∣ M) = M.primeFactors := by
  ext p
  constructor
  · intro hp
    obtain ⟨hpN, hpM⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primesBelow hpN, hpM, hM.ne'⟩
  · intro hp
    obtain ⟨hpPrime, hpM, _⟩ := Nat.mem_primeFactors.mp hp
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_primesBelow.mpr ⟨(Nat.le_of_dvd hM hpM).trans_lt hN, hpPrime⟩, hpM⟩

theorem primeFactors_totientProduct {M : ℕ} (hM : 0 < M) :
    (∏ p ∈ M.primeFactors, (1 - 1 / (p : ℝ))) = (M.totient : ℝ) / M := by
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hphi : (M.totient : ℝ) =
      (M : ℝ) * ∏ p ∈ M.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) (Nat.totient_eq_mul_prod_factors M)
    push_cast at h
    exact h
  apply (eq_div_iff hM0).2
  rw [hphi]
  simp only [one_div]
  ring

theorem preSieveBoundary_tsum_eq_totientDensity {M : ℕ} (hM : 0 < M) :
    (∑' n, preSieveBoundary M n) = (M.totient : ℝ) / M := by
  have hnorm : Summable (fun n => ‖preSieveBoundary M n‖) := by
    simpa only [Real.norm_eq_abs] using (preSieveBoundary_absolute_sum_bound hM.ne').1
  have hEuler := (preSieveBoundary_isMultiplicative M).eulerProduct hnorm
  have hprod : ∀ N : ℕ, M < N →
      (∏ p ∈ N.primesBelow, ∑' j, preSieveBoundary M (p ^ j)) =
        (M.totient : ℝ) / M := by
    intro N hN
    calc
      _ = ∏ p ∈ N.primesBelow, (if p ∣ M then 1 - 1 / (p : ℝ) else 1) := by
        apply Finset.prod_congr rfl
        intro p hp
        exact preSieveBoundary_local_tsum M (Nat.prime_of_mem_primesBelow hp)
      _ = ∏ p ∈ N.primesBelow.filter (fun p => p ∣ M), (1 - 1 / (p : ℝ)) := by
        rw [Finset.prod_filter]
      _ = (M.totient : ℝ) / M := by
        rw [primeFactors_eq_filtered_primesBelow hM hN, primeFactors_totientProduct hM]
  have hevent : (fun N : ℕ => ∏ p ∈ N.primesBelow,
      ∑' j, preSieveBoundary M (p ^ j)) =ᶠ[atTop] (fun _ => (M.totient : ℝ) / M) := by
    filter_upwards [eventually_ge_atTop (M + 1)] with N hN
    exact hprod N (by omega)
  exact tendsto_nhds_unique hEuler (tendsto_const_nhds.congr' hevent.symm)

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.preSieveBoundary_tsum_eq_totientDensity
