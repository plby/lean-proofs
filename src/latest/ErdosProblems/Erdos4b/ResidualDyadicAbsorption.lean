/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.ResidualDyadicParameters
import ErdosProblems.Erdos4b.ResidualPrimeFiberAbsorption

/-!
# Residual-prime fibre bound on the exact dyadic ray

This module inserts the exact power-of-two parameters into the finite
beta-sieve/Mertens/Bombieri--Vinogradov estimate.  The hypotheses
z ≤ U / m, 2 ≤ U / m, and the logarithmic lower bound are discharged
uniformly from the factorization U = z * B.
-/

namespace Erdos4b
namespace SmoothParameters

noncomputable section

open scoped BigOperators

theorem smoothFrontier_one_lt {r : ℕ} (hr : 0 < r) :
    1 < smoothFrontier r := by
  rw [smoothFrontier]
  apply one_lt_pow₀ (by norm_num)
  rw [smoothExponent]
  exact (Nat.mul_pos hr (rankinDenominator_pos r)).ne'

/-- The complete residual-prime-fibre estimate after substituting the exact
dyadic endpoints.  The only remaining hypotheses are the chosen finite sieve
depth and the one prime-level witness at the lower endpoint. -/
theorem exists_sum_residualPrimeFiber_dyadic_absorbed_upper_bound :
    ∃ Aβ Cπ CV : ℝ,
      1 ≤ Aβ ∧ 0 < Cπ ∧ 0 < CV ∧
      ∀ {theta Bexp CBV : ℝ} {X₀ S Aco a r : ℕ},
        0 ≤ theta → 0 ≤ Bexp → 0 < Aco →
        Aco ≤ fullResidualCofactorCutoff r → 0 < r → 101 ≤ S →
        Real.log Aβ ≤ 2 * (S - 100 : ℕ) / 99 →
        BoundedGaps.Maynard.PrimeLevelWitness theta Bexp CBV X₀ →
        X₀ ≤ residualPrimeFrontier a r →
        smoothFrontier r ^ S ≤
          BoundedGaps.Maynard.modulusCutoff theta
            (residualPrimeFrontier a r) →
        let eta := (4 * Aβ / 3) * (1 / 4 : ℝ) ^ (S - 100)
        let U := intervalLength a r
        let y := smoothFrontier r
        let z := residualPrimeFrontier a r
        let Bco := fullResidualCofactorCutoff r
        let L := Real.log (z : ℝ)
        (∑ m ∈ residualEvenCofactors Aco Bco,
          ((residualPrimeFiber U y z m).card : ℝ)) ≤
          (Cπ * (1 + eta) * CV * (U : ℝ) /
              (L * Real.log (y : ℝ))) *
            (4 * (1 + Real.log ((Bco : ℝ) / Aco))) +
          (Bco : ℝ) *
            (CBV * (U : ℝ) / Real.rpow L Bexp +
              CBV * (z : ℝ) / Real.rpow L Bexp) := by
  obtain ⟨Aβ, Cπ, CV, hAβ, hCπ, hCV, hbound⟩ :=
    exists_sum_residualPrimeFiber_absorbed_upper_bound
  refine ⟨Aβ, Cπ, CV, hAβ, hCπ, hCV, ?_⟩
  intro theta Bexp CBV X₀ S Aco a r htheta hBexp hAco hABco hr hS
    hlogAβ hw hXz hDz
  dsimp only
  let U := intervalLength a r
  let y := smoothFrontier r
  let z := residualPrimeFrontier a r
  let Bco := fullResidualCofactorCutoff r
  let L := Real.log (z : ℝ)
  have hy : 1 < y := by
    simpa [y] using smoothFrontier_one_lt hr
  have hz : 1 < z := by
    simpa [z] using residualPrimeFrontier_one_lt a r
  have hL : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast hz)
  have hparams : ∀ m ∈ residualEvenCofactors Aco Bco,
      z ≤ U / m ∧ X₀ ≤ U / m ∧
      y ^ S ≤ BoundedGaps.Maynard.modulusCutoff theta (U / m) ∧
      2 ≤ U / m := by
    intro m hm
    have hmData := mem_residualEvenCofactors.mp hm
    have hmPos : 0 < m := lt_trans hAco hmData.1
    have hzle : z ≤ U / m := by
      simpa [z, U, Bco] using
        (residualPrimeFrontier_le_intervalLength_div
          (a := a) (r := r) hmPos hmData.2.1)
    refine ⟨hzle, hXz.trans hzle, ?_, hz.trans_le hzle⟩
    exact hDz.trans
      (BoundedGaps.Maynard.modulusCutoff_mono htheta hzle)
  have hlog : ∀ m ∈ Finset.Ioc Aco Bco,
      L ≤ Real.log ((U / m : ℕ) : ℝ) := by
    intro m hm
    have hmData := Finset.mem_Ioc.mp hm
    have hmPos : 0 < m := lt_trans hAco hmData.1
    simpa [L, z, U, Bco] using
      (log_residualPrimeFrontier_le_log_intervalLength_div
        (a := a) (r := r) hmPos hmData.2)
  have hresult := hbound hBexp hAco hABco hL hL hy hS hlogAβ hw
    hXz hDz hparams hlog le_rfl
  simpa [U, y, z, Bco, L] using hresult

end

end SmoothParameters
end Erdos4b
