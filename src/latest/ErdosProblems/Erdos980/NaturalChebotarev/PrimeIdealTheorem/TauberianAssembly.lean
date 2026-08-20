import ErdosProblems.Erdos980.NaturalChebotarev.PrimeIdealTheorem.WeightedDefs
import ErdosProblems.Erdos980.NaturalChebotarev.PrimeIdealTheorem.WienerBridge

/-!
# Tauberian assembly for the prime-ideal Chebyshev function

This file turns the generic strict-partial-sum conclusion of Wiener--Ikehara into the
inclusive endpoint convention used by `Chebotarev.primeIdealChebyshev`.
-/

namespace Erdos980.NaturalChebotarev.PrimeIdealTheorem

open BigOperators Filter LSeries Set
open scoped Topology

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- Once the prime-ideal von Mangoldt Dirichlet series has the required pole-subtracted
continuous extension, the inclusive prime-ideal Chebyshev function has ratio limit one. -/
theorem primeIdealChebyshev_div_tendsto_of_continuousExtension
    {G : ℂ → ℂ}
    (hsummable : ∀ σ : ℝ, 1 < σ →
      Summable (nterm (fun n ↦ (Chebotarev.primeIdealVonMangoldtCoeff K n : ℂ)) σ))
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G
      (fun s ↦
        LSeries (fun n ↦ (Chebotarev.primeIdealVonMangoldtCoeff K n : ℂ)) s -
          1 / (s - 1))
      {s | 1 < s.re}) :
    Tendsto
      (fun N : ℕ ↦ Chebotarev.primeIdealChebyshev K N / (N : ℝ))
      atTop (nhds 1) := by
  have hstrict :
      Tendsto
        (fun N : ℕ ↦
          (∑ n ∈ Finset.range N, Chebotarev.primeIdealVonMangoldtCoeff K n) / (N : ℝ))
        atTop (nhds 1) :=
    wienerIkehara_sum_range_div_tendsto
      (f := Chebotarev.primeIdealVonMangoldtCoeff K) (A := 1) (G := G)
      (Chebotarev.primeIdealVonMangoldtCoeff_nonneg K) hsummable hG hG'
  have hshift :
      Tendsto
        (fun N : ℕ ↦
          (∑ n ∈ Finset.range (N + 1),
            Chebotarev.primeIdealVonMangoldtCoeff K n) / ((N + 1 : ℕ) : ℝ))
        atTop (nhds 1) :=
    hstrict.comp (tendsto_add_atTop_nat 1)
  have hscale : Tendsto (fun N : ℕ ↦ (((N + 1 : ℕ) : ℝ) / (N : ℝ)))
      atTop (nhds 1) := by
    have hlim : Tendsto (fun N : ℕ ↦ 1 + 1 / (N : ℝ)) atTop (nhds (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
    have heq :
        (fun N : ℕ ↦ (((N + 1 : ℕ) : ℝ) / (N : ℝ))) =ᶠ[atTop]
          (fun N : ℕ ↦ 1 + 1 / (N : ℝ)) := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hN0 : (N : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hN))
      push_cast
      field_simp
    simpa using hlim.congr' heq.symm
  have hprod := hshift.mul hscale
  have hprod' :
      Tendsto
        (fun N : ℕ ↦
          (∑ n ∈ Finset.range (N + 1),
            Chebotarev.primeIdealVonMangoldtCoeff K n) / ((N + 1 : ℕ) : ℝ) *
              (((N + 1 : ℕ) : ℝ) / (N : ℝ)))
        atTop (nhds 1) := by simpa using hprod
  apply hprod'.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [Chebotarev.primeIdealChebyshev]
  have hN0 : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hN))
  have hN10 : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

end

end Erdos980.NaturalChebotarev.PrimeIdealTheorem
