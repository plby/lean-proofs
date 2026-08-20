import ErdosProblems.Erdos980.NaturalChebotarev.PrimeIdealTheorem.AnalyticAssembly
import ErdosProblems.Erdos980.NaturalChebotarev.PrimeIdealTheorem.CoefficientLSeries
import ErdosProblems.Erdos980.NaturalChebotarev.PrimeIdealTheorem.TauberianAssembly

/-!
# The weighted prime ideal theorem

The coefficient Dirichlet series, the zero-free boundary theorem, pole subtraction, and
Wiener--Ikehara are assembled here to prove `ψₖ(x) ~ x` for every number field `K`.
-/

namespace Erdos980.NaturalChebotarev.PrimeIdealTheorem

open Asymptotics Complex Filter LSeries Set
open scoped Topology

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- The inclusive prime-ideal Chebyshev function satisfies `ψₖ(N) / N → 1`. -/
theorem primeIdealChebyshev_div_tendsto :
    Tendsto
      (fun N : ℕ ↦ Chebotarev.primeIdealChebyshev K N / (N : ℝ))
      atTop (nhds 1) := by
  obtain ⟨G, hG, hGlog⟩ := exists_continuous_dedekindZeta_logDeriv_sub_pole K
  apply primeIdealChebyshev_div_tendsto_of_continuousExtension K
      (G := G)
      (summable_nterm_primeIdealVonMangoldtCoeff K) hG
  intro s hs
  change G s =
    LSeries (fun n ↦ (Chebotarev.primeIdealVonMangoldtCoeff K n : ℂ)) s -
      1 / (s - 1)
  rw [LSeries_primeIdealVonMangoldtCoeff_eq_neg_logDeriv K hs]
  exact hGlog hs

/-- Asymptotic-equivalence form of the weighted prime ideal theorem. -/
theorem primeIdealChebyshev_isEquivalent :
    Chebotarev.primeIdealChebyshev K ~[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
  have hden : ∀ᶠ N : ℕ in atTop, (N : ℝ) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hN))
  apply (isEquivalent_iff_tendsto_one hden).2
  exact primeIdealChebyshev_div_tendsto K

end

end Erdos980.NaturalChebotarev.PrimeIdealTheorem
