/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos980.NaturalChebotarev.IdealMangoldt.Analytic
import ErdosProblems.Erdos980.NaturalChebotarev.PrimeIdealTheorem.PoleSubtraction
import ErdosProblems.Erdos980.NaturalChebotarev.PrimeIdealTheorem.WienerBridge
import ErdosProblems.Erdos980.NaturalChebotarev.PrimeIdealTheorem.ZeroFreeLine

/-!
# The weighted prime ideal theorem

This file combines the prime-ideal von Mangoldt Dirichlet series, the zero-free
line for Dedekind zeta, pole subtraction, and Wiener--Ikehara.  The result is
the unconditional weighted prime ideal theorem for every number field.
-/

namespace Erdos980.NaturalChebotarev.PrimeIdealTheorem

open Asymptotics BigOperators Filter Set
open scoped Topology

noncomputable section

/-- The strict partial sums of the norm-collapsed ideal von Mangoldt
coefficient have mean value one. -/
theorem idealMangoldt_sum_range_div_tendsto
    (K : Type*) [Field K] [NumberField K] :
    Tendsto
      (fun N : ℕ ↦
        (∑ n ∈ Finset.range N, IdealMangoldt.idealMangoldt K n) / (N : ℝ))
      atTop (nhds 1) := by
  obtain ⟨G, hG, hG'⟩ :=
    PoleSubtraction.exists_continuous_poleSubtractedDedekindLogDeriv K
      (fun s hs hs1 ↦ continuedDedekindZeta_ne_zero_of_one_le_re K hs hs1)
  apply wienerIkehara_sum_range_div_tendsto
      (f := IdealMangoldt.idealMangoldt K) (A := 1) (G := G)
  · exact IdealMangoldt.idealMangoldt_nonnegative K
  · intro σ hσ
    exact IdealMangoldt.summable_nterm_idealMangoldt K hσ
  · simpa [PoleSubtraction.closedOneHalfPlane] using hG
  · intro s hs
    have hseries := IdealMangoldt.LSeries_idealMangoldt_eq_neg_logDeriv K hs
    change G s =
      LSeries (fun n ↦ (IdealMangoldt.idealMangoldt K n : ℂ)) s - 1 / (s - 1)
    rw [hseries]
    exact hG' (by simpa [PoleSubtraction.openOneHalfPlane] using hs)

/-- Equivalent asymptotic form of the weighted prime ideal theorem. -/
theorem idealMangoldt_sum_range_isEquivalent
    (K : Type*) [Field K] [NumberField K] :
    (fun N : ℕ ↦ ∑ n ∈ Finset.range N, IdealMangoldt.idealMangoldt K n)
      ~[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
  have hden : ∀ᶠ N : ℕ in atTop, (N : ℝ) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    positivity
  apply (Asymptotics.isEquivalent_iff_tendsto_one hden).2
  convert idealMangoldt_sum_range_div_tendsto K using 1
  rfl

end

end Erdos980.NaturalChebotarev.PrimeIdealTheorem
