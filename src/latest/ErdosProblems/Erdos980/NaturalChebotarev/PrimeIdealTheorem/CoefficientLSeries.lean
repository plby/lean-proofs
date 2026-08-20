/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos980.NaturalChebotarev.PrimeIdealTheorem.WeightedDefs
import ErdosProblems.Erdos980.NaturalChebotarev.IdealMangoldt.Analytic
import PrimeNumberTheoremAnd.Wiener

/-!
# The Dirichlet series of the prime-ideal von Mangoldt coefficient

This file identifies the explicitly bounded coefficient from `WeightedDefs` with the canonical
norm-fiber coefficient from `IdealMangoldt`.  It then transports the absolutely convergent
prime-power expansion of the latter to obtain

`L(Λ_K, s) = -ζ'_K(s) / ζ_K(s)` for `1 < re s`.
-/

noncomputable section

open NumberField
open scoped BigOperators

namespace Erdos980.NaturalChebotarev.PrimeIdealTheorem

variable (K : Type*) [Field K] [NumberField K]

private abbrev BoundedPrime (n : ℕ) :=
  {𝔭 : Ideal (𝓞 K) //
    𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ Ideal.absNorm 𝔭 ≤ n}

private abbrev BoundedExponent (n : ℕ) :=
  {m : ℕ // m ∈ Finset.Icc 1 n}

private abbrev ContributingPair (n : ℕ) :=
  {z : BoundedPrime K n × BoundedExponent n //
    Ideal.absNorm z.1.1 ^ z.2.1 = n}

/-- The bounded pairs used in `Chebotarev.primeIdealVonMangoldtCoeff` are exactly the
prime-ideal powers in the canonical norm fiber. -/
private def contributingPairEquivNormFiber (n : ℕ) :
    ContributingPair K n ≃ IdealMangoldt.normFiber K n where
  toFun z := {
    val := {
      val := (⟨z.1.1.1, z.1.1.2.1, z.1.1.2.2.1⟩, z.1.2.1)
      property := (Finset.mem_Icc.mp z.1.2.2).1
    }
    property := z.2
  }
  invFun x := {
    val :=
      (⟨x.1.prime, x.1.prime_isPrime, x.1.prime_ne_bot,
          x.1.absNorm_prime_le_norm.trans_eq x.2⟩,
        ⟨x.1.exponent, Finset.mem_Icc.mpr
          ⟨x.1.exponent_pos, x.1.exponent_le_norm.trans_eq x.2⟩⟩)
    property := x.2
  }
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      rfl
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · rfl

/-- The bounded finite coefficient agrees with the canonical norm-fiber coefficient. -/
theorem primeIdealVonMangoldtCoeff_eq_idealMangoldt (n : ℕ) :
    Chebotarev.primeIdealVonMangoldtCoeff K n = IdealMangoldt.idealMangoldt K n := by
  classical
  let _ : Finite (BoundedPrime K n) :=
    (Chebotarev.primeIdealsUpToSet_finite K n).to_subtype
  let _ : Fintype (BoundedPrime K n) := Fintype.ofFinite _
  rw [Chebotarev.primeIdealVonMangoldtCoeff_eq]
  rw [Finset.sum_subtype (Chebotarev.primeIdealsUpTo K n)
    (fun 𝔭 ↦ Chebotarev.mem_primeIdealsUpTo (K := K))
    (fun 𝔭 ↦ ∑ m ∈ Finset.Icc 1 n,
      if Ideal.absNorm 𝔭 ^ m = n then Real.log (Ideal.absNorm 𝔭 : ℝ) else 0)]
  simp_rw [Finset.sum_subtype (Finset.Icc 1 n) (fun _ ↦ Iff.rfl)]
  rw [← Fintype.sum_prod_type (fun z : BoundedPrime K n × BoundedExponent n ↦
    if Ideal.absNorm z.1.1 ^ z.2.1 = n
    then Real.log (Ideal.absNorm z.1.1 : ℝ) else 0)]
  rw [← Finset.sum_filter
    (fun z : BoundedPrime K n × BoundedExponent n ↦
      Ideal.absNorm z.1.1 ^ z.2.1 = n)
    (fun z ↦ Real.log (Ideal.absNorm z.1.1 : ℝ))]
  rw [Finset.sum_subtype
    (p := fun z : BoundedPrime K n × BoundedExponent n ↦
      Ideal.absNorm z.1.1 ^ z.2.1 = n)
    (Finset.univ.filter
      (fun z : BoundedPrime K n × BoundedExponent n ↦
        Ideal.absNorm z.1.1 ^ z.2.1 = n))
    (fun _ ↦ by simp)
    (fun z ↦ Real.log (Ideal.absNorm z.1.1 : ℝ))]
  exact Fintype.sum_equiv (contributingPairEquivNormFiber K n)
    (fun z : ContributingPair K n ↦ Real.log (Ideal.absNorm z.1.1.1 : ℝ))
    (fun x : IdealMangoldt.normFiber K n ↦ x.1.weight)
    (fun _ ↦ rfl)

/-- Absolute convergence of the `nterm` majorant required by the Wiener--Ikehara bridge. -/
theorem summable_nterm_primeIdealVonMangoldtCoeff (σ : ℝ) (hσ : 1 < σ) :
    Summable (nterm (fun n ↦ (Chebotarev.primeIdealVonMangoldtCoeff K n : ℂ)) σ) := by
  have hL : LSeriesSummable
      (fun n ↦ (Chebotarev.primeIdealVonMangoldtCoeff K n : ℂ)) (σ : ℂ) := by
    simpa only [primeIdealVonMangoldtCoeff_eq_idealMangoldt] using
      (IdealMangoldt.lSeriesSummable_idealMangoldt K (s := (σ : ℂ)) (by simpa using hσ))
  exact hL.norm.congr fun n ↦ (nterm_eq_norm_term (n := n) (σ' := σ)).symm

/-- The Dirichlet series of the bounded prime-ideal von Mangoldt coefficient is the negative
logarithmic derivative of the Dedekind zeta function on `re s > 1`. -/
theorem LSeries_primeIdealVonMangoldtCoeff_eq_neg_logDeriv {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n ↦ (Chebotarev.primeIdealVonMangoldtCoeff K n : ℂ)) s =
      -(logDeriv (NumberField.dedekindZeta K) s) := by
  simpa only [primeIdealVonMangoldtCoeff_eq_idealMangoldt] using
    IdealMangoldt.LSeries_idealMangoldt_eq_neg_logDeriv K hs

end Erdos980.NaturalChebotarev.PrimeIdealTheorem
