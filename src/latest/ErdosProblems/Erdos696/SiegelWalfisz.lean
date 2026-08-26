import ErdosProblems.Erdos696.AnalyticDefinitions
import ErdosProblems.Erdos696.SiegelWalfiszScales
import ErdosProblems.Erdos696.PrimeCounting
import BoundedGaps.BombieriVinogradov.Analytic.SiegelWalfiszEndpointMaximum
import BoundedGaps.BombieriVinogradov.Analytic.CenteredPrimeCountingComposition
import BoundedGaps.PrimeNumberTheorem.Analytic.StrongChebyshev

/-!
# Siegel–Walfisz for the prime-counting function

The character estimate comes from the pinned `BoundedGaps` development.
This file transports it to the prime-counting convention used in Problem 696.
-/

namespace Erdos696

open BoundedGaps.Maynard Filter
open scoped BigOperators

/-- Uniform character cancellation also controls the inducing primitive
character, including its identically zero centered twist at conductor one. -/
theorem exists_inducingPrimitive_bound (A : ℝ) (hA : 0 < A) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∃ X₀ : ℕ, 4 ≤ X₀ ∧ ∀ x : ℕ, X₀ ≤ x →
        ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log (x : ℝ) ^ A →
          ∀ χ : DirichletCharacter ℂ q,
            inducingPrimitiveCenteredEndpointMaximum x q χ ≤
              C * ((x : ℝ) * Real.exp (-c * Real.sqrt (Real.log (x : ℝ)))) := by
  obtain ⟨C, c, hC, hc, X₀, hX₀, hbound⟩ :=
    exists_siegelWalfisz_primitiveCenteredEndpointMaximum_le A hA
  refine ⟨C, c, hC, hc, X₀, hX₀, ?_⟩
  intro x hx q hq hqLog χ
  letI : NeZero q := ⟨by omega⟩
  by_cases hd : χ.conductor = 1
  · have hzero : inducingPrimitiveCenteredEndpointMaximum x q χ = 0 := by
      have hz (d : ℕ) (ψ : primitiveCharacters d) (hd : d = 1) :
          primitiveCenteredEndpointMaximum x d ψ = 0 := by
        subst d
        exact primitiveCenteredEndpointMaximum_one x ψ
      unfold inducingPrimitiveCenteredEndpointMaximum
      exact hz _ _ hd
    rw [hzero]
    positivity
  · apply hbound x hx χ.conductor
      (by have := χ.conductor_ne_zero; omega)
    have hdq : (χ.conductor : ℝ) ≤ q := by
      exact_mod_cast Nat.le_of_dvd (by omega : 0 < q) χ.conductor_dvd_level
    exact hdq.trans hqLog

/-- The prime-counting discrepancy relative to the global prime count has
the Siegel–Walfisz error, plus explicit elementary correction terms. -/
theorem exists_centered_prime_count_bound (A : ℝ) (hA : 0 < A) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∃ X₀ : ℕ, 4 ≤ X₀ ∧ ∀ x : ℕ, X₀ ≤ x →
        ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log (x : ℝ) ^ A →
          maxProgressionDiscrepancy x q ≤ (Real.log 2)⁻¹ *
            (Real.log ((q * x : ℕ) : ℝ) ^ 2 +
              C * ((x : ℝ) * Real.exp (-c * Real.sqrt (Real.log (x : ℝ)))) +
              (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ))) := by
  obtain ⟨C, c, hC, hc, X₀, hX₀, hbound⟩ := exists_inducingPrimitive_bound A hA
  refine ⟨C, c, hC, hc, X₀, hX₀, ?_⟩
  intro x hx q hq hqLog
  letI : NeZero q := ⟨by omega⟩
  have hphi : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < q)).ne'
  have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    rw [← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have havg : (q.totient : ℝ)⁻¹ *
      (∑ χ : DirichletCharacter ℂ q, inducingPrimitiveCenteredEndpointMaximum x q χ) ≤
      C * ((x : ℝ) * Real.exp (-c * Real.sqrt (Real.log (x : ℝ)))) := by
    calc
      _ ≤ (q.totient : ℝ)⁻¹ *
          ∑ _χ : DirichletCharacter ℂ q,
            C * ((x : ℝ) * Real.exp (-c * Real.sqrt (Real.log (x : ℝ)))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum fun χ _ => hbound x hx q hq hqLog χ
      _ = _ := by simp [hcard, hphi, mul_assoc]
  have hx2 : 2 ≤ x := by omega
  calc
    _ ≤ (Real.log 2)⁻¹ * maxCenteredThetaProgressionDiscrepancyUpTo x q :=
      maxProgressionDiscrepancy_le_inv_log_two_mul_maxCenteredThetaUpTo hx2 hq
    _ ≤ (Real.log 2)⁻¹ * (maxCenteredProgressionDiscrepancyUpTo x q +
        (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ))) := by
      apply mul_le_mul_of_nonneg_left (maxCenteredThetaProgressionDiscrepancyUpTo_le hq)
      positivity
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add
        ((maxCenteredProgressionDiscrepancyUpTo_le_log_sq_add_primitive hx2 hq).trans
          (add_le_add le_rfl havg)) le_rfl

/-- All elementary correction terms can be absorbed without weakening the
exponential shape of the centered prime-counting estimate. -/
theorem exists_eventually_centered_prime_count_sw (A : ℝ) (hA : 0 < A) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ c ≤ 1 ∧
      ∀ᶠ x : ℕ in atTop, ∀ q : ℕ, 1 ≤ q →
        (q : ℝ) ≤ Real.log (x : ℝ) ^ A →
          maxProgressionDiscrepancy x q ≤ C * swError c x := by
  obtain ⟨C, c₀, hC, hc₀, X₀, hX₀, hbound⟩ := exists_centered_prime_count_bound A hA
  obtain ⟨K, hK⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let c := min c₀ 1
  have hc : 0 < c := lt_min hc₀ zero_lt_one
  have hc1 : c ≤ 1 := min_le_right _ _
  have hcc₀ : c ≤ c₀ := min_le_left _ _
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(Real.log 2)⁻¹ * (4 + C + max K 0), c, by positivity, hc, hc1, ?_⟩
  have hlogTop : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop X₀, hlogTop.eventually_ge_atTop 4,
    tendsto_natCast_atTop_atTop.eventually (eventually_log_rpow_le_sqrt A),
    tendsto_natCast_atTop_atTop.eventually (eventually_log_rpow_le_sqrt 2)]
    with x hx hlog hpow hlogSq
  intro q hq hqLog
  have hx4 : 4 ≤ x := hX₀.trans hx
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
  have hqx : (q : ℝ) ≤ x :=
    (hqLog.trans hpow).trans
      (Real.sqrt_le_iff.mpr ⟨hx0.le, by nlinarith only [hx1]⟩)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hlogs : Real.log ((q * x : ℕ) : ℝ) ≤ 2 * Real.log (x : ℝ) := by
    rw [Nat.cast_mul, Real.log_mul hq0.ne' hx0.ne']
    linarith only [Real.log_le_log hq0 hqx]
  have hlogNonneg : 0 ≤ Real.log ((q * x : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hlogSq' : Real.log (x : ℝ) ^ 2 ≤ Real.sqrt (x : ℝ) := by
    simpa only [Real.rpow_two] using hlogSq
  have hs := sqrt_le_swError hc1 hx0 hlog
  have herr : swError c₀ (x : ℝ) ≤ swError c x := swError_antitone hx0.le hcc₀
  have hlogBound : Real.log ((q * x : ℕ) : ℝ) ^ 2 ≤ 4 * swError c x := by
    have h := pow_le_pow_left₀ hlogNonneg hlogs 2
    nlinarith only [h, hlogSq', hs]
  have hprimePower : Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ) ≤
      max K 0 * swError c x := by
    calc
      _ ≤ K * Real.sqrt (x : ℝ) := hK _
      _ ≤ max K 0 * Real.sqrt (x : ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (le_max_right _ _)
  have hraw := hbound x hx q hq hqLog
  change maxProgressionDiscrepancy x q ≤
    (Real.log 2)⁻¹ * (Real.log ((q * x : ℕ) : ℝ) ^ 2 +
      C * swError c₀ x + (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ))) at hraw
  calc
    _ ≤ _ := hraw
    _ ≤ (Real.log 2)⁻¹ * (4 * swError c x +
        C * swError c x + max K 0 * swError c x) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hlog2.le)
      exact add_le_add (add_le_add hlogBound (mul_le_mul_of_nonneg_left herr hC.le))
        hprimePower
    _ = _ := by ring

lemma piMod_natCast_eq (x q a : ℕ) :
    piMod x q a = primeCountUpTo x q a := by
  classical
  have hset : {p : ℕ | p ≤ x ∧ p.Prime ∧ p % q = a % q} =
      ↑((Finset.range (x + 1)).filter (fun p => p.Prime ∧ p % q = a % q)) := by
    ext p
    simp [Nat.lt_succ_iff, and_assoc]
  rw [piMod, Nat.floor_natCast, hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  rfl

lemma piMod_centered_le_max (x q a : ℕ) (hq : 1 ≤ q) (ha : a.Coprime q) :
    |(piMod x q a : ℝ) - (Nat.primeCounting x : ℝ) / q.totient| ≤
      maxProgressionDiscrepancy x q := by
  classical
  have hq0 : 0 < q := by omega
  have haMem : a % q ∈ coprimeResidues q := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (Nat.mod_lt _ hq0), ?_⟩
    change (a % q).gcd q = 1
    rw [← Nat.gcd_rec, Nat.gcd_comm]
    exact ha
  have h := Finset.le_sup' (progressionDiscrepancy x q) haMem
  simpa only [maxProgressionDiscrepancy, dif_pos hq0, progressionDiscrepancy,
    primeCountTotal, piMod_natCast_eq, primeCountUpTo, Nat.mod_mod] using h

theorem exists_eventually_piMod_sw_nat (A : ℝ) (hA : 0 < A) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ c ≤ 1 ∧
      ∀ᶠ x : ℕ in atTop, ∀ q : ℕ, 1 ≤ q →
        (q : ℝ) ≤ Real.log (x : ℝ) ^ A → ∀ a : ℕ, a.Coprime q →
          |(piMod x q a : ℝ) - li x / q.totient| ≤ C * swError c x := by
  obtain ⟨C₁, c₁, hC₁, hc₁, hc₁1, hcenter⟩ := exists_eventually_centered_prime_count_sw A hA
  obtain ⟨C₂, c₂, hC₂, hc₂, hc₂1, hglobal⟩ := exists_eventually_primeCounting_sw
  let c := min c₁ c₂
  have hc : 0 < c := lt_min hc₁ hc₂
  refine ⟨C₁ + C₂, c, by positivity, hc, (min_le_left _ _).trans hc₁1, ?_⟩
  filter_upwards [hcenter, hglobal] with x hx hglob
  intro q hq hqLog a ha
  have hE₁ : swError c₁ x ≤ swError c x :=
    swError_antitone (Nat.cast_nonneg x) (min_le_left _ _)
  have hE₂ : swError c₂ x ≤ swError c x :=
    swError_antitone (Nat.cast_nonneg x) (min_le_right _ _)
  have hphi : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hcenter := (piMod_centered_le_max x q a hq ha).trans (hx q hq hqLog)
  have hglobal : |(Nat.primeCounting x : ℝ) / q.totient - li x / q.totient| ≤
      C₂ * swError c x := by
    rw [← sub_div, abs_div, abs_of_pos (lt_of_lt_of_le zero_lt_one hphi)]
    exact (div_le_self (abs_nonneg _) hphi).trans
      (hglob.trans (mul_le_mul_of_nonneg_left hE₂ hC₂.le))
  calc
    _ ≤ |(piMod x q a : ℝ) - (Nat.primeCounting x : ℝ) / q.totient| +
        |(Nat.primeCounting x : ℝ) / q.totient - li x / q.totient| := abs_sub_le _ _ _
    _ ≤ C₁ * swError c x + C₂ * swError c x :=
      add_le_add (hcenter.trans (mul_le_mul_of_nonneg_left hE₁ hC₁.le)) hglobal
    _ = _ := by ring

end Erdos696
