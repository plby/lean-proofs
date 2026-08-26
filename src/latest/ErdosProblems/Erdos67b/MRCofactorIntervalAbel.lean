import ErdosProblems.Erdos67b.MRCofactorTwistedPrefix

/-! # Finite Abel bounds on a general cofactor interval -/

open scoped BigOperators ComplexConjugate

namespace Erdos67b

open LSeriesLogPhaseBridge

noncomputable section

theorem mrNorm_intervalHarmonicSum_le_of_positivePrefixes
    (a : ℕ → ℂ) {Y U : ℕ} (hY : 0 < Y) (hYU : Y ≤ U)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hprefix : ∀ Z ∈ Finset.Icc Y U, ‖positivePrefixSum a Z‖ / (Z : ℝ) ≤ epsilon) :
    ‖∑ n ∈ Finset.Ioc Y U, a n / (n : ℂ)‖ ≤
      epsilon * ((Y : ℝ) + U) / ((Y : ℝ) + 1) := by
  by_cases hlt : Y < U
  · have hYreal : (0 : ℝ) < Y := by exact_mod_cast hY
    have hsumY : ‖positivePrefixSum a Y‖ ≤ epsilon * Y :=
      (div_le_iff₀ hYreal).1 (hprefix Y (Finset.mem_Icc.2 ⟨le_rfl, hYU⟩))
    have hset (Z : ℕ) : Finset.Icc (Y + 1) Z = Finset.Ioc Y Z := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      omega
    have hraw : ∀ Z ∈ Finset.Icc (Y + 1) U,
        ‖complexIntervalPartialSum a (Y + 1) Z‖ ≤ epsilon * ((Y : ℝ) + U) := by
      intro Z hZ
      have hYZ : Y ≤ Z := by have := (Finset.mem_Icc.1 hZ).1; omega
      have hZU := (Finset.mem_Icc.1 hZ).2
      have hZreal : (0 : ℝ) < Z := by exact_mod_cast hY.trans_le hYZ
      have hsumZ : ‖positivePrefixSum a Z‖ ≤ epsilon * Z :=
        (div_le_iff₀ hZreal).1 (hprefix Z (Finset.mem_Icc.2 ⟨hYZ, hZU⟩))
      unfold complexIntervalPartialSum
      rw [hset, sum_Ioc_eq_positivePrefixSum_sub a hYZ]
      calc
        _ ≤ ‖positivePrefixSum a Z‖ + ‖positivePrefixSum a Y‖ := norm_sub_le _ _
        _ ≤ epsilon * Z + epsilon * Y := add_le_add hsumZ hsumY
        _ ≤ epsilon * ((Y : ℝ) + U) := by
          have hcast : (Z : ℝ) ≤ U := by exact_mod_cast hZU
          nlinarith
    have hAbel := norm_sum_Icc_mul_le_of_prefix_bound a (fun n ↦ (n : ℝ)⁻¹)
      (Nat.succ_le_of_lt hlt) (show 0 ≤ epsilon * ((Y : ℝ) + U) by positivity)
      (show 0 ≤ (U : ℝ)⁻¹ by positivity)
      (fun n hn ↦ inv_anti₀ (by
        have hnY := (Finset.mem_Ico.1 hn).1
        exact_mod_cast (show 0 < n by omega)) (by exact_mod_cast Nat.le_succ n)) hraw
    have heq : (∑ n ∈ Finset.Ioc Y U, a n / (n : ℂ)) =
        ∑ n ∈ Finset.Icc (Y + 1) U, a n * (((n : ℝ)⁻¹ : ℝ) : ℂ) := by
      rw [hset]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Complex.ofReal_inv, Complex.ofReal_natCast, div_eq_mul_inv]
    rw [heq]
    simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, div_eq_mul_inv] using hAbel
  · have hEq : U = Y := by omega
    subst U
    simp only [Finset.Ioc_self, Finset.sum_empty, norm_zero]
    positivity

theorem mrCofactor_intervalPolynomial_eq_untwistedHarmonicSum {ι : Type*}
    (A : Finset ℕ) (J : Finset ι) (B : ι → Finset ℕ) (f : ℕ → ℂ) (Y U : ℕ) (t : ℝ) :
    logarithmicDirichletPolynomial (Finset.Ioc Y U)
        (fun n ↦ mrIndexedTypicalCofactorCoefficient A J B f n / (n : ℂ)) (-t) =
      ∑ n ∈ Finset.Ioc Y U,
        mrIndexedTypicalCofactorCoefficient A J B (archimedeanUntwist f t) n / (n : ℂ) := by
  unfold logarithmicDirichletPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : 0 < n := (Nat.zero_le Y).trans_lt (Finset.mem_Ioc.1 hn).1
  rw [mrIndexedTypicalCofactor_untwist_apply A J B f t hnpos,
    logarithmicPhase_eq_archimedeanTwist hnpos, archimedeanTwist_neg]
  ring

theorem mrNorm_cofactor_intervalPolynomial_le_of_untwistedPrefixes {ι : Type*}
    (A : Finset ℕ) (J : Finset ι) (B : ι → Finset ℕ) (f : ℕ → ℂ)
    {Y U r : ℕ} (hY : 0 < Y) (hYU : Y ≤ U) (hratio : U ≤ r * Y)
    (t : ℝ) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hprefix : ∀ Z ∈ Finset.Icc Y U,
      ‖positivePrefixSum (mrIndexedTypicalCofactorCoefficient A J B (archimedeanUntwist f t)) Z‖ /
        (Z : ℝ) ≤ epsilon) :
    ‖logarithmicDirichletPolynomial (Finset.Ioc Y U)
      (fun n ↦ mrIndexedTypicalCofactorCoefficient A J B f n / (n : ℂ)) (-t)‖ ≤
        ((r : ℝ) + 1) * epsilon := by
  rw [mrCofactor_intervalPolynomial_eq_untwistedHarmonicSum]
  apply (mrNorm_intervalHarmonicSum_le_of_positivePrefixes _ hY hYU hepsilon hprefix).trans
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (Y : ℝ) + 1)).2
  have hcast : (U : ℝ) ≤ (r : ℝ) * Y := by exact_mod_cast hratio
  have hmul := mul_le_mul_of_nonneg_left hcast hepsilon
  have hnonneg : 0 ≤ ((r : ℝ) + 1) * epsilon := by positivity
  nlinarith

end

end Erdos67b
