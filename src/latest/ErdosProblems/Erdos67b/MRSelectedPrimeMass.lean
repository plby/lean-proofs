import ErdosProblems.Erdos67b.MRGSA9FiniteEulerPositiveLine

/-!
# Positive Dirichlet mass of a finite selected prime set

The whole Euler product converges on the positive real half-line, since
the set of allowed primes is finite. This keeps the lower prime endpoint
available in reciprocal-mass and Rankin tail bounds.
-/

open scoped BigOperators

namespace Erdos67b

open MRHalaszBands

noncomputable section

open Classical in
def mrSelectedPrimeWeight (A : Finset ℕ) (sigma : ℝ) (n : ℕ) : ℝ :=
  if PrimeSupported (fun p ↦ p ∈ A) n then (n : ℝ) ^ (-sigma) else 0

theorem mrSelectedPrimeWeight_nonneg (A : Finset ℕ) (sigma : ℝ) (n : ℕ) :
    0 ≤ mrSelectedPrimeWeight A sigma n := by
  classical
  unfold mrSelectedPrimeWeight
  split_ifs <;> positivity

private theorem selectedPrimeWeight_cast (A : Finset ℕ) (sigma : ℝ) (n : ℕ) :
    (mrSelectedPrimeWeight A sigma n : ℂ) =
      LSeries.term (primeBandCoefficient (fun _ ↦ (1 : ℂ)) (fun p ↦ p ∈ A)) (sigma : ℂ) n := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [mrSelectedPrimeWeight, PrimeSupported]
  · rw [LSeries.term_of_ne_zero hn]
    unfold mrSelectedPrimeWeight primeBandCoefficient
    split_ifs
    · rw [Real.rpow_neg (Nat.cast_nonneg n), Complex.ofReal_inv,
        Complex.ofReal_cpow (Nat.cast_nonneg n)]
      simp
    · simp

theorem mrSummable_selectedPrimeWeight (A : Finset ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    Summable (mrSelectedPrimeWeight A sigma) := by
  have hm : IsMultiplicativeOnPositiveNat (fun _ : ℕ ↦ (1 : ℂ)) := by
    constructor
    · rfl
    · intro m n hm hn hcop
      simp
  have hs := primeBandCoefficient_LSeriesSummable_of_pos_re hm (by simp)
    (fun p ↦ p ∈ A) (A.sup id) (fun p hp ↦ Finset.le_sup (f := id) hp)
    (s := (sigma : ℂ)) (by simpa using hsigma)
  apply Complex.summable_ofReal.mp
  change Summable (LSeries.term _ _) at hs
  exact hs.congr (fun n ↦ (selectedPrimeWeight_cast A sigma n).symm)

private theorem localEulerFactor_one_real {p : ℕ} (hp : p.Prime)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    gsA9LocalEulerFactor (fun _ : ℕ ↦ (1 : ℂ)) (sigma : ℂ) p =
      (((1 - (p : ℝ) ^ (-sigma))⁻¹ : ℝ) : ℂ) := by
  have hr0 : 0 ≤ (p : ℝ) ^ (-sigma) := Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hr1 : (p : ℝ) ^ (-sigma) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (neg_neg_of_pos hsigma)
  have hbase : (p : ℂ) ^ (-(sigma : ℂ)) = (((p : ℝ) ^ (-sigma) : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_neg, Complex.ofReal_natCast] using
      (Complex.ofReal_cpow (Nat.cast_nonneg p) (-sigma)).symm
  unfold gsA9LocalEulerFactor
  simp_rw [one_mul, hbase, ← Complex.ofReal_pow]
  rw [← Complex.ofReal_tsum, tsum_geometric_of_lt_one hr0 hr1]

theorem mrTsum_selectedPrimeWeight_eq_euler
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) {sigma : ℝ} (hsigma : 0 < sigma) :
    (∑' n : ℕ, mrSelectedPrimeWeight A sigma n) =
      ∏ p ∈ A, (1 - (p : ℝ) ^ (-sigma))⁻¹ := by
  have hm : IsMultiplicativeOnPositiveNat (fun _ : ℕ ↦ (1 : ℂ)) := by
    constructor
    · rfl
    · intro m n hm hn hcop
      simp
  have hEuler := LSeries_primeBandCoefficient_eq_finiteEulerProduct_of_pos_re
    hm (by simp) (fun p ↦ p ∈ A) (A.sup id)
    (fun p hp ↦ Finset.le_sup (f := id) hp) (s := (sigma : ℂ)) (by simpa using hsigma)
  have hset : (primesUpTo (A.sup id)).filter (fun p ↦ p ∈ A) = A := by
    ext p
    constructor
    · exact fun hp ↦ (Finset.mem_filter.mp hp).2
    · intro hp
      exact Finset.mem_filter.mpr
        ⟨mem_primesUpTo.mpr ⟨hA p hp, Finset.le_sup (f := id) hp⟩, hp⟩
  rw [hset] at hEuler
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum]
  calc
    _ = LSeries (primeBandCoefficient (fun _ ↦ (1 : ℂ)) (fun p ↦ p ∈ A)) (sigma : ℂ) :=
      tsum_congr (selectedPrimeWeight_cast A sigma)
    _ = ∏ p ∈ A, gsA9LocalEulerFactor (fun _ ↦ (1 : ℂ)) (sigma : ℂ) p := hEuler
    _ = _ := by
      rw [Complex.ofReal_prod]
      apply Finset.prod_congr rfl
      intro p hp
      exact localEulerFactor_one_real (hA p hp) hsigma

theorem mrSum_selectedPrimeWeight_le_euler
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) {sigma : ℝ} (hsigma : 0 < sigma)
    (S : Finset ℕ) :
    (∑ n ∈ S, mrSelectedPrimeWeight A sigma n) ≤
      ∏ p ∈ A, (1 - (p : ℝ) ^ (-sigma))⁻¹ := by
  rw [← mrTsum_selectedPrimeWeight_eq_euler A hA hsigma]
  exact (mrSummable_selectedPrimeWeight A hsigma).sum_le_tsum S
    (fun n _ ↦ mrSelectedPrimeWeight_nonneg A sigma n)

open Classical in
def mrSelectedPrimeTailWeight (A : Finset ℕ) (K : ℝ) (n : ℕ) : ℝ :=
  if K < (n : ℝ) then mrSelectedPrimeWeight A 1 n else 0

theorem mrSelectedPrimeTailWeight_le_rankin
    (A : Finset ℕ) {K sigma : ℝ} (hK : 0 < K) (hsigma : sigma ≤ 1) (n : ℕ) :
    mrSelectedPrimeTailWeight A K n ≤ K ^ (sigma - 1) * mrSelectedPrimeWeight A sigma n := by
  classical
  unfold mrSelectedPrimeTailWeight
  by_cases hKn : K < (n : ℝ)
  · rw [if_pos hKn]
    unfold mrSelectedPrimeWeight
    split_ifs with hn
    · have hnpos : (0 : ℝ) < n := hK.trans hKn
      have hpower := Real.rpow_le_rpow_of_nonpos hK hKn.le (sub_nonpos.mpr hsigma)
      calc
        (n : ℝ) ^ (-(1 : ℝ)) = (n : ℝ) ^ (sigma - 1) * (n : ℝ) ^ (-sigma) := by
          rw [← Real.rpow_add hnpos]
          congr 1
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hpower (Real.rpow_nonneg hnpos.le _)
    · simp
  · rw [if_neg hKn]
    exact mul_nonneg (Real.rpow_nonneg hK.le _) (mrSelectedPrimeWeight_nonneg A sigma n)

theorem mrSummable_selectedPrimeTailWeight
    (A : Finset ℕ) (K : ℝ) : Summable (mrSelectedPrimeTailWeight A K) := by
  classical
  apply (mrSummable_selectedPrimeWeight A (by norm_num : (0 : ℝ) < 1)).of_nonneg_of_le
  · intro n
    unfold mrSelectedPrimeTailWeight
    split_ifs
    · exact mrSelectedPrimeWeight_nonneg A 1 n
    · exact le_rfl
  · intro n
    unfold mrSelectedPrimeTailWeight
    split_ifs
    · exact le_rfl
    · exact mrSelectedPrimeWeight_nonneg A 1 n

theorem mrTsum_selectedPrimeTailWeight_le_rankin
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) {K sigma : ℝ}
    (hK : 0 < K) (hsigma : 0 < sigma) (hsigmaOne : sigma ≤ 1) :
    (∑' n : ℕ, mrSelectedPrimeTailWeight A K n) ≤
      K ^ (sigma - 1) * ∏ p ∈ A, (1 - (p : ℝ) ^ (-sigma))⁻¹ := by
  calc
    _ ≤ ∑' n : ℕ, K ^ (sigma - 1) * mrSelectedPrimeWeight A sigma n :=
      (mrSummable_selectedPrimeTailWeight A K).tsum_le_tsum
        (mrSelectedPrimeTailWeight_le_rankin A hK hsigmaOne)
        ((mrSummable_selectedPrimeWeight A hsigma).mul_left _)
    _ = K ^ (sigma - 1) * ∑' n : ℕ, mrSelectedPrimeWeight A sigma n := tsum_mul_left
    _ = _ := by rw [mrTsum_selectedPrimeWeight_eq_euler A hA hsigma]

theorem mrSum_selectedPrimeTailWeight_le_rankin
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) {K sigma : ℝ}
    (hK : 0 < K) (hsigma : 0 < sigma) (hsigmaOne : sigma ≤ 1) (S : Finset ℕ) :
    (∑ n ∈ S, mrSelectedPrimeTailWeight A K n) ≤
      K ^ (sigma - 1) * ∏ p ∈ A, (1 - (p : ℝ) ^ (-sigma))⁻¹ := by
  classical
  apply le_trans ((mrSummable_selectedPrimeTailWeight A K).sum_le_tsum S (fun n _ ↦ ?_))
    (mrTsum_selectedPrimeTailWeight_le_rankin A hA hK hsigma hsigmaOne)
  unfold mrSelectedPrimeTailWeight
  split_ifs
  · exact mrSelectedPrimeWeight_nonneg A 1 n
  · exact le_rfl

end

end Erdos67b
