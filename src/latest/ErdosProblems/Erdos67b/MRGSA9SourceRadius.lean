import ErdosProblems.Erdos67b.MRGSA9A13ShiftedThreeBlock

/-!
# Automatic source-line radius and displacement hypotheses for A.13

After primes below `23` have been deleted, the source A.10 left line
`sigmaLow ≥ 1/2` puts every remaining Euler variable in the closed ball of
radius `1/3`.  This file also restricts the already-proved complete radial
displacement bound to arbitrary finite subblocks of the primes through `y`.
-/

open scoped BigOperators

namespace Erdos67b.MRHalaszBands

noncomputable section

/-- The fixed absolute radial-displacement budget used in source A.13. -/
def gsA9SourceShiftConstant : ℝ :=
  3 * Real.exp 2 *
    (1 + primeLogMertensConstant / Real.log 2)

/-- On `Re s ≥ 1/2`, every Euler variable at a prime at least `23` has
norm at most `1/3`. -/
theorem norm_prime_cpow_le_one_third_of_twenty_three_le
    {p : ℕ} (hp : p.Prime) (hpLarge : 23 ≤ p) {sigma t : ℝ}
    (hsigma : 1 / 2 ≤ sigma) :
    ‖(p : ℂ) ^ (-((sigma : ℂ) + Complex.I * (t : ℂ)))‖ ≤
      (1 / 3 : ℝ) := by
  rw [Erdos67b.HalaszCpowDeficit.norm_nat_cpow_neg_sigma_add_I_mul hp.pos]
  have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hmono : (p : ℝ) ^ (-sigma) ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
    exact Real.rpow_le_rpow_of_exponent_le hpOne (by linarith)
  have hp0 : (0 : ℝ) ≤ p := by positivity
  let x : ℝ := (p : ℝ) ^ (-(1 / 2 : ℝ))
  have hx0 : 0 ≤ x := Real.rpow_nonneg hp0 _
  have hx2 : x ^ 2 = (p : ℝ)⁻¹ := by
    dsimp only [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0]
    norm_num [Real.rpow_neg_one]
  have hpR : (23 : ℝ) ≤ p := by exact_mod_cast hpLarge
  have hinv : (p : ℝ)⁻¹ ≤ (1 / 9 : ℝ) := by
    simpa only [one_div] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 9) (by linarith)
  have hx : x ≤ (1 / 3 : ℝ) := by
    nlinarith [hx2, hinv]
  exact hmono.trans hx

/-- Radial norms decrease when the real part of the exponent increases. -/
theorem norm_prime_cpow_antitone_real
    {p : ℕ} (hp : p.Prime) {sigmaLow sigmaHigh t : ℝ}
    (hle : sigmaLow ≤ sigmaHigh) :
    ‖(p : ℂ) ^ (-((sigmaHigh : ℂ) + Complex.I * (t : ℂ)))‖ ≤
      ‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖ := by
  rw [Erdos67b.HalaszCpowDeficit.norm_nat_cpow_neg_sigma_add_I_mul hp.pos,
    Erdos67b.HalaszCpowDeficit.norm_nat_cpow_neg_sigma_add_I_mul hp.pos]
  exact Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast hp.one_le) (by linarith)

/-- Every subblock of the primes through `y` inherits the complete source
radial-displacement budget. -/
theorem sum_prime_radial_norm_sub_subset_sourceGap_le_constant
    {y : ℕ} (hy : 2 ≤ y) (S : Finset ℕ)
    (hS : S ⊆ primesUpTo y)
    {sigmaLow sigmaHigh t : ℝ}
    (hle : sigmaLow ≤ sigmaHigh)
    (hsigma : 1 - 2 / Real.log (y : ℝ) ≤ sigmaLow)
    (hgap : sigmaHigh - sigmaLow ≤ 3 / Real.log (y : ℝ)) :
    (∑ p ∈ S,
      (‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖ -
        ‖(p : ℂ) ^ (-((sigmaHigh : ℂ) + Complex.I * (t : ℂ)))‖)) ≤
      gsA9SourceShiftConstant := by
  have hsub :
      (∑ p ∈ S,
        (‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖ -
          ‖(p : ℂ) ^ (-((sigmaHigh : ℂ) + Complex.I * (t : ℂ)))‖)) ≤
        ∑ p ∈ primesUpTo y,
        (‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖ -
          ‖(p : ℂ) ^ (-((sigmaHigh : ℂ) + Complex.I * (t : ℂ)))‖) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hS
    intro p hp _
    exact sub_nonneg.mpr
      (norm_prime_cpow_antitone_real (mem_primesUpTo.mp hp).1 hle)
  exact hsub.trans (by
    simpa only [gsA9SourceShiftConstant] using
      sum_prime_radial_norm_sub_sourceGap_le_constant hy hle hsigma hgap)

/-- The quadratic Euler mass on the source left line is still absolutely
bounded.  The factor `exp 4` is exactly the cost of moving at most
`2 / log y` to the left of `Re s = 1`. -/
theorem two_mul_sum_norm_prime_cpow_sq_sourceLow_le
    {y : ℕ} (S : Finset ℕ) (hS : S ⊆ primesUpTo y)
    {sigmaLow t : ℝ}
    (hsigma : 1 - 2 / Real.log (y : ℝ) ≤ sigmaLow) :
    2 * (∑ p ∈ S,
      ‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖ ^ 2) ≤
      Real.exp 4 * Erdos67b.EulerQuantitative.primeQuadraticConstant := by
  let e : {p // p ∈ S} → Nat.Primes := fun p ↦
    ⟨p, (mem_primesUpTo.mp (hS p.property)).1⟩
  have heinj : Function.Injective e := by
    intro p q hpq
    apply Subtype.ext
    exact congrArg (fun z : Nat.Primes ↦ (z : ℕ)) hpq
  let T : Finset Nat.Primes := Finset.univ.map ⟨e, heinj⟩
  let G : Nat.Primes → ℝ := fun p ↦ (p.1 : ℝ) ^ (-2 : ℝ)
  have hGs : Summable G :=
    (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).subtype
      Nat.Prime
  have hpoint (p : ℕ) (hp : p ∈ S) :
      ‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖ ^ 2 ≤
        Real.exp 4 * (p : ℝ) ^ (-2 : ℝ) := by
    have hpPrime := (mem_primesUpTo.mp (hS hp)).1
    have hnorm := norm_prime_cpow_sourceLow_le_exp_two_div
      hpPrime (mem_primesUpTo.mp (hS hp)).2 hsigma (t := t)
    have hnorm0 : 0 ≤
        ‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖ := norm_nonneg _
    have hdiv0 : 0 ≤ Real.exp 2 / (p : ℝ) := by positivity
    have hsq := (sq_le_sq₀ hnorm0 hdiv0).2 hnorm
    calc
      ‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖ ^ 2 ≤
          (Real.exp 2 / (p : ℝ)) ^ 2 := hsq
      _ = Real.exp 4 * (p : ℝ) ^ (-2 : ℝ) := by
        rw [div_pow, ← Real.exp_nat_mul]
        have hp0 : (0 : ℝ) ≤ p := by positivity
        rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
          Real.rpow_neg hp0]
        norm_num [div_eq_mul_inv]
  have hsumEq :
      (∑ p ∈ S,
        Real.exp 4 * (p : ℝ) ^ (-2 : ℝ)) =
        ∑ p ∈ T, Real.exp 4 * G p := by
    rw [Finset.sum_subtype S (fun _ ↦ Iff.rfl), Finset.sum_map]
    rfl
  have hfinite :
      (∑ p ∈ S,
        ‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖ ^ 2) ≤
        Real.exp 4 * ∑' p : Nat.Primes, G p := by
    calc
      _ ≤ ∑ p ∈ S, Real.exp 4 * (p : ℝ) ^ (-2 : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        exact hpoint p hp
      _ = ∑ p ∈ T, Real.exp 4 * G p := hsumEq
      _ ≤ ∑' p : Nat.Primes, Real.exp 4 * G p := by
        exact (hGs.mul_left (Real.exp 4)).sum_le_tsum T
          (fun p _ ↦ mul_nonneg (Real.exp_pos _).le
            (Real.rpow_nonneg (by positivity) _))
      _ = Real.exp 4 * ∑' p : Nat.Primes, G p := by
        rw [hGs.tsum_mul_left]
  have hconst : 2 * ∑' p : Nat.Primes, G p =
      Erdos67b.EulerQuantitative.primeQuadraticConstant := by
    unfold Erdos67b.EulerQuantitative.primeQuadraticConstant
    rw [hGs.tsum_mul_left]
  calc
    2 * (∑ p ∈ S,
      ‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖ ^ 2) ≤
        2 * (Real.exp 4 * ∑' p : Nat.Primes, G p) := by gcongr
    _ = Real.exp 4 * Erdos67b.EulerQuantitative.primeQuadraticConstant := by
      rw [← hconst]
      ring

/-- The finite three-block A.13 theorem with all analytic radius and
horizontal-displacement hypotheses discharged by the source window. -/
theorem norm_threeEulerBlockAlternating_sq_le_source_shifted_full_products
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y : ℕ} (hy : 2 ≤ y)
    (S₀ S₂ S₃ : Finset ℕ)
    (hS₀ : S₀ ⊆ primesUpTo y) (hS₂ : S₂ ⊆ primesUpTo y)
    (hS₃ : S₃ ⊆ primesUpTo y)
    (hlarge₀ : ∀ p ∈ S₀, 23 ≤ p)
    (hlarge₂ : ∀ p ∈ S₂, 23 ≤ p)
    (hlarge₃ : ∀ p ∈ S₃, 23 ≤ p)
    {sigmaLow sigmaHigh t : ℝ}
    (hhalf : 1 / 2 ≤ sigmaLow)
    (hle : sigmaLow ≤ sigmaHigh)
    (hsigma : 1 - 2 / Real.log (y : ℝ) ≤ sigmaLow)
    (hgap : sigmaHigh - sigmaLow ≤ 3 / Real.log (y : ℝ)) :
    let sLow : ℂ := (sigmaLow : ℂ) + Complex.I * (t : ℂ)
    let sHigh : ℂ := (sigmaHigh : ℂ) + Complex.I * (t : ℂ)
    let one : ℕ → ℂ := fun _ ↦ 1
    let P₀ := ∏ p ∈ S₀, gsA9LocalEulerFactor f sLow p
    let P₂ := ∏ p ∈ S₂, gsA9LocalEulerFactor f sLow p
    let P₃ := ∏ p ∈ S₃, gsA9LocalEulerFactor f sLow p
    let Q₀ := ∏ p ∈ S₀, gsA9LocalEulerFactor f sHigh p
    let Q₂ := ∏ p ∈ S₂, gsA9LocalEulerFactor f sHigh p
    let Q₃ := ∏ p ∈ S₃, gsA9LocalEulerFactor f sHigh p
    let Q₀p := ∏ p ∈ S₀, gsA9LocalEulerFactor one (sigmaHigh : ℂ) p
    let Q₂p := ∏ p ∈ S₂, gsA9LocalEulerFactor one (sigmaHigh : ℂ) p
    let Q₃p := ∏ p ∈ S₃, gsA9LocalEulerFactor one (sigmaHigh : ℂ) p
    let V₀ := ∑ p ∈ S₀, ‖(p : ℂ) ^ (-sLow)‖ ^ 2
    let V₂ := ∑ p ∈ S₂, ‖(p : ℂ) ^ (-sLow)‖ ^ 2
    let V₃ := ∑ p ∈ S₃, ‖(p : ℂ) ^ (-sLow)‖ ^ 2
    ‖P₀ * (P₂ - 1) * (P₃ - 1)‖ ^ 2 ≤
      Real.exp (7 * V₀ + 24 * (V₂ + V₃) +
        36 * gsA9SourceShiftConstant) *
        ‖Q₀ * Q₂ * Q₃‖ * ‖Q₀p * Q₂p * Q₃p‖ := by
  apply norm_threeEulerBlockAlternating_sq_le_shifted_full_products
    hmul hbound S₀ S₂ S₃
  · intro p hp
    exact (mem_primesUpTo.mp (hS₀ hp)).1
  · intro p hp
    exact (mem_primesUpTo.mp (hS₂ hp)).1
  · intro p hp
    exact (mem_primesUpTo.mp (hS₃ hp)).1
  · exact hle
  · intro p hp
    exact norm_prime_cpow_le_one_third_of_twenty_three_le
      (mem_primesUpTo.mp (hS₀ hp)).1 (hlarge₀ p hp) hhalf
  · intro p hp
    exact norm_prime_cpow_le_one_third_of_twenty_three_le
      (mem_primesUpTo.mp (hS₂ hp)).1 (hlarge₂ p hp) hhalf
  · intro p hp
    exact norm_prime_cpow_le_one_third_of_twenty_three_le
      (mem_primesUpTo.mp (hS₃ hp)).1 (hlarge₃ p hp) hhalf
  · exact sum_prime_radial_norm_sub_subset_sourceGap_le_constant
      hy S₀ hS₀ hle hsigma hgap
  · exact sum_prime_radial_norm_sub_subset_sourceGap_le_constant
      hy S₂ hS₂ hle hsigma hgap
  · exact sum_prime_radial_norm_sub_subset_sourceGap_le_constant
      hy S₃ hS₃ hle hsigma hgap

end

end Erdos67b.MRHalaszBands
