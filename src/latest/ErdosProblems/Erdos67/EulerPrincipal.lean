import ErdosProblems.Erdos67.EulerResidue
import ErdosProblems.Erdos67.EulerSubpower

/-!
# The principal Dirichlet twist

This file evaluates the principal-character Euler product attached to a
completely multiplicative function.  The principal character deletes exactly
the Euler factors at the primes dividing its modulus.  We then specialize the
identity to moduli dividing a power of `q`, when the function is assumed to be
one at every prime dividing `q`.
-/

open scoped BigOperators Topology
open Complex Finset Filter

namespace Erdos67.EulerResidue

noncomputable section

/-- Euler product for a Dirichlet twist of a unit-norm completely
multiplicative function. -/
theorem twistedEulerProduct_hasProd {r : ℕ} {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h) (χ : DirichletCharacter ℂ r)
    {s : ℂ} (hs : 1 < s.re) :
    HasProd
      (fun p : Nat.Primes ↦
        (1 - h p * χ p * (p : ℂ) ^ (-s))⁻¹)
      (LSeries (twistCoefficient h χ) s) := by
  rw [← tsum_twistedWeightedSummandHom_eq_LSeries h χ hs]
  simpa only [twistedWeightedSummandHom_apply] using
    EulerProduct.eulerProduct_completely_multiplicative_hasProd
      (summable_norm_twistedWeightedSummandHom hh χ hs)

/-- Euler product for a Dirichlet twist, as a `tprod` identity. -/
theorem twistedEulerProduct_tprod {r : ℕ} {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h) (χ : DirichletCharacter ℂ r)
    {s : ℂ} (hs : 1 < s.re) :
    (∏' p : Nat.Primes,
        (1 - h p * χ p * (p : ℂ) ^ (-s))⁻¹) =
      LSeries (twistCoefficient h χ) s :=
  (twistedEulerProduct_hasProd hh χ hs).tprod_eq

/-- The principal character deletes exactly the Euler factors indexed by
the prime divisors of its modulus. -/
theorem principalTwistSeries_eq_mul_prod_primeFactors
    {r : ℕ} [NeZero r] {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h) {s : ℂ} (hs : 1 < s.re) :
    principalTwistSeries h r s =
      LSeries h s *
        ∏ p ∈ r.primeFactors, (1 - h p * (p : ℂ) ^ (-s)) := by
  unfold principalTwistSeries
  rw [prod_eq_tprod_mulIndicator,
    ← twistedEulerProduct_tprod hh (1 : DirichletCharacter ℂ r) hs,
    ← weightedEulerProduct_tprod hh hs]
  have (f : Nat.Primes → ℂ) :
      ∏' (p : Nat.Primes), f p =
        ∏' (p : ↑{p : ℕ | p.Prime}), f p := rfl
  rw [this,
    _root_.tprod_subtype _ fun p : ℕ ↦
      (1 - h p * (1 : DirichletCharacter ℂ r) p *
        (p : ℂ) ^ (-s))⁻¹,
    this,
    _root_.tprod_subtype _ fun p : ℕ ↦
      (1 - h p * (p : ℂ) ^ (-s))⁻¹,
    ← Multipliable.tprod_mul]
  rotate_left
  · exact multipliable_subtype_iff_mulIndicator.mp
      (weightedEulerProduct_hasProd hh hs).multipliable
  · exact multipliable_subtype_iff_mulIndicator.mp Multipliable.of_finite
  · congr 1 with p
    simp only [Set.mulIndicator_apply, Set.mem_ofPred_eq,
      Finset.mem_coe, Nat.mem_primeFactors, ne_eq, mul_ite, mul_one]
    by_cases hp : p.Prime
    swap
    · simp only [hp, false_and, if_false]
    simp only [hp, true_and, if_true]
    by_cases hpr : p ∣ r
    swap
    · simp only [hpr, false_and, ↓reduceIte]
      have hunit : IsUnit (p : ZMod r) :=
        (ZMod.isUnit_prime_iff_not_dvd hp).mpr hpr
      rw [MulChar.one_apply hunit, mul_one]
    · simp only [hpr, NeZero.ne r, not_false_eq_true, and_self,
        ↓reduceIte]
      have hnonunit : ¬IsUnit (p : ZMod r) := by
        rwa [ZMod.isUnit_prime_iff_not_dvd hp, not_not]
      rw [MulChar.map_nonunit _ hnonunit]
      simp only [mul_zero, zero_mul, sub_zero, inv_one]
      refine (inv_mul_cancel₀ ?_).symm
      rw [sub_ne_zero, ne_comm]
      apply_fun (‖·‖)
      simp only [norm_mul, norm_one]
      have ha : ‖h p‖ ≤ 1 := hh.norm_le_one p
      have hb : ‖(p : ℂ) ^ (-s)‖ ≤ 1 / 2 :=
        norm_prime_cpow_le_one_half ⟨p, hp⟩ hs
      exact ((mul_le_mul ha hb (norm_nonneg _) zero_le_one).trans_lt
        (by norm_num)).ne

/-- If `r` divides a power of `q` and `h` is one at all prime divisors of
`q`, then every deleted Euler factor is the ordinary factor `1 - p⁻ˢ`. -/
theorem principalTwistSeries_eq_LSeries_mul_prod_of_dvd_pow
    {q k r : ℕ} (_hq0 : q ≠ 0) {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ q → h p = 1)
    (hr : r ∣ q ^ k) (hr0 : r ≠ 0)
    {s : ℂ} (hs : 1 < s.re) :
    principalTwistSeries h r s =
      LSeries h s *
        ∏ p ∈ r.primeFactors, (1 - (p : ℂ) ^ (-s)) := by
  let : NeZero r := ⟨hr0⟩
  rw [principalTwistSeries_eq_mul_prod_primeFactors hh hs]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpr : p ∣ r := Nat.dvd_of_mem_primeFactors hp
  have hpqpow : p ∣ q ^ k := hpr.trans hr
  have hpq : p ∣ q := hpprime.dvd_of_dvd_pow hpqpow
  rw [hprime p hpprime hpq, one_mul]

/-- The preceding identity at Tao's exponent, with the untwisted series
written as `singularSeries`. -/
theorem principalTwistSeries_eq_singularSeries_mul_prod
    {q k r X : ℕ} (hq0 : q ≠ 0) {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ q → h p = 1)
    (hr : r ∣ q ^ k) (hr0 : r ≠ 0) (hX : 1 < X) :
    principalTwistSeries h r (taoExponent X) =
      singularSeries h X *
        ∏ p ∈ r.primeFactors,
          (1 - (p : ℂ) ^ (-(taoExponent X : ℂ))) := by
  exact principalTwistSeries_eq_LSeries_mul_prod_of_dvd_pow
    hq0 hh hprime hr hr0 (by simpa using one_lt_taoExponent hX)

/-! ## A hypothesis-free principal error term -/

/-- The finite Euler factor by which the principal twist differs from the
untwisted singular series. -/
def principalEulerFactor (r X : ℕ) : ℂ :=
  ∏ p ∈ r.primeFactors,
    (1 - (p : ℂ) ^ (-(taoExponent X : ℂ)))

/-- The exact error made by replacing the normalized principal twist by
the common normalized main term `S / r`.  Its finite product is independent
of `h`. -/
def principalEulerError (S : ℂ) (r X : ℕ) : ℝ :=
  ‖S‖ *
    ‖(r.totient : ℂ)⁻¹ * principalEulerFactor r X - (r : ℂ)⁻¹‖

/-- Unconditional normalized principal-character estimate at Tao's
exponent.  All analytic content is discharged by the exact Euler product;
the right side is a completely explicit finite-product error. -/
theorem norm_normalized_principalTwist_sub_div_le
    {q k r X : ℕ} (hq0 : q ≠ 0) {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ q → h p = 1)
    (hr : r ∣ q ^ k) (hr0 : r ≠ 0) (hX : 1 < X) :
    ‖(r.totient : ℂ)⁻¹ *
          principalTwistSeries h r (taoExponent X) -
        singularSeries h X / (r : ℂ)‖ ≤
      principalEulerError (singularSeries h X) r X := by
  rw [principalTwistSeries_eq_singularSeries_mul_prod
    hq0 hh hprime hr hr0 hX]
  unfold principalEulerError principalEulerFactor
  have hid :
      (r.totient : ℂ)⁻¹ *
          (singularSeries h X *
            ∏ p ∈ r.primeFactors,
              (1 - (p : ℂ) ^ (-(taoExponent X : ℂ)))) -
          singularSeries h X / (r : ℂ) =
        singularSeries h X *
          ((r.totient : ℂ)⁻¹ *
              ∏ p ∈ r.primeFactors,
                (1 - (p : ℂ) ^ (-(taoExponent X : ℂ))) -
            (r : ℂ)⁻¹) := by ring
  rw [hid, norm_mul]

/-- Tao's real exponent tends to `1`. -/
theorem tendsto_taoExponent :
    Filter.Tendsto taoExponent Filter.atTop (𝓝 1) := by
  unfold taoExponent
  simpa only [Function.comp_apply, add_zero] using
    (Filter.Tendsto.add
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ (1 : ℝ))
        Filter.atTop (𝓝 1))
      (tendsto_inv_atTop_zero.comp
        Erdos67.EulerSubpower.tendsto_log_nat_atTop))

/-- For a fixed modulus, its finite principal Euler factor tends to the
factor at `s = 1`. -/
theorem tendsto_principalEulerFactor (r : ℕ) :
    Filter.Tendsto (principalEulerFactor r) Filter.atTop
      (𝓝 (∏ p ∈ r.primeFactors, (1 - (p : ℂ)⁻¹))) := by
  unfold principalEulerFactor
  apply tendsto_finset_prod
  intro p hp
  have hp0 : (p : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hexp : Filter.Tendsto
      (fun X : ℕ ↦ -(taoExponent X : ℂ)) Filter.atTop
      (𝓝 (-(1 : ℂ))) := tendsto_taoExponent.ofReal.neg
  have hpow : Filter.Tendsto
      (fun X : ℕ ↦ (p : ℂ) ^ (-(taoExponent X : ℂ))) Filter.atTop
      (𝓝 ((p : ℂ) ^ (-(1 : ℂ)))) :=
    (continuousAt_const_cpow hp0).tendsto.comp hexp
  convert tendsto_const_nhds.sub hpow using 1
  simp [Complex.cpow_neg]

/-- Euler's totient product formula, cast to `ℂ` and divided by the
modulus. -/
theorem prod_one_sub_prime_inv_eq_totient_div {r : ℕ} (hr0 : r ≠ 0) :
    (∏ p ∈ r.primeFactors, (1 - (p : ℂ)⁻¹)) =
      (r.totient : ℂ) / (r : ℂ) := by
  have htot := congrArg (algebraMap ℚ ℂ)
    (Nat.totient_eq_mul_prod_factors r)
  have htot' : (r.totient : ℂ) = (r : ℂ) *
      ∏ p ∈ r.primeFactors, (1 - (p : ℂ)⁻¹) := by
    simpa using htot
  apply (eq_div_iff (Nat.cast_ne_zero.mpr hr0)).2
  simpa only [mul_comm] using htot'.symm

/-- The scalar error in the normalized principal Euler factor tends to
zero for every fixed nonzero modulus. -/
theorem tendsto_normalized_principalEulerFactor_sub_inv
    {r : ℕ} (hr0 : r ≠ 0) :
    Filter.Tendsto
      (fun X : ℕ ↦
        (r.totient : ℂ)⁻¹ * principalEulerFactor r X - (r : ℂ)⁻¹)
      Filter.atTop (𝓝 0) := by
  have hprod := tendsto_principalEulerFactor r
  have hmul :=
    (tendsto_const_nhds : Filter.Tendsto
      (fun _ : ℕ ↦ (r.totient : ℂ)⁻¹) Filter.atTop
        (𝓝 (r.totient : ℂ)⁻¹)).mul hprod
  have hconst : Filter.Tendsto (fun _ : ℕ ↦ (r : ℂ)⁻¹)
      Filter.atTop (𝓝 (r : ℂ)⁻¹) := tendsto_const_nhds
  have hlim := hmul.sub hconst
  convert hlim using 1
  rw [prod_one_sub_prime_inv_eq_totient_div hr0]
  have hphi0 : (r.totient : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hr0)).ne'
  field_simp
  simp

/-- Consequently, the norm of the scalar principal-factor error tends to
zero. -/
theorem tendsto_norm_normalized_principalEulerFactor_sub_inv
    {r : ℕ} (hr0 : r ≠ 0) :
    Filter.Tendsto
      (fun X : ℕ ↦
        ‖(r.totient : ℂ)⁻¹ * principalEulerFactor r X - (r : ℂ)⁻¹‖)
      Filter.atTop (𝓝 0) := by
  simpa using (tendsto_normalized_principalEulerFactor_sub_inv hr0).norm

/-- The singular series is majorized by the corresponding real zeta
Dirichlet series. -/
theorem norm_singularSeries_le_realZetaSum {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h) {X : ℕ} (hX : 1 < X) :
    ‖singularSeries h X‖ ≤
      ∑' n : ℕ, 1 / (n : ℝ) ^ taoExponent X := by
  have hs : (1 : ℝ) < ((taoExponent X : ℝ) : ℂ).re := by
    simpa using one_lt_taoExponent hX
  refine (norm_LSeries_le_zetaMajorant hh hs).trans_eq ?_
  apply tsum_congr
  intro n
  simp only [riemannZetaSummandHom, MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk]
  rw [← Complex.ofReal_natCast]
  rw [Complex.norm_cpow_eq_rpow_re_of_nonneg (Nat.cast_nonneg n)
    (by simpa using ne_zero_of_one_lt_re hs)]
  simp only [neg_re, ofReal_re, Real.rpow_neg (Nat.cast_nonneg n),
    one_div]

/-- The real zeta residue theorem along Tao's exponents. -/
theorem tendsto_taoExponent_mul_realZetaSum :
    Filter.Tendsto
      (fun X : ℕ ↦
        (taoExponent X - 1) *
          ∑' n : ℕ, 1 / (n : ℝ) ^ taoExponent X)
      Filter.atTop (𝓝 1) := by
  apply tendsto_sub_mul_tsum_nat_rpow.comp
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨tendsto_taoExponent, ?_⟩
  filter_upwards [eventually_ge_atTop 2] with X hX
  exact one_lt_taoExponent (by omega)

/-- Uniformly for every unit-norm coefficient, its singular series is
`O(log X)`.  This is the upper half of the Mertens comparison needed in the
principal-character error. -/
theorem norm_singularSeries_isBigO_log {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h) :
    (fun X : ℕ ↦ ‖singularSeries h X‖) =O[Filter.atTop]
      (fun X : ℕ ↦ Real.log (X : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound 2 ?_
  have hzeta : ∀ᶠ X : ℕ in Filter.atTop,
      (taoExponent X - 1) *
          (∑' n : ℕ, 1 / (n : ℝ) ^ taoExponent X) < 2 :=
    tendsto_taoExponent_mul_realZetaSum.eventually
      (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2))
  filter_upwards [hzeta, eventually_ge_atTop 2] with X hzetaX hX
  have hX1 : 1 < X := by omega
  have hlog : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast hX1)
  have hzetaX' :
      (Real.log (X : ℝ))⁻¹ *
          (∑' n : ℕ, 1 / (n : ℝ) ^ taoExponent X) ≤ 2 := by
    have htao : taoExponent X - 1 = (Real.log (X : ℝ))⁻¹ := by
      unfold taoExponent
      ring
    rw [htao] at hzetaX
    exact hzetaX.le
  have hsum :
      (∑' n : ℕ, 1 / (n : ℝ) ^ taoExponent X) ≤
        2 * Real.log (X : ℝ) := by
    rw [inv_mul_eq_div] at hzetaX'
    exact (div_le_iff₀ hlog).mp hzetaX'
  have hmain := (norm_singularSeries_le_realZetaSum hh hX1).trans hsum
  simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    abs_of_pos hlog] using hmain

/-- For each fixed nonzero modulus, the completely explicit principal
error is `o(log X)`. -/
theorem principalEulerError_isLittleO_log {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h) {r : ℕ} (hr0 : r ≠ 0) :
    (fun X : ℕ ↦ principalEulerError (singularSeries h X) r X)
      =o[Filter.atTop] (fun X : ℕ ↦ Real.log (X : ℝ)) := by
  have hcoefficient :
      (fun X : ℕ ↦
        ‖(r.totient : ℂ)⁻¹ * principalEulerFactor r X - (r : ℂ)⁻¹‖)
        =o[Filter.atTop] (fun _ : ℕ ↦ (1 : ℝ)) :=
    (Asymptotics.isLittleO_one_iff ℝ).mpr
      (tendsto_norm_normalized_principalEulerFactor_sub_inv hr0)
  have hmul := (norm_singularSeries_isBigO_log hh).mul_isLittleO hcoefficient
  simpa only [principalEulerError, mul_one] using hmul

/-- A single principal-character error which works simultaneously for all
divisors of `q^k`. -/
def uniformPrincipalEulerError (h : ℕ →*₀ ℂ) (q k X : ℕ) : ℝ :=
  ∑ r ∈ (q ^ k).divisors,
    principalEulerError (singularSeries h X) r X

theorem principalEulerError_le_uniform {h : ℕ →*₀ ℂ}
    {q k r X : ℕ} (hq0 : q ≠ 0) (hr : r ∣ q ^ k) :
    principalEulerError (singularSeries h X) r X ≤
      uniformPrincipalEulerError h q k X := by
  unfold uniformPrincipalEulerError
  have hrmem : r ∈ (q ^ k).divisors :=
    Nat.mem_divisors.mpr ⟨hr, pow_ne_zero k hq0⟩
  refine Finset.single_le_sum
    (s := (q ^ k).divisors)
    (f := fun t ↦ principalEulerError (singularSeries h X) t X) ?_ hrmem
  intro t ht
  exact mul_nonneg (norm_nonneg _) (norm_nonneg _)

/-- The uniform principal error over the finite divisor set is still
`o(log X)`. -/
theorem uniformPrincipalEulerError_isLittleO_log {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h) {q k : ℕ} (hq0 : q ≠ 0) :
    (uniformPrincipalEulerError h q k)
      =o[Filter.atTop] (fun X : ℕ ↦ Real.log (X : ℝ)) := by
  unfold uniformPrincipalEulerError
  have heach : ∀ r ∈ (q ^ k).divisors,
      (fun X : ℕ ↦ principalEulerError (singularSeries h X) r X)
        =o[Filter.atTop] (fun X : ℕ ↦ Real.log (X : ℝ)) := by
    intro r hr
    have hr0 : r ≠ 0 := by
      intro hzero
      subst r
      have hpow0 : q ^ k ≠ 0 := pow_ne_zero k hq0
      exact hpow0 (zero_dvd_iff.mp (Nat.dvd_of_mem_divisors hr))
    exact principalEulerError_isLittleO_log hh hr0
  have hsum := Asymptotics.IsLittleO.sum heach
  refine hsum.congr_left ?_
  intro X
  exact Finset.sum_apply X (q ^ k).divisors
    (fun r X ↦ principalEulerError (singularSeries h X) r X)

/-- Pointwise normalized principal-twist estimate with one error term uniform
over every divisor of `q^k`. -/
theorem norm_normalized_principalTwist_sub_div_le_uniform
    {q k r X : ℕ} (hq0 : q ≠ 0) {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ q → h p = 1)
    (hr : r ∣ q ^ k) (hr0 : r ≠ 0) (hX : 1 < X) :
    ‖(r.totient : ℂ)⁻¹ *
          principalTwistSeries h r (taoExponent X) -
        singularSeries h X / (r : ℂ)‖ ≤
      uniformPrincipalEulerError h q k X :=
  (norm_normalized_principalTwist_sub_div_le
    hq0 hh hprime hr hr0 hX).trans
      (principalEulerError_le_uniform hq0 hr)

end

end Erdos67.EulerResidue
