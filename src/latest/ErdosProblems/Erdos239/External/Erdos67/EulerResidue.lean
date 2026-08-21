import ErdosProblems.Erdos239.External.Erdos67.CompletelyMultiplicative
import ErdosProblems.Erdos239.External.Erdos67.PrimeEstimates
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# Euler products and residue classes for Erdős 67

This file isolates the exact (as opposed to asymptotic) analytic identities
used in Section 4 of Tao's proof.  The coefficient `h` is represented by a
zero-preserving completely multiplicative map `ℕ →*₀ ℂ`; on positive
integers it has unit norm.  For `re s > 1` we prove absolute convergence,
the Euler product, Dirichlet-character expansion of a unit residue class, and
a uniform error lemma which reduces residue equidistribution to the
principal and nonprincipal twisted-series estimates.

The last reduction is intentionally quantitative and contains no hidden
analytic hypothesis.  In the eventual Erdős 67 assembly, its two hypotheses
are discharged by the pretentious prime-sum estimates: the principal twist
is compared with the singular series and the finitely many nonprincipal
twists are bounded uniformly.
-/

open scoped BigOperators
open Complex Finset

namespace Erdos67.EulerResidue

noncomputable section

/-- A zero-preserving completely multiplicative complex function whose
values on positive integers lie on the unit circle. -/
def HasUnitNorm (h : ℕ →*₀ ℂ) : Prop :=
  ∀ ⦃n : ℕ⦄, n ≠ 0 → ‖h n‖ = 1

lemma HasUnitNorm.norm_le_one {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h) (n : ℕ) :
    ‖h n‖ ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [hh hn]

lemma HasUnitNorm.ne_zero {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h)
    {n : ℕ} (hn : n ≠ 0) : h n ≠ 0 := by
  intro hz
  have := hh hn
  simp [hz] at this

/-- The completely multiplicative summand `h(n)n⁻ˢ`, including its value
zero at `n = 0`. -/
def weightedSummandHom (h : ℕ →*₀ ℂ) {s : ℂ} (hs : s ≠ 0) : ℕ →*₀ ℂ :=
  h * riemannZetaSummandHom hs

@[simp] lemma weightedSummandHom_apply (h : ℕ →*₀ ℂ) {s : ℂ}
    (hs : s ≠ 0) (n : ℕ) :
    weightedSummandHom h hs n = h n * (n : ℂ) ^ (-s) := by
  rfl

/-- Absolute convergence of the weighted completely multiplicative
summand in the half-plane `re s > 1`. -/
theorem summable_norm_weightedSummandHom {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ ↦ ‖weightedSummandHom h (ne_zero_of_one_lt_re hs) n‖) := by
  refine (summable_riemannZetaSummand hs).congr ?_
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [weightedSummandHom]
  · change ‖(n : ℂ) ^ (-s)‖ = ‖h n * (n : ℂ) ^ (-s)‖
    rw [norm_mul, hh hn, one_mul]

/-- The weighted sum is the ordinary `LSeries` with coefficient `h`. -/
theorem tsum_weightedSummandHom_eq_LSeries {h : ℕ →*₀ ℂ}
    {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, weightedSummandHom h (ne_zero_of_one_lt_re hs) n) =
      LSeries h s := by
  apply tsum_congr
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [weightedSummandHom]
  · simp [weightedSummandHom_apply, LSeries.term_of_ne_zero hn,
      div_eq_mul_inv, Complex.cpow_neg]

/-- Absolute convergence of the weighted Dirichlet series. -/
theorem weightedLSeriesSummable {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h)
    {s : ℂ} (hs : 1 < s.re) : LSeriesSummable h s := by
  exact LSeriesSummable_of_bounded_of_one_lt_re
    (fun n hn ↦ (hh hn).le) hs

/-- Termwise equality with the zeta majorant.  Thus the comparison with zeta
is sharp at the level of absolute values, not merely an inequality. -/
theorem norm_weightedSummandHom_eq_zetaSummand {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h) {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    ‖weightedSummandHom h (ne_zero_of_one_lt_re hs) n‖ =
      ‖riemannZetaSummandHom (ne_zero_of_one_lt_re hs) n‖ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [weightedSummandHom]
  · change ‖h n * (n : ℂ) ^ (-s)‖ = ‖(n : ℂ) ^ (-s)‖
    rw [norm_mul, hh hn, one_mul]

/-- The norm of the weighted series is bounded by the absolutely convergent
zeta majorant. -/
theorem norm_LSeries_le_zetaMajorant {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h) {s : ℂ} (hs : 1 < s.re) :
    ‖LSeries h s‖ ≤
      ∑' n : ℕ, ‖riemannZetaSummandHom (ne_zero_of_one_lt_re hs) n‖ := by
  rw [← tsum_weightedSummandHom_eq_LSeries hs]
  refine norm_tsum_le_tsum_norm (summable_norm_weightedSummandHom hh hs) |>.trans_eq ?_
  apply tsum_congr
  exact norm_weightedSummandHom_eq_zetaSummand hh hs

/-- Euler product for the singular series `Σ h(n)n⁻ˢ`. -/
theorem weightedEulerProduct_hasProd {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h) {s : ℂ} (hs : 1 < s.re) :
    HasProd
      (fun p : Nat.Primes ↦
        (1 - h p * (p : ℂ) ^ (-s))⁻¹)
      (LSeries h s) := by
  rw [← tsum_weightedSummandHom_eq_LSeries hs]
  simpa only [weightedSummandHom_apply] using
    EulerProduct.eulerProduct_completely_multiplicative_hasProd
      (summable_norm_weightedSummandHom hh hs)

/-- Euler product as a `tprod` equality. -/
theorem weightedEulerProduct_tprod {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h) {s : ℂ} (hs : 1 < s.re) :
    (∏' p : Nat.Primes, (1 - h p * (p : ℂ) ^ (-s))⁻¹) =
      LSeries h s :=
  (weightedEulerProduct_hasProd hh hs).tprod_eq

/-! ## The special exponent `1 + 1 / log X` -/

/-- The real exponent used in Tao's weighted Section 4 argument. -/
def taoExponent (X : ℕ) : ℝ :=
  1 + (Real.log (X : ℝ))⁻¹

theorem one_lt_taoExponent {X : ℕ} (hX : 1 < X) :
    1 < taoExponent X := by
  unfold taoExponent
  have hlog : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast hX)
  have hinv : 0 < (Real.log (X : ℝ))⁻¹ := inv_pos.mpr hlog
  linarith

theorem taoExponent_ne_zero {X : ℕ} (hX : 1 < X) :
    (taoExponent X : ℂ) ≠ 0 :=
  ne_zero_of_one_lt_re (by simpa using one_lt_taoExponent hX)

/-- The singular series at Tao's exponent. -/
def singularSeries (h : ℕ →*₀ ℂ) (X : ℕ) : ℂ :=
  LSeries h (taoExponent X)

theorem singularSeries_eulerProduct {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h) {X : ℕ} (hX : 1 < X) :
    (∏' p : Nat.Primes,
        (1 - h p * (p : ℂ) ^ (-(taoExponent X : ℂ)))⁻¹) =
      singularSeries h X := by
  exact weightedEulerProduct_tprod hh (by simpa using one_lt_taoExponent hX)

/-! ## Finite pretentious distance -/

/-- The prime sum measuring the squared pretentious distance from the
constant function `1`. -/
def pretentiousMass (h : ℕ →*₀ ℂ) (X : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE X, (1 - (h p).re) / (p : ℝ)

/-- Uniform finiteness of the pretentious distance from `1`. -/
def HasFinitePretentiousDistance (h : ℕ →*₀ ℂ) : Prop :=
  ∃ D : ℝ, 0 ≤ D ∧ ∀ X : ℕ, pretentiousMass h X ≤ D

lemma pretentiousTerm_nonneg {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h)
    {p : ℕ} (hp : p.Prime) :
    0 ≤ (1 - (h p).re) / (p : ℝ) := by
  have hre : (h p).re ≤ 1 := by
    calc
      (h p).re ≤ ‖h p‖ := Complex.re_le_norm _
      _ = 1 := hh hp.ne_zero
  exact div_nonneg (sub_nonneg.mpr hre) (Nat.cast_nonneg p)

theorem pretentiousMass_nonneg {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h)
    (X : ℕ) : 0 ≤ pretentiousMass h X := by
  unfold pretentiousMass
  apply Finset.sum_nonneg
  intro p hp
  exact pretentiousTerm_nonneg hh (Nat.mem_primesLE.mp hp).2

/-- On the unit circle, the pretentious summand is exactly half the square
of the Euclidean distance to `1`. -/
theorem norm_sub_one_sq {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h)
    {n : ℕ} (hn : n ≠ 0) :
    ‖h n - 1‖ ^ 2 = 2 * (1 - (h n).re) := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
  rw [Complex.normSq_eq_norm_sq, hh hn]
  norm_num
  ring

/-- A convenient unweighted finite consequence of finite pretentious
distance.  It is the exact input to Cauchy--Schwarz in the Euler-log
comparison. -/
theorem sum_norm_sub_one_sq_div {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h)
    (X : ℕ) :
    (∑ p ∈ Nat.primesLE X, ‖h p - 1‖ ^ 2 / (p : ℝ)) =
      2 * pretentiousMass h X := by
  unfold pretentiousMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [norm_sub_one_sq hh (Nat.mem_primesLE.mp hp).2.ne_zero]
  ring

/-- Cauchy--Schwarz converts the squared pretentious distance into the
linear prime sum that occurs in the difference of two Euler logarithms. -/
theorem sum_norm_sub_one_div_le_sqrt {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h) (X : ℕ) :
    (∑ p ∈ Nat.primesLE X, ‖h p - 1‖ / (p : ℝ)) ≤
      Real.sqrt
        ((2 * pretentiousMass h X) *
          Erdos67.PrimeEstimates.primeReciprocals X) := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (R := ℝ) (Nat.primesLE X)
    (r := fun p ↦ ‖h p - 1‖ / (p : ℝ))
    (f := fun p ↦ ‖h p - 1‖ ^ 2 / (p : ℝ))
    (g := fun p ↦ 1 / (p : ℝ))
    (fun p hp ↦ div_nonneg (sq_nonneg _) (Nat.cast_nonneg p))
    (fun p hp ↦ div_nonneg zero_le_one (Nat.cast_nonneg p))
    (fun p hp ↦ by
      have hp0 : (p : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.mem_primesLE.mp hp).2.ne_zero
      field_simp
      exact le_rfl)
  rw [sum_norm_sub_one_sq_div hh] at hcs
  apply Real.le_sqrt_of_sq_le
  simpa [Erdos67.PrimeEstimates.primeReciprocals,
    Erdos784.Analytic.primeReciprocals, one_div] using hcs

theorem sum_norm_sub_one_div_le_of_finiteDistance
    {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h)
    {D : ℝ} (hD : ∀ X : ℕ, pretentiousMass h X ≤ D) (X : ℕ) :
    (∑ p ∈ Nat.primesLE X, ‖h p - 1‖ / (p : ℝ)) ≤
      Real.sqrt
        ((2 * D) * Erdos67.PrimeEstimates.primeReciprocals X) := by
  refine (sum_norm_sub_one_div_le_sqrt hh X).trans ?_
  apply Real.sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hD X) (by norm_num))
    (Erdos67.PrimeEstimates.primeReciprocals_nonneg X)

/-! ## Quantitative Euler-log comparison -/

/-- A nonprincipal Dirichlet `L`-function is bounded on the fixed compact
real interval containing all exponents `1 + 1 / log X`, `X ≥ 2`. -/
theorem exists_nonprincipal_LFunction_bound {r : ℕ} [NeZero r]
    (χ : DirichletCharacter ℂ r) (hχ : χ ≠ 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ,
      t ∈ Set.Icc (1 : ℝ) (1 + (Real.log 2)⁻¹) →
        ‖DirichletCharacter.LFunction χ (t : ℂ)‖ ≤ B := by
  have hc : Continuous (fun t : ℝ ↦
      ‖DirichletCharacter.LFunction χ (t : ℂ)‖) :=
    ((DirichletCharacter.differentiable_LFunction hχ).continuous.comp
      Complex.continuous_ofReal).norm
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hc.continuousOn
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro t ht
  exact (hB ⟨t, ht, rfl⟩).trans (le_max_left _ _)

/-- Every exponent used in the weighted argument lies in the compact
interval chosen above. -/
theorem taoExponent_mem_fixed_Icc {X : ℕ} (hX : 2 ≤ X) :
    taoExponent X ∈ Set.Icc (1 : ℝ) (1 + (Real.log 2)⁻¹) := by
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hXpos : (0 : ℝ) < X := by
    exact_mod_cast (show 0 < X by omega)
  have hlogMono : Real.log 2 ≤ Real.log (X : ℝ) :=
    Real.strictMonoOn_log.monotoneOn (by norm_num)
      hXpos
      (by exact_mod_cast hX)
  constructor
  · unfold taoExponent
    exact le_add_of_nonneg_right (inv_nonneg.mpr hlogX.le)
  · unfold taoExponent
    simpa only [add_comm] using add_le_add_left (inv_anti₀ hlogTwo hlogMono) 1

/-- Uniform boundedness of an ordinary nonprincipal character series at
the exponents used below. -/
theorem exists_nonprincipal_characterLSeries_bound {r : ℕ} [NeZero r]
    (χ : DirichletCharacter ℂ r) (hχ : χ ≠ 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ X : ℕ, 2 ≤ X →
      ‖LSeries (fun n : ℕ ↦ χ n) (taoExponent X)‖ ≤ B := by
  obtain ⟨B, hB0, hB⟩ := exists_nonprincipal_LFunction_bound χ hχ
  refine ⟨B, hB0, ?_⟩
  intro X hX
  rw [← DirichletCharacter.LFunction_eq_LSeries χ
    (by simpa using one_lt_taoExponent (lt_of_lt_of_le one_lt_two hX))]
  exact hB _ (taoExponent_mem_fixed_Icc hX)

/-- In the open unit disk, Mathlib's logarithm of the inverse Euler factor
is exactly the negative logarithm used by the Euler-product theorem. -/
theorem neg_log_one_sub_eq_log_inv {z : ℂ} (hz : ‖z‖ < 1) :
    -Complex.log (1 - z) = Complex.log (1 - z)⁻¹ := by
  exact (Complex.log_inv _ (Complex.slitPlane_arg_ne_pi
    (Complex.mem_slitPlane_of_norm_lt_one (z := -z)
      (by simpa only [norm_neg] using hz)))).symm

/-- The logarithm of one Euler factor is its linear term up to a quadratic
error, in the normalization used in this file. -/
theorem norm_neg_log_one_sub_sub_self_le {z : ℂ} (hz : ‖z‖ < 1) :
    ‖-Complex.log (1 - z) - z‖ ≤
      ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 := by
  rw [neg_log_one_sub_eq_log_inv hz]
  exact Complex.norm_log_one_sub_inv_sub_self_le hz

/-- On the half disk the quadratic Taylor remainder has coefficient one. -/
theorem norm_neg_log_one_sub_sub_self_le_sq {z : ℂ}
    (hz : ‖z‖ ≤ 1 / 2) :
    ‖-Complex.log (1 - z) - z‖ ≤ ‖z‖ ^ 2 := by
  have hzlt : ‖z‖ < 1 := hz.trans_lt (by norm_num)
  refine (norm_neg_log_one_sub_sub_self_le hzlt).trans ?_
  have hinv : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_le_iff_one_le_mul₀' (by linarith : 0 < 1 - ‖z‖)]
    nlinarith
  calc
    ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 ≤ ‖z‖ ^ 2 * 2 / 2 := by
      gcongr
    _ = ‖z‖ ^ 2 := by ring

/-- Lipschitz comparison of two local Euler logarithms, with the prime-power
terms isolated as an absolutely summable quadratic error. -/
theorem norm_neg_log_one_sub_sub_neg_log_one_sub_le
    {z w : ℂ} (hz : ‖z‖ ≤ 1 / 2) (hw : ‖w‖ ≤ 1 / 2) :
    ‖-Complex.log (1 - z) - (-Complex.log (1 - w))‖ ≤
      ‖z - w‖ + ‖z‖ ^ 2 + ‖w‖ ^ 2 := by
  have hid :
      -Complex.log (1 - z) - (-Complex.log (1 - w)) =
        (-Complex.log (1 - z) - z) + (z - w) -
          (-Complex.log (1 - w) - w) := by ring
  rw [hid]
  calc
    ‖(-Complex.log (1 - z) - z) + (z - w) -
          (-Complex.log (1 - w) - w)‖ ≤
        ‖(-Complex.log (1 - z) - z) + (z - w)‖ +
          ‖-Complex.log (1 - w) - w‖ := norm_sub_le _ _
    _ ≤ (‖-Complex.log (1 - z) - z‖ + ‖z - w‖) +
          ‖-Complex.log (1 - w) - w‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ ≤ (‖z‖ ^ 2 + ‖z - w‖) + ‖w‖ ^ 2 :=
      add_le_add
        (add_le_add (norm_neg_log_one_sub_sub_self_le_sq hz) le_rfl)
        (norm_neg_log_one_sub_sub_self_le_sq hw)
    _ = ‖z - w‖ + ‖z‖ ^ 2 + ‖w‖ ^ 2 := by ring

/-- The positive von Mangoldt series which dominates the sum over primes is
absolutely summable to the right of `1`. -/
theorem summable_vonMangoldt_div_log_rpow {u : ℝ} (hu : 1 < u) :
    Summable (fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n /
        ((n : ℝ) ^ u * Real.log (n : ℝ))) := by
  open ArithmeticFunction in
    refine (Real.summable_nat_rpow.mpr (by linarith : -u < -1)).of_nonneg_of_le
      (fun n ↦ by
        by_cases hn : n ≤ 1
        · interval_cases n <;> simp
        · have hn' : 1 < n := by omega
          exact div_nonneg vonMangoldt_nonneg
            (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
              (Real.log_pos (by exact_mod_cast hn')).le)) ?_
  intro n
  by_cases hn : n ≤ 1
  · interval_cases n
    · simpa using Real.rpow_nonneg (show (0 : ℝ) ≤ 0 by norm_num) (-u)
    · simp
  have hn' : 1 < n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast hn')
  have hratio : ArithmeticFunction.vonMangoldt n /
      Real.log (n : ℝ) ≤ 1 :=
    (div_le_one hlog).2 ArithmeticFunction.vonMangoldt_le_log
  rw [Real.rpow_neg hnpos.le]
  calc
    ArithmeticFunction.vonMangoldt n /
          ((n : ℝ) ^ u * Real.log (n : ℝ)) =
        (ArithmeticFunction.vonMangoldt n / Real.log (n : ℝ)) *
          ((n : ℝ) ^ u)⁻¹ := by ring
    _ ≤ 1 * ((n : ℝ) ^ u)⁻¹ :=
      mul_le_mul_of_nonneg_right hratio (by positivity)
    _ = ((n : ℝ) ^ u)⁻¹ := one_mul _

/-- The prime `p^{-u}` series is bounded by `log ζ(u)`.  This is the
quantitative replacement for an explicit decomposition into prime blocks. -/
theorem tsum_primes_rpow_le_log_riemannZeta {u : ℝ} (hu : 1 < u) :
    (∑' p : Nat.Primes, (p : ℝ) ^ (-u)) ≤
      Real.log (riemannZeta (u : ℂ)).re := by
  open ArithmeticFunction in
    let F : ℕ → ℝ := fun n ↦ Λ n / ((n : ℝ) ^ u * Real.log (n : ℝ))
    have hF : Summable F := by
      simpa only [F] using summable_vonMangoldt_div_log_rpow hu
    rw [log_riemannZeta_eq hu]
    change (∑' p : Nat.Primes, (p : ℝ) ^ (-u)) ≤ ∑' n : ℕ, F n
    have heq (p : Nat.Primes) : (p : ℝ) ^ (-u) = F p := by
      dsimp [F]
      rw [vonMangoldt_apply_prime p.prop]
      have hlog : Real.log (p : ℝ) ≠ 0 := by
        exact_mod_cast p.prop.log_ne_zero
      have hp : (0 : ℝ) < p := by exact_mod_cast p.prop.pos
      rw [Real.rpow_neg hp.le]
      field_simp
    simp_rw [heq]
    exact Summable.tsum_subtype_le F {n : ℕ | n.Prime}
      (fun _ ↦ by positivity) hF

/-- The square-distance summand on the set of primes. -/
def primeDistanceSquare (h : ℕ →*₀ ℂ) (p : Nat.Primes) : ℝ :=
  ‖h p - 1‖ ^ 2 / (p : ℝ)

theorem sum_primeDistanceSquare_le {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h) {D : ℝ}
    (hD : ∀ X : ℕ, pretentiousMass h X ≤ D)
    (S : Finset Nat.Primes) :
    ∑ p ∈ S, primeDistanceSquare h p ≤ 2 * D := by
  let e : Nat.Primes ↪ ℕ := ⟨fun p ↦ p, fun _ _ hp ↦ Subtype.ext hp⟩
  let T : Finset ℕ := S.map e
  obtain ⟨N, hN⟩ := Finset.exists_nat_subset_range T
  have hsub : T ⊆ Nat.primesLE N := by
    intro p hp
    rcases Finset.mem_map.mp hp with ⟨P, hPS, rfl⟩
    exact Nat.mem_primesLE.mpr ⟨by
      have hpRange := Finset.mem_range.mp
        (hN (Finset.mem_map.mpr ⟨P, hPS, rfl⟩))
      omega, P.prop⟩
  calc
    ∑ p ∈ S, primeDistanceSquare h p =
        ∑ p ∈ T, ‖h p - 1‖ ^ 2 / (p : ℝ) := by
      dsimp [T]
      rw [Finset.sum_map]
      rfl
    _ ≤ ∑ p ∈ Nat.primesLE N,
        ‖h p - 1‖ ^ 2 / (p : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ ↦ by positivity)
    _ = 2 * pretentiousMass h N := sum_norm_sub_one_sq_div hh N
    _ ≤ 2 * D := mul_le_mul_of_nonneg_left (hD N) (by norm_num)

/-- Finite pretentious distance controls the complete square-distance series
over all primes, not just each finite prefix. -/
theorem summable_primeDistanceSquare_and_tsum_le {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h) {D : ℝ}
    (hD : ∀ X : ℕ, pretentiousMass h X ≤ D) :
    Summable (primeDistanceSquare h) ∧
      (∑' p : Nat.Primes, primeDistanceSquare h p) ≤ 2 * D := by
  have hnonneg : ∀ p : Nat.Primes, 0 ≤ primeDistanceSquare h p := fun p ↦ by
    unfold primeDistanceSquare
    positivity
  have hfinite : ∀ S : Finset Nat.Primes,
      ∑ p ∈ S, primeDistanceSquare h p ≤ 2 * D :=
    sum_primeDistanceSquare_le hh hD
  exact ⟨summable_of_sum_le hnonneg hfinite,
    Real.tsum_le_of_sum_le hnonneg hfinite⟩

/-- The linear Euler-log perturbation at real exponent `u`. -/
def weightedPrimeDifference (h : ℕ →*₀ ℂ) (u : ℝ)
    (p : Nat.Primes) : ℝ :=
  ‖h p - 1‖ * (p : ℝ) ^ (-u)

theorem summable_weightedPrimeDifference {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h) {u : ℝ} (hu : 1 < u) :
    Summable (weightedPrimeDifference h u) := by
  have hs : Summable (fun p : Nat.Primes ↦ (p : ℝ) ^ (-u)) :=
    (Real.summable_nat_rpow.mpr (by linarith : -u < -1)).subtype Nat.Prime
  refine (hs.mul_left 2).of_nonneg_of_le (fun p ↦ by
    exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)) ?_
  intro p
  unfold weightedPrimeDifference
  have hnorm : ‖h p - 1‖ ≤ 2 := by
    calc
      ‖h p - 1‖ ≤ ‖h p‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [hh p.prop.ne_zero]; norm_num
  calc
    ‖h p - 1‖ * (p : ℝ) ^ (-u) ≤ 2 * (p : ℝ) ^ (-u) :=
      mul_le_mul_of_nonneg_right hnorm (Real.rpow_nonneg (by positivity) _)
    _ = 2 * (p : ℝ) ^ (-u) := rfl

/-- Infinite Cauchy--Schwarz for the prime perturbation. -/
theorem tsum_weightedPrimeDifference_le_sqrt {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h) {D u : ℝ}
    (hD : ∀ X : ℕ, pretentiousMass h X ≤ D) (hu : 1 < u) :
    (∑' p : Nat.Primes, weightedPrimeDifference h u p) ≤
      Real.sqrt
        ((∑' p : Nat.Primes, primeDistanceSquare h p) *
          (∑' p : Nat.Primes, (p : ℝ) ^ (1 - 2 * u))) := by
  have hf : Summable (primeDistanceSquare h) :=
    (summable_primeDistanceSquare_and_tsum_le hh hD).1
  have hg : Summable (fun p : Nat.Primes ↦ (p : ℝ) ^ (1 - 2 * u)) :=
    (Real.summable_nat_rpow.mpr (by linarith : 1 - 2 * u < -1)).subtype Nat.Prime
  have hr := summable_weightedPrimeDifference hh hu
  refine hr.tsum_le_of_sum_le fun S ↦ Real.le_sqrt_of_sq_le ?_
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (R := ℝ) S
    (r := weightedPrimeDifference h u)
    (f := primeDistanceSquare h)
    (g := fun p : Nat.Primes ↦ (p : ℝ) ^ (1 - 2 * u))
    (fun p hp ↦ by unfold primeDistanceSquare; positivity)
    (fun p hp ↦ Real.rpow_nonneg (by positivity) _)
    (fun p hp ↦ by
      unfold weightedPrimeDifference primeDistanceSquare
      have hp0 : (0 : ℝ) < p := by exact_mod_cast p.prop.pos
      have hpow : ((p : ℝ) ^ (-u)) ^ 2 =
          (p : ℝ) ^ (-1 : ℝ) * (p : ℝ) ^ (1 - 2 * u) := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul hp0.le]
        convert Real.rpow_add hp0 (-1 : ℝ) (1 - 2 * u) using 1 <;> ring
      rw [mul_pow, hpow, Real.rpow_neg_one]
      field_simp
      exact le_rfl)
  refine hcs.trans ?_
  have hA := hf.sum_le_tsum S
    (fun p hp ↦ by unfold primeDistanceSquare; positivity)
  have hB := hg.sum_le_tsum S
    (fun p hp ↦ Real.rpow_nonneg (by positivity) _)
  calc
    (∑ p ∈ S, primeDistanceSquare h p) *
          ∑ p ∈ S, (p : ℝ) ^ (1 - 2 * u) ≤
        (∑' p : Nat.Primes, primeDistanceSquare h p) *
          ∑ p ∈ S, (p : ℝ) ^ (1 - 2 * u) :=
      mul_le_mul_of_nonneg_right hA (Finset.sum_nonneg fun p _ ↦
        Real.rpow_nonneg (by positivity) _)
    _ ≤ (∑' p : Nat.Primes, primeDistanceSquare h p) *
          (∑' p : Nat.Primes, (p : ℝ) ^ (1 - 2 * u)) :=
      mul_le_mul_of_nonneg_left hB (tsum_nonneg fun p ↦ by
        unfold primeDistanceSquare
        positivity)

/-- Quantitative all-primes Cauchy--Schwarz bound.  The second factor is a
logarithm of zeta at `2u-1`, hence has size `log (1/(u-1))` near one. -/
theorem tsum_weightedPrimeDifference_le_logZeta {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h) {D u : ℝ}
    (hD : ∀ X : ℕ, pretentiousMass h X ≤ D) (hu : 1 < u) :
    (∑' p : Nat.Primes, weightedPrimeDifference h u p) ≤
      Real.sqrt (2 * D *
        Real.log (riemannZeta ((2 * u - 1 : ℝ) : ℂ)).re) := by
  refine (tsum_weightedPrimeDifference_le_sqrt hh hD hu).trans ?_
  apply Real.sqrt_le_sqrt
  have hA := (summable_primeDistanceSquare_and_tsum_le hh hD).2
  have hB := tsum_primes_rpow_le_log_riemannZeta
    (show 1 < 2 * u - 1 by linarith)
  have hBrewrite :
      (∑' p : Nat.Primes, (p : ℝ) ^ (1 - 2 * u)) ≤
        Real.log (riemannZeta ((2 * u - 1 : ℝ) : ℂ)).re := by
    simpa only [show -(2 * u - 1) = 1 - 2 * u by ring] using hB
  calc
    (∑' p : Nat.Primes, primeDistanceSquare h p) *
          (∑' p : Nat.Primes, (p : ℝ) ^ (1 - 2 * u)) ≤
        (2 * D) * (∑' p : Nat.Primes, (p : ℝ) ^ (1 - 2 * u)) :=
      mul_le_mul_of_nonneg_right hA (tsum_nonneg fun p ↦
        Real.rpow_nonneg (by positivity) _)
    _ ≤ (2 * D) *
        Real.log (riemannZeta ((2 * u - 1 : ℝ) : ℂ)).re :=
      mul_le_mul_of_nonneg_left hBrewrite
        (mul_nonneg (by norm_num) ((pretentiousMass_nonneg hh 0).trans (hD 0)))
    _ = 2 * D *
        Real.log (riemannZeta ((2 * u - 1 : ℝ) : ℂ)).re := by ring

/-- If a completely multiplicative function is one at every prime dividing
`q`, it is one at every divisor of a power of `q`. -/
theorem map_eq_one_of_dvd_pow {h : ℕ →*₀ ℂ} {q k d : ℕ}
    (hq0 : q ≠ 0)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ q → h p = 1)
    (hd : d ∣ q ^ k) : h d = 1 := by
  induction d using induction_on_primes with
  | zero =>
      have hpow0 : q ^ k ≠ 0 := pow_ne_zero _ hq0
      exact False.elim (hpow0 (zero_dvd_iff.mp hd))
  | one => simp
  | prime_mul p a hp ih =>
      have hpqpow : p ∣ q ^ k := (dvd_mul_right p a).trans hd
      have hpq : p ∣ q := hp.dvd_of_dvd_pow hpqpow
      have haqpow : a ∣ q ^ k := (dvd_mul_left a p).trans hd
      rw [map_mul, hprime p hp hpq, ih haqpow, one_mul]

/-! ## Dirichlet twists and exact unit-residue expansion -/

/-- Coefficients of the twist of `h` by a Dirichlet character. -/
def twistCoefficient {r : ℕ} (h : ℕ →*₀ ℂ)
    (χ : DirichletCharacter ℂ r) (n : ℕ) : ℂ :=
  h n * χ n

theorem twistLSeriesSummable {r : ℕ} {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h) (χ : DirichletCharacter ℂ r)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (twistCoefficient h χ) s := by
  apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1) _ hs
  intro n hn
  rw [twistCoefficient, norm_mul, hh hn]
  simpa using χ.norm_le_one n

/-- The completely multiplicative summand of a Dirichlet twist. -/
def twistedWeightedSummandHom {r : ℕ} (h : ℕ →*₀ ℂ)
    (χ : DirichletCharacter ℂ r) {s : ℂ} (hs : s ≠ 0) : ℕ →*₀ ℂ :=
  h * dirichletSummandHom χ hs

@[simp] theorem twistedWeightedSummandHom_apply {r : ℕ}
    (h : ℕ →*₀ ℂ) (χ : DirichletCharacter ℂ r)
    {s : ℂ} (hs : s ≠ 0) (n : ℕ) :
    twistedWeightedSummandHom h χ hs n =
      h n * χ n * (n : ℂ) ^ (-s) := by
  change h n * (χ n * (n : ℂ) ^ (-s)) = _
  ring

theorem summable_norm_twistedWeightedSummandHom {r : ℕ}
    {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h)
    (χ : DirichletCharacter ℂ r) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ ↦
      ‖twistedWeightedSummandHom h χ (ne_zero_of_one_lt_re hs) n‖) := by
  refine (summable_riemannZetaSummand hs).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) ?_
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [twistedWeightedSummandHom]
  · rw [twistedWeightedSummandHom_apply]
    change ‖h n * χ n * (n : ℂ) ^ (-s)‖ ≤ ‖(n : ℂ) ^ (-s)‖
    simp only [norm_mul, hh hn, one_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one n)

theorem tsum_twistedWeightedSummandHom_eq_LSeries {r : ℕ}
    (h : ℕ →*₀ ℂ) (χ : DirichletCharacter ℂ r)
    {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ,
      twistedWeightedSummandHom h χ (ne_zero_of_one_lt_re hs) n) =
      LSeries (twistCoefficient h χ) s := by
  apply tsum_congr
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [twistedWeightedSummandHom, twistCoefficient]
  · simp only [twistedWeightedSummandHom_apply,
      LSeries.term_of_ne_zero hn, twistCoefficient, div_eq_mul_inv,
      Complex.cpow_neg]

/-- Logarithmic Euler product for a Dirichlet twist of `h`. -/
theorem twistedEulerProduct_exp_log {r : ℕ} {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h) (χ : DirichletCharacter ℂ r)
    {s : ℂ} (hs : 1 < s.re) :
    Complex.exp
        (∑' p : Nat.Primes,
          -Complex.log (1 - h p * χ p * (p : ℂ) ^ (-s))) =
      LSeries (twistCoefficient h χ) s := by
  rw [← tsum_twistedWeightedSummandHom_eq_LSeries h χ hs]
  simpa only [twistedWeightedSummandHom_apply] using
    EulerProduct.exp_tsum_primes_log_eq_tsum
      (summable_norm_twistedWeightedSummandHom hh χ hs)

/-- Logarithmic Euler product for the untwisted singular series. -/
theorem weightedEulerProduct_exp_log {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h) {s : ℂ} (hs : 1 < s.re) :
    Complex.exp
        (∑' p : Nat.Primes,
          -Complex.log (1 - h p * (p : ℂ) ^ (-s))) =
      LSeries h s := by
  rw [← tsum_weightedSummandHom_eq_LSeries hs]
  simpa only [weightedSummandHom_apply] using
    EulerProduct.exp_tsum_primes_log_eq_tsum
      (summable_norm_weightedSummandHom hh hs)

/-- The series in one residue class.  The representative is a value of
`ZMod r`, so this definition is invariant under changing an integer
representative. -/
def residueCoefficient {r : ℕ} (h : ℕ →*₀ ℂ) (a : ZMod r)
    (n : ℕ) : ℂ :=
  if (n : ZMod r) = a then h n else 0

def residueLSeries {r : ℕ} (h : ℕ →*₀ ℂ) (a : ZMod r) (s : ℂ) : ℂ :=
  LSeries (residueCoefficient h a) s

theorem residueLSeriesSummable {r : ℕ} {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h) (a : ZMod r) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (residueCoefficient h a) s := by
  apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1) _ hs
  intro n hn
  unfold residueCoefficient
  split_ifs
  · exact (hh hn).le
  · simp

/-! ## Exact gcd reduction for arbitrary residue classes -/

/-- The common divisor which obstructs an arbitrary residue class from
being a unit class. -/
def residueGCD {r : ℕ} (a : ZMod r) : ℕ :=
  Nat.gcd a.val r

/-- The modulus left after removing the common divisor of a residue and its
modulus. -/
def reducedModulus {r : ℕ} (a : ZMod r) : ℕ :=
  r / residueGCD a

/-- The resulting primitive residue class. -/
def reducedResidue {r : ℕ} (a : ZMod r) : ZMod (reducedModulus a) :=
  a.val / residueGCD a

/-- The scalar by which a residue Dirichlet series changes after removing
its common divisor. -/
def residueScale (h : ℕ →*₀ ℂ) (d : ℕ) (s : ℂ) : ℂ :=
  h d * (d : ℂ) ^ (-s)

lemma residueGCD_pos {r : ℕ} [NeZero r] (a : ZMod r) :
    0 < residueGCD a := by
  exact Nat.gcd_pos_of_pos_right _ (NeZero.pos r)

lemma residueGCD_dvd_val {r : ℕ} (a : ZMod r) :
    residueGCD a ∣ a.val :=
  Nat.gcd_dvd_left _ _

lemma residueGCD_dvd_modulus {r : ℕ} (a : ZMod r) :
    residueGCD a ∣ r :=
  Nat.gcd_dvd_right _ _

lemma reducedModulus_pos {r : ℕ} [NeZero r] (a : ZMod r) :
    0 < reducedModulus a := by
  exact Nat.div_pos
    (Nat.le_of_dvd (NeZero.pos r) (residueGCD_dvd_modulus a))
    (residueGCD_pos a)

lemma reducedModulus_dvd {r : ℕ} [NeZero r] (a : ZMod r) :
    reducedModulus a ∣ r := by
  exact ⟨residueGCD a, by
    rw [Nat.mul_comm]
    exact (Nat.mul_div_cancel' (residueGCD_dvd_modulus a)).symm⟩

/-- Dividing a residue and its modulus by their gcd produces a unit. -/
theorem reducedResidue_isUnit {r : ℕ} [NeZero r] (a : ZMod r) :
    IsUnit (reducedResidue a) := by
  apply (ZMod.isUnit_iff_coprime _ _).2
  exact Nat.coprime_div_gcd_div_gcd (residueGCD_pos a)

/-- Congruence by an arbitrary residue is equivalent, after factoring out
the gcd, to congruence by its reduced unit residue. -/
theorem natCast_mul_residueGCD_eq_iff {r : ℕ} [NeZero r]
    (a : ZMod r) (m : ℕ) :
    ((residueGCD a * m : ℕ) : ZMod r) = a ↔
      (m : ZMod (reducedModulus a)) = reducedResidue a := by
  have hdA : residueGCD a ∣ a.val := residueGCD_dvd_val a
  have hdR : residueGCD a ∣ r := residueGCD_dvd_modulus a
  have hd0 : residueGCD a ≠ 0 := (residueGCD_pos a).ne'
  constructor
  · intro h
    have hmod : residueGCD a * m ≡ a.val [MOD r] :=
      (ZMod.natCast_eq_natCast_iff ..).1
        (h.trans (ZMod.natCast_zmod_val a).symm)
    have hmod' : m ≡ a.val / residueGCD a [MOD reducedModulus a] := by
      apply (Nat.ModEq.mul_left_cancel_iff' hd0).1
      simpa [reducedModulus, Nat.mul_div_cancel' hdA,
        Nat.mul_div_cancel' hdR] using hmod
    exact (ZMod.natCast_eq_natCast_iff ..).2 hmod'
  · intro h
    have hmod' : m ≡ a.val / residueGCD a [MOD reducedModulus a] :=
      (ZMod.natCast_eq_natCast_iff ..).1 h
    have hmod : residueGCD a * m ≡ a.val [MOD r] := by
      have := (Nat.ModEq.mul_left_cancel_iff' hd0).2 hmod'
      simpa [reducedModulus, Nat.mul_div_cancel' hdA,
        Nat.mul_div_cancel' hdR] using this
    exact ((ZMod.natCast_eq_natCast_iff ..).2 hmod).trans
      (ZMod.natCast_zmod_val a)

/-- Every integer in the class `a (mod r)` is divisible by `gcd(a,r)`. -/
theorem residueGCD_dvd_of_natCast_eq {r : ℕ} [NeZero r]
    (a : ZMod r) {n : ℕ} (hn : (n : ZMod r) = a) :
    residueGCD a ∣ n := by
  have hm : n ≡ a.val [MOD r] := by
    rwa [show a = (a.val : ZMod r) by simp,
      ZMod.natCast_eq_natCast_iff] at hn
  have hm' : n ≡ a.val [MOD residueGCD a] := by
    rw [Nat.modEq_iff_dvd]
    exact (Int.natCast_dvd_natCast.mpr (residueGCD_dvd_modulus a)).trans hm.dvd
  exact Nat.modEq_zero_iff_dvd.mp
    (hm'.trans (Nat.modEq_zero_iff_dvd.mpr (residueGCD_dvd_val a)))

lemma residueCoefficient_eq_zero_of_not_residueGCD_dvd
    {r : ℕ} [NeZero r] (h : ℕ →*₀ ℂ) (a : ZMod r) {n : ℕ}
    (hn : ¬ residueGCD a ∣ n) : residueCoefficient h a n = 0 := by
  unfold residueCoefficient
  rw [if_neg]
  exact fun hz ↦ hn (residueGCD_dvd_of_natCast_eq a hz)

private lemma residueTerm_gcd_reduction {r : ℕ} [NeZero r]
    (h : ℕ →*₀ ℂ) (a : ZMod r) (s : ℂ) (m : ℕ) :
    LSeries.term (residueCoefficient h a) s (residueGCD a * m) =
      residueScale h (residueGCD a) s *
        LSeries.term (residueCoefficient h (reducedResidue a)) s m := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [LSeries.term, residueScale]
  have hd0 : residueGCD a ≠ 0 := (residueGCD_pos a).ne'
  have hdm : residueGCD a * m ≠ 0 := Nat.mul_ne_zero hd0 hm
  rw [LSeries.term_of_ne_zero hdm, LSeries.term_of_ne_zero hm]
  unfold residueCoefficient
  by_cases hc : (m : ZMod (reducedModulus a)) = reducedResidue a
  · rw [if_pos ((natCast_mul_residueGCD_eq_iff a m).2 hc), if_pos hc, map_mul]
    rw [show ((residueGCD a * m : ℕ) : ℂ) ^ s =
      (residueGCD a : ℂ) ^ s * (m : ℂ) ^ s by
        simpa only [Nat.cast_mul] using
          (Complex.natCast_mul_natCast_cpow (residueGCD a) m s)]
    simp only [residueScale, div_eq_mul_inv, Complex.cpow_neg, mul_inv_rev]
    ring
  · rw [if_neg (not_congr (natCast_mul_residueGCD_eq_iff a m) |>.mpr hc),
      if_neg hc]
    simp

/-- Exact gcd reduction for an arbitrary residue Dirichlet series:
`n = d m` contributes the factor `h(d)d⁻ˢ`, and the remaining residue is a
unit modulo `r/d`. -/
theorem residueLSeries_gcd_reduction {r : ℕ} [NeZero r]
    {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h) (a : ZMod r)
    {s : ℂ} (hs : 1 < s.re) :
    residueLSeries h a s =
      residueScale h (residueGCD a) s *
        residueLSeries h (reducedResidue a) s := by
  let T : ℕ → ℂ := fun n ↦ LSeries.term (residueCoefficient h a) s n
  let g : ℕ → ℕ := fun m ↦ residueGCD a * m
  have hg : Function.Injective g := by
    intro x y hxy
    exact Nat.eq_of_mul_eq_mul_left (residueGCD_pos a) hxy
  have hzero : ∀ n ∉ Set.range g, T n = 0 := by
    intro n hn
    have hndvd : ¬ residueGCD a ∣ n := by
      intro hd
      obtain ⟨m, rfl⟩ := hd
      exact hn ⟨m, by simp [g, Nat.mul_comm]⟩
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [T]
    · change LSeries.term (residueCoefficient h a) s n = 0
      rw [LSeries.term_of_ne_zero hn0,
        residueCoefficient_eq_zero_of_not_residueGCD_dvd h a hndvd, zero_div]
  have hsumT : Summable T := residueLSeriesSummable hh a hs
  have hreindex : (∑' m, T (g m)) = ∑' n, T n :=
    ((hg.hasSum_iff hzero).2 hsumT.hasSum).tsum_eq
  calc
    residueLSeries h a s = ∑' n, T n := rfl
    _ = ∑' m, T (g m) := hreindex.symm
    _ = ∑' m, residueScale h (residueGCD a) s *
        LSeries.term (residueCoefficient h (reducedResidue a)) s m := by
      apply tsum_congr
      intro m
      dsimp only [T, g]
      exact residueTerm_gcd_reduction h a s m
    _ = residueScale h (residueGCD a) s *
        ∑' m, LSeries.term (residueCoefficient h (reducedResidue a)) s m :=
      tsum_mul_left
    _ = residueScale h (residueGCD a) s *
        residueLSeries h (reducedResidue a) s := rfl

/-- Character orthogonality, with the coefficient `h(n)` included. -/
theorem residueCoefficient_eq_characterAverage {r : ℕ} [NeZero r]
    (h : ℕ →*₀ ℂ) {a : ZMod r} (ha : IsUnit a) (n : ℕ) :
    residueCoefficient h a n =
      (r.totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ r, χ a⁻¹ * twistCoefficient h χ n := by
  have htot : (r.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos r)).ne'
  rw [eq_inv_mul_iff_mul_eq₀ htot]
  simp only [residueCoefficient, twistCoefficient]
  have hsum :
      (∑ χ : DirichletCharacter ℂ r, χ a⁻¹ * (h n * χ n)) =
        (∑ χ : DirichletCharacter ℂ r, χ a⁻¹ * χ n) * h n := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro χ _
    ring
  rw [hsum]
  rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha n]
  by_cases han : (n : ZMod r) = a
  · rw [if_pos han, if_pos han.symm]
  · have hna : a ≠ (n : ZMod r) := fun h ↦ han h.symm
    simp only [han, ↓reduceIte, hna, mul_zero, zero_mul]

/-- Exact expansion of a unit residue-class series into finitely many
Dirichlet twists. -/
theorem residueLSeries_eq_characterAverage {r : ℕ} [NeZero r]
    {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h) {a : ZMod r} (ha : IsUnit a)
    {s : ℂ} (hs : 1 < s.re) :
    residueLSeries h a s =
      (r.totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ r,
          χ a⁻¹ * LSeries (twistCoefficient h χ) s := by
  unfold residueLSeries
  rw [show residueCoefficient h a =
      (r.totient : ℂ)⁻¹ •
        ∑ χ : DirichletCharacter ℂ r,
          χ a⁻¹ • twistCoefficient h χ by
    funext n
    simpa only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, ← mul_assoc] using
      residueCoefficient_eq_characterAverage h ha n]
  rw [LSeries_smul, LSeries_sum]
  · simp_rw [LSeries_smul]
  · intro χ _
    exact (twistLSeriesSummable hh χ hs).smul _

/-- The principal twist at modulus `r`. -/
def principalTwistSeries (h : ℕ →*₀ ℂ) (r : ℕ) (s : ℂ) : ℂ :=
  LSeries (twistCoefficient h (1 : DirichletCharacter ℂ r)) s

/-- The contribution from the nonprincipal characters. -/
def nonprincipalCharacters (r : ℕ) :
    Finset (DirichletCharacter ℂ r) := by
  classical
  exact Finset.univ.erase 1

/-- The contribution from the nonprincipal characters. -/
def nonprincipalTwistSum (h : ℕ →*₀ ℂ) (r : ℕ)
    (a : ZMod r) (s : ℂ) : ℂ :=
  by
    classical
    exact ∑ χ ∈ nonprincipalCharacters r,
      χ a⁻¹ * LSeries (twistCoefficient h χ) s

/-- Principal/nonprincipal decomposition of the exact character expansion. -/
theorem residueLSeries_eq_principal_add_nonprincipal {r : ℕ} [NeZero r]
    {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h) {a : ZMod r} (ha : IsUnit a)
    {s : ℂ} (hs : 1 < s.re) :
    residueLSeries h a s =
      (r.totient : ℂ)⁻¹ * principalTwistSeries h r s +
      (r.totient : ℂ)⁻¹ * nonprincipalTwistSum h r a s := by
  classical
  rw [residueLSeries_eq_characterAverage hh ha hs]
  have ha' : IsUnit a⁻¹ :=
    isUnit_of_dvd_one ⟨a, (ZMod.inv_mul_of_unit a ha).symm⟩
  have hone : (1 : DirichletCharacter ℂ r) a⁻¹ = 1 :=
    MulChar.one_apply ha'
  unfold nonprincipalTwistSum nonprincipalCharacters
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : DirichletCharacter ℂ r))]
  simp only [principalTwistSeries, hone, one_mul]
  ring

/-! ## Quantitative uniform reduction -/

/-- A bound for all nonprincipal twists at a fixed modulus and exponent. -/
def NonprincipalTwistsBounded (h : ℕ →*₀ ℂ) (r : ℕ)
    (s : ℂ) (E : ℝ) : Prop :=
  ∀ χ : DirichletCharacter ℂ r, χ ≠ 1 →
    ‖LSeries (twistCoefficient h χ) s‖ ≤ E

/-- Exact uniform residue error bound.  Notice that the hypotheses do not
depend on the unit residue `a`; consequently the conclusion is uniform in
that residue.  This is the interface consumed by the BCC layer. -/
theorem norm_residueLSeries_sub_main_le {r : ℕ} [NeZero r]
    {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h) {s : ℂ} (hs : 1 < s.re)
    (M : ℂ) (E₀ E : ℝ)
    (hprincipal :
      ‖(r.totient : ℂ)⁻¹ * principalTwistSeries h r s - M‖ ≤ E₀)
    (hnonprincipal : NonprincipalTwistsBounded h r s E)
    {a : ZMod r} (ha : IsUnit a) :
    ‖residueLSeries h a s - M‖ ≤
      E₀ + ‖(r.totient : ℂ)⁻¹‖ *
        ((nonprincipalCharacters r).card : ℝ) * E := by
  classical
  rw [residueLSeries_eq_principal_add_nonprincipal hh ha hs]
  have hsplit :
      (r.totient : ℂ)⁻¹ * principalTwistSeries h r s +
          (r.totient : ℂ)⁻¹ * nonprincipalTwistSum h r a s - M =
        ((r.totient : ℂ)⁻¹ * principalTwistSeries h r s - M) +
          (r.totient : ℂ)⁻¹ * nonprincipalTwistSum h r a s := by ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  refine add_le_add hprincipal ?_
  rw [norm_mul]
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg ((r.totient : ℂ)⁻¹))
  unfold nonprincipalTwistSum
  have hnorm :
      ‖∑ χ ∈ nonprincipalCharacters r,
          χ a⁻¹ * LSeries (twistCoefficient h χ) s‖ ≤
        ∑ χ ∈ nonprincipalCharacters r,
          ‖χ a⁻¹ * LSeries (twistCoefficient h χ) s‖ := by
    exact norm_sum_le _ _
  refine hnorm.trans ?_
  calc
    (∑ χ ∈ nonprincipalCharacters r,
        ‖χ a⁻¹ * LSeries (twistCoefficient h χ) s‖) ≤
        ∑ _χ ∈ nonprincipalCharacters r, E := by
      apply Finset.sum_le_sum
      intro χ hχ
      rw [norm_mul]
      have hne : χ ≠ 1 := by
        simpa [nonprincipalCharacters] using hχ
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (χ.norm_le_one _)).trans (hnonprincipal χ hne)
    _ = ((nonprincipalCharacters r).card : ℝ) * E := by
      simp [nsmul_eq_mul]

/-- The preceding bound simultaneously for every divisor of `q^k`.  This
packages exactly the modulus-uniform statement needed in Section 4; the only
remaining inputs are a principal estimate and uniform nonprincipal twisted
estimates for those divisors. -/
theorem uniform_residue_estimate_for_divisors
    (h : ℕ →*₀ ℂ) (hh : HasUnitNorm h)
    {s : ℂ} (hs : 1 < s.re) (q k : ℕ)
    (M : ℕ → ℂ) (E₀ E : ℕ → ℝ)
    (hprincipal : ∀ r, r ∣ q ^ k → r ≠ 0 →
      ‖(r.totient : ℂ)⁻¹ * principalTwistSeries h r s - M r‖ ≤ E₀ r)
    (hnonprincipal : ∀ r, r ∣ q ^ k → r ≠ 0 →
      NonprincipalTwistsBounded h r s (E r)) :
    ∀ r, r ∣ q ^ k → r ≠ 0 → ∀ a : ZMod r, IsUnit a →
      ‖residueLSeries h a s - M r‖ ≤
        E₀ r + ‖(r.totient : ℂ)⁻¹‖ *
          ((nonprincipalCharacters r).card : ℝ) * E r := by
  classical
  intro r hr hr0 a ha
  letI : NeZero r := ⟨hr0⟩
  exact norm_residueLSeries_sub_main_le hh hs (M r) (E₀ r) (E r)
    (hprincipal r hr hr0) (hnonprincipal r hr hr0) ha

/-! ## Quantitative estimates for arbitrary residue classes -/

/-- Gcd reduction transports a unit-residue estimate at modulus `r/d` to
an arbitrary residue at modulus `r`.  The first term is the transported
unit error and the second is the exact error made by replacing the scaled
main term by a common main term.

This is the quantitative form of the two factors in Tao's argument:
`d⁻ˢ` multiplies the reduced residue series, while a normalized main term
`S/(r/d)` consequently acquires the factor `d^(1-s)` relative to `S/r`. -/
theorem norm_residueLSeries_sub_main_arbitrary_le
    {r : ℕ} [NeZero r] {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h) {s : ℂ} (hs : 1 < s.re)
    (M : ℕ → ℂ) (U Esc : ℕ → ℝ) (Main : ℂ)
    (hunit : ∀ t, t ∣ r → t ≠ 0 → ∀ b : ZMod t, IsUnit b →
      ‖residueLSeries h b s - M t‖ ≤ U t)
    (hscale : ∀ d, d ∣ r → d ≠ 0 →
      ‖residueScale h d s * M (r / d) - Main‖ ≤ Esc d)
    (a : ZMod r) :
    ‖residueLSeries h a s - Main‖ ≤
      ‖residueScale h (residueGCD a) s‖ * U (reducedModulus a) +
        Esc (residueGCD a) := by
  let d := residueGCD a
  let t := reducedModulus a
  let b := reducedResidue a
  let c := residueScale h d s
  have hd : d ∣ r := residueGCD_dvd_modulus a
  have hd0 : d ≠ 0 := (residueGCD_pos a).ne'
  have ht : t ∣ r := reducedModulus_dvd a
  have ht0 : t ≠ 0 := (reducedModulus_pos a).ne'
  have hb : IsUnit b := reducedResidue_isUnit a
  have hred : ‖residueLSeries h b s - M t‖ ≤ U t :=
    hunit t ht ht0 b hb
  have hsc : ‖c * M t - Main‖ ≤ Esc d := by
    simpa only [c, t, d, reducedModulus] using hscale d hd hd0
  rw [residueLSeries_gcd_reduction hh a hs]
  have hid :
      residueScale h (residueGCD a) s * residueLSeries h (reducedResidue a) s -
          Main =
        c * (residueLSeries h b s - M t) + (c * M t - Main) := by
    dsimp only [c, b, t, d]
    ring
  rw [hid]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  exact add_le_add
    (mul_le_mul_of_nonneg_left hred (norm_nonneg c)) hsc

/-- A scale-independent arbitrary-residue estimate, obtained by budgeting
the transported unit error and the main-term scaling error uniformly over
all possible gcds. -/
theorem uniform_arbitrary_residue_estimate
    {r : ℕ} [NeZero r] {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h) {s : ℂ} (hs : 1 < s.re)
    (M : ℕ → ℂ) (U Esc : ℕ → ℝ) (Main : ℂ) (Err : ℝ)
    (hunit : ∀ t, t ∣ r → t ≠ 0 → ∀ b : ZMod t, IsUnit b →
      ‖residueLSeries h b s - M t‖ ≤ U t)
    (hscale : ∀ d, d ∣ r → d ≠ 0 →
      ‖residueScale h d s * M (r / d) - Main‖ ≤ Esc d)
    (hbudget : ∀ d, d ∣ r → d ≠ 0 →
      ‖residueScale h d s‖ * U (r / d) + Esc d ≤ Err) :
    ∀ a : ZMod r, ‖residueLSeries h a s - Main‖ ≤ Err := by
  intro a
  refine (norm_residueLSeries_sub_main_arbitrary_le hh hs M U Esc Main
    hunit hscale a).trans ?_
  simpa only [reducedModulus] using
    hbudget (residueGCD a) (residueGCD_dvd_modulus a)
      (residueGCD_pos a).ne'

/-- Fully expands the arbitrary-class estimate into the
principal/nonprincipal character estimates at every divisor of `q^k`.
Thus the arbitrary-residue conclusion has no unit-residue hypothesis. -/
theorem uniform_arbitrary_residue_estimate_for_divisors
    (h : ℕ →*₀ ℂ) (hh : HasUnitNorm h)
    {s : ℂ} (hs : 1 < s.re) (q k : ℕ)
    (M : ℕ → ℂ) (E₀ E Esc : ℕ → ℝ) (Main : ℂ) (Err : ℝ)
    (hprincipal : ∀ t, t ∣ q ^ k → t ≠ 0 →
      ‖(t.totient : ℂ)⁻¹ * principalTwistSeries h t s - M t‖ ≤ E₀ t)
    (hnonprincipal : ∀ t, t ∣ q ^ k → t ≠ 0 →
      NonprincipalTwistsBounded h t s (E t))
    (hscale : ∀ r, r ∣ q ^ k → r ≠ 0 → ∀ d, d ∣ r → d ≠ 0 →
      ‖residueScale h d s * M (r / d) - Main‖ ≤ Esc d)
    (hbudget : ∀ r, r ∣ q ^ k → r ≠ 0 → ∀ d, d ∣ r → d ≠ 0 →
      ‖residueScale h d s‖ *
          (E₀ (r / d) + ‖(((r / d).totient : ℂ)⁻¹)‖ *
            ((nonprincipalCharacters (r / d)).card : ℝ) * E (r / d)) +
        Esc d ≤ Err) :
    ∀ r, r ∣ q ^ k → r ≠ 0 → ∀ a : ZMod r,
      ‖residueLSeries h a s - Main‖ ≤ Err := by
  intro r hr hr0
  letI : NeZero r := ⟨hr0⟩
  apply uniform_arbitrary_residue_estimate hh hs M
    (fun t ↦ E₀ t + ‖((t.totient : ℂ)⁻¹)‖ *
      ((nonprincipalCharacters t).card : ℝ) * E t) Esc Main Err
  · intro t ht ht0 b hb
    letI : NeZero t := ⟨ht0⟩
    exact norm_residueLSeries_sub_main_le hh hs (M t) (E₀ t) (E t)
      (hprincipal t (ht.trans hr) ht0)
      (hnonprincipal t (ht.trans hr) ht0) hb
  · exact hscale r hr hr0
  · exact hbudget r hr hr0

/-- If `h(d)=1`, the scaled normalized main term has exactly the familiar
`d^(1-s)` correction:
`d⁻ˢ · S/(r/d) = (S/r) d^(1-s)`. -/
theorem residueScale_mul_div_reducedModulus
    {h : ℕ →*₀ ℂ} {r d : ℕ} (hd : d ∣ r) (hr0 : r ≠ 0)
    (hdone : h d = 1) (s S : ℂ) :
    residueScale h d s * (S / ((r / d : ℕ) : ℂ)) =
      (S / (r : ℂ)) * (d : ℂ) ^ (1 - s) := by
  have hd0 : d ≠ 0 := fun hz ↦ hr0 (by simpa [hz] using hd)
  have ht0 : r / d ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hr0) hd)
      (Nat.pos_of_ne_zero hd0)).ne'
  have hrfac : (r : ℂ) = (d : ℂ) * ((r / d : ℕ) : ℂ) := by
    exact_mod_cast (Nat.mul_div_cancel' hd).symm
  have hdpow : (d : ℂ) ^ (1 - s) = (d : ℂ) * (d : ℂ) ^ (-s) := by
    rw [show (1 : ℂ) - s = 1 + (-s) by ring,
      Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hd0)]
    simp
  rw [residueScale, hdone, one_mul, hdpow, hrfac]
  field_simp

end

end Erdos67.EulerResidue
