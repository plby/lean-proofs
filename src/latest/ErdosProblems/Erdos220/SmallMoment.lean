import ErdosProblems.Erdos220.Basic
import ErdosProblems.Erdos220.Mertens

/-!
# The smooth-modulus sixth moment

This file contains the elementary algebraic parts of the small-prime
sixth-moment argument used for Erdős problem 220.  The genuinely analytic
input is the constrained-fraction estimate; the lemmas below isolate the
finite Markov step, the local factor `716`, and the absorption of a fixed
power of a logarithm by one power of the interval length.
-/

open scoped BigOperators

namespace Erdos220

/-- An even power of the norm of a real-valued complex number can be kept
as a complex sixth power until after character orthogonality is used. -/
lemma norm_pow_six_eq_re_pow_six_of_im_eq_zero {z : ℂ} (hz : z.im = 0) :
    ‖z‖ ^ 6 = z.re ^ 6 := by
  have hz' : z = (z.re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [hz]
  calc
    ‖z‖ ^ 6 = ‖(z.re : ℂ)‖ ^ 6 :=
      congrArg (fun w : ℂ ↦ ‖w‖ ^ 6) hz'
    _ = z.re ^ 6 := by
      rw [Complex.norm_real, Real.norm_eq_abs, ← abs_pow,
        abs_of_nonneg (by positivity : 0 ≤ z.re ^ 6)]

/-! ## The local divisor factor -/

/-- The local Euler factor left after the six denominator variables have
been summed.  A prime must occur in at least two of the six denominators. -/
noncomputable def sixthLocalFactor (p : ℝ) : ℝ :=
  1 + ∑ j ∈ Finset.Icc 2 6,
    (Nat.choose 6 j : ℝ) * p ^ (j - 1) / (p - 1) ^ j

noncomputable def inverseEulerFactor (p : ℕ) : ℝ :=
  (1 - (p : ℝ)⁻¹)⁻¹

/-- The contribution of one prime occurring in a specified subset of the
six denominator variables. -/
noncomputable def sixthSupportWeight (p : ℝ) (I : Finset (Fin 6)) : ℝ :=
  if 0 < I.card then p ^ (I.card - 1) / (p - 1) ^ I.card else 1

/-- Supports of size one are killed by character orthogonality. -/
def admissibleSixthSupports : Finset (Finset (Fin 6)) :=
  Finset.univ.powerset.filter fun I ↦ I.card ≠ 1

/-- Grouping admissible prime supports by cardinality gives exactly the
local factor used below. -/
lemma sum_sixthSupportWeight_eq (p : ℝ) :
    ∑ I ∈ admissibleSixthSupports, sixthSupportWeight p I =
      sixthLocalFactor p := by
  rw [admissibleSixthSupports, Finset.sum_filter]
  let f : ℕ → ℝ := fun j ↦
    if j ≠ 1 then (if 0 < j then p ^ (j - 1) / (p - 1) ^ j else 1) else 0
  have hgroup := Finset.sum_powerset_apply_card f
    (x := (Finset.univ : Finset (Fin 6)))
  change (∑ I ∈ (Finset.univ : Finset (Fin 6)).powerset, f I.card) =
    sixthLocalFactor p
  rw [hgroup]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num [f, sixthLocalFactor, Finset.sum_Icc_succ_top, Finset.sum_range_succ,
    Nat.choose]
  ring

/-- The elementary numerical identity behind the constant `716`. -/
lemma choose_six_weighted_sum :
    ∑ j ∈ Finset.Icc 2 6, Nat.choose 6 j * 2 ^ j = 716 := by
  norm_num [Finset.sum_Icc_succ_top, Nat.choose]

/-- For `p ≥ 2`, a local term with support size `j` is bounded by
`choose 6 j * 2^j / p`. -/
lemma local_six_term_mul_le {p : ℝ} (hp : 2 ≤ p) {j : ℕ}
    (hj₂ : 2 ≤ j) :
    p * ((Nat.choose 6 j : ℝ) * p ^ (j - 1) / (p - 1) ^ j) ≤
      (Nat.choose 6 j : ℝ) * 2 ^ j := by
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  have hp1 : 0 < p - 1 := by linarith
  have hratio0 : 0 ≤ p / (p - 1) := div_nonneg hp0 hp1.le
  have hratio : p / (p - 1) ≤ 2 := by
    rw [div_le_iff₀ hp1]
    linarith
  have hpow : (p / (p - 1)) ^ j ≤ (2 : ℝ) ^ j :=
    pow_le_pow_left₀ hratio0 hratio _
  have hj₁ : 1 ≤ j := le_trans (by omega) hj₂
  have hident :
      p * (p ^ (j - 1) / (p - 1) ^ j) = (p / (p - 1)) ^ j := by
    rw [div_pow]
    field_simp
    rw [← pow_succ', Nat.sub_add_cancel hj₁]
  rw [mul_div_assoc, ← mul_assoc, mul_comm p (Nat.choose 6 j : ℝ),
    mul_assoc, hident]
  exact mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)

/-- The sum of the nontrivial local contributions is at most `716 / p`. -/
lemma sixthLocalFactor_sub_one_mul_le (p : ℝ) (hp : 2 ≤ p) :
    p * (sixthLocalFactor p - 1) ≤ 716 := by
  rw [sixthLocalFactor]
  simp only [add_sub_cancel_left]
  rw [Finset.mul_sum]
  calc
    ∑ j ∈ Finset.Icc 2 6,
        p * ((Nat.choose 6 j : ℝ) * p ^ (j - 1) / (p - 1) ^ j)
        ≤ ∑ j ∈ Finset.Icc 2 6, (Nat.choose 6 j : ℝ) * 2 ^ j := by
          exact Finset.sum_le_sum fun j hj ↦
            local_six_term_mul_le hp (Finset.mem_Icc.mp hj).1
    _ = 716 := by
      exact_mod_cast choose_six_weighted_sum

/-- Convenient divided form of the local estimate. -/
lemma sixthLocalFactor_le (p : ℝ) (hp : 2 ≤ p) :
    sixthLocalFactor p ≤ 1 + 716 / p := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have h := sixthLocalFactor_sub_one_mul_le p hp
  have h' : sixthLocalFactor p - 1 ≤ 716 / p := by
    rw [le_div_iff₀ hp0]
    simpa [mul_comm] using h
  linarith

/-- The linear local bound is absorbed by the `716`-th power of the inverse
Euler factor. -/
lemma one_add_716_div_le_inverseEuler_pow (p : ℝ) (hp : 2 ≤ p) :
    1 + 716 / p ≤ ((1 - p⁻¹)⁻¹) ^ 716 := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hp1 : 0 < p - 1 := by linarith
  have hfrac : 1 / p ≤ 1 / (p - 1) := by
    exact one_div_le_one_div_of_le hp1 (by linarith)
  have hlinear : 1 + 716 / p ≤ 1 + (716 : ℝ) * (1 / (p - 1)) := by
    norm_num [div_eq_mul_inv] at hfrac ⊢
    nlinarith
  have hbernoulli :
      1 + (716 : ℝ) * (1 / (p - 1)) ≤
        (1 + 1 / (p - 1)) ^ (716 : ℕ) := by
    exact one_add_mul_le_pow
      (le_trans (by norm_num) (div_nonneg zero_le_one hp1.le)) 716
  calc
    1 + 716 / p ≤ 1 + (716 : ℝ) * (1 / (p - 1)) := hlinear
    _ ≤ (1 + 1 / (p - 1)) ^ (716 : ℕ) := hbernoulli
    _ = ((1 - p⁻¹)⁻¹) ^ 716 := by
      congr 1
      field_simp
      ring

lemma sixthLocalFactor_nonneg (p : ℝ) (hp : 2 ≤ p) :
    0 ≤ sixthLocalFactor p := by
  rw [sixthLocalFactor]
  apply add_nonneg zero_le_one
  exact Finset.sum_nonneg fun j _ ↦ div_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by positivity) _))
    (pow_nonneg (by linarith) _)

/-- Product form of the local estimate.  This is the exact Euler-product
factor that is passed to the weak Mertens bound. -/
lemma sixthLocalFactor_prod_le (P : Finset ℕ)
    (hP : ∀ p ∈ P, 2 ≤ p) :
    ∏ p ∈ P, sixthLocalFactor p ≤
      (∏ p ∈ P, inverseEulerFactor p) ^ 716 := by
  calc
    ∏ p ∈ P, sixthLocalFactor p ≤
        ∏ p ∈ P, (inverseEulerFactor p) ^ 716 := by
          refine Finset.prod_le_prod ?_ ?_
          · intro p hpP
            exact sixthLocalFactor_nonneg p (by exact_mod_cast hP p hpP)
          · intro p hpP
            have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hP p hpP
            exact (sixthLocalFactor_le p hpR).trans <| by
              simpa [inverseEulerFactor] using
                one_add_716_div_le_inverseEuler_pow (p : ℝ) hpR
    _ = (∏ p ∈ P, inverseEulerFactor p) ^ 716 := by
          rw [Finset.prod_pow]

/-- The complete local divisor product has the required fixed log-power
bound for a smooth squarefree modulus. -/
theorem exists_sixthLocalFactor_prod_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {s h : ℕ}, 1 ≤ h →
      (∀ p ∈ s.primeFactors, p ≤ h) →
      ∏ p ∈ s.primeFactors, sixthLocalFactor p ≤
        (C * Real.log (2 * (h : ℝ))) ^ 716 := by
  obtain ⟨C, hC, hbound⟩ := partial_euler_product_le_log_two_mul
  refine ⟨C, hC, ?_⟩
  intro s h hh hsmooth
  calc
    ∏ p ∈ s.primeFactors, sixthLocalFactor p ≤
        (∏ p ∈ s.primeFactors, inverseEulerFactor p) ^ 716 := by
          apply sixthLocalFactor_prod_le
          intro p hp
          exact (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ (partial_euler_product h) ^ 716 := by
          apply pow_le_pow_left₀
          · exact Finset.prod_nonneg fun p hp ↦ by
              exact zero_le_one.trans <| by
                simpa [inverseEulerFactor] using one_le_inverse_prime_factor
                  (Nat.prime_of_mem_primeFactors hp)
          · simpa [inverseEulerFactor] using
              primeFactors_inverse_product_le_partial_euler_product hsmooth
    _ ≤ (C * Real.log (2 * (h : ℝ))) ^ 716 := by
          exact pow_le_pow_left₀
            ((by norm_num : (0 : ℝ) ≤ 1).trans partial_euler_trivial_lower_bound)
            (hbound h hh) 716

/-! ## Finite sixth-moment Markov inequality -/

/-- Counting Markov inequality at half the mean, in the denominator-free
form used in the small-prime argument. -/
lemma sixth_moment_lower_tail {X : Type*} (S : Finset X) (f : X → ℝ)
    {μ : ℝ} (hμ : 0 ≤ μ) :
    ((S.filter fun x ↦ f x < μ / 2).card : ℝ) * μ ^ 6 ≤
      64 * ∑ x ∈ S, |f x - μ| ^ 6 := by
  classical
  have hpoint (x : X) (hx : x ∈ S) (hbad : f x < μ / 2) :
      μ ^ 6 ≤ 64 * |f x - μ| ^ 6 := by
    have hdist : μ / 2 ≤ |f x - μ| := by
      rw [abs_of_nonpos]
      · linarith
      · linarith
    have hhalf : 0 ≤ μ / 2 := by positivity
    have hp := pow_le_pow_left₀ hhalf hdist 6
    nlinarith
  calc
    ((S.filter fun x ↦ f x < μ / 2).card : ℝ) * μ ^ 6 =
        ∑ x ∈ S.filter (fun x ↦ f x < μ / 2), μ ^ 6 := by simp
    _ ≤ ∑ x ∈ S.filter (fun x ↦ f x < μ / 2),
        64 * |f x - μ| ^ 6 := by
          exact Finset.sum_le_sum fun x hx ↦
            hpoint x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2
    _ ≤ ∑ x ∈ S, 64 * |f x - μ| ^ 6 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
          intro x hxS hx
          positivity
    _ = 64 * ∑ x ∈ S, |f x - μ| ^ 6 := by
          rw [Finset.mul_sum]

/-! ## Absorbing powers of `log` -/

/-- An explicit form of the one-variable bound
`log(2h)^L / h ≤ 2 L^L`.  This is exactly the estimate needed after
the sixth-moment Markov step. -/
lemma log_two_mul_pow_le (L h : ℕ) (hL : 0 < L) (hh : 0 < h) :
    Real.log (2 * (h : ℝ)) ^ L ≤
      2 * (L : ℝ) ^ L * h := by
  have hx0 : 0 ≤ (2 : ℝ) * h := by positivity
  have hx1 : 1 ≤ (2 : ℝ) * h := by
    norm_cast
    omega
  have hlog0 : 0 ≤ Real.log ((2 : ℝ) * h) := Real.log_nonneg hx1
  have hL0 : 0 ≤ (L : ℝ) := by positivity
  have hLi : 0 < ((L : ℝ)⁻¹) := inv_pos.mpr (by positivity)
  have hbase := Real.log_le_rpow_div hx0 hLi
  have hbase' :
      Real.log ((2 : ℝ) * h) ≤
        (L : ℝ) * (((2 : ℝ) * h) ^ ((L : ℝ)⁻¹)) := by
    convert hbase using 1
    all_goals field_simp
  have hpow := pow_le_pow_left₀ hlog0 hbase' L
  calc
    Real.log (2 * (h : ℝ)) ^ L
        ≤ ((L : ℝ) * (((2 : ℝ) * h) ^ ((L : ℝ)⁻¹))) ^ L := hpow
    _ = (L : ℝ) ^ L * ((2 : ℝ) * h) := by
          rw [mul_pow]
          congr 1
          simpa using Real.rpow_inv_natCast_pow hx0 hL.ne'
    _ = 2 * (L : ℝ) ^ L * h := by ring

/-- Division form of `log_two_mul_pow_le`. -/
lemma log_two_mul_pow_div_le (L h : ℕ) (hL : 0 < L) (hh : 0 < h) :
    Real.log (2 * (h : ℝ)) ^ L / h ≤ 2 * (L : ℝ) ^ L := by
  rw [div_le_iff₀ (Nat.cast_pos.mpr hh)]
  simpa [mul_assoc] using log_two_mul_pow_le L h hL hh

/-! ## Exact small-prime interface and its lower-tail consequence -/

/-- The unnormalised sixth centered moment of the number of units in an
interval. -/
noncomputable def centeredSixthMoment (s h : ℕ) : ℝ :=
  ∑ u ∈ Finset.range s,
    |(unitCount s h u : ℝ) - (h : ℝ) * density s| ^ 6

/-- The exact quantitative assertion proved by the smooth-modulus Fourier
argument.  It is named separately so the analytic input and its elementary
consequences have a stable interface. -/
def SmallPrimeSixthMomentBound (A : ℝ) : Prop :=
  0 < A ∧ ∀ {s h : ℕ}, 0 < s → Squarefree s → 1 ≤ h →
    (∀ p ∈ s.primeFactors, p ≤ h) →
    centeredSixthMoment s h ≤
      A * s * ((h : ℝ) * density s) ^ 3 *
        Real.log (2 * (h : ℝ)) ^ 1432

/-- Cancelling the positive cube of the mean after applying finite Markov. -/
lemma lower_tail_mul_mean_cube_le_of_sixthMoment
    {s h : ℕ} (hs : 0 < s) (hh : 0 < h) {A : ℝ}
    (hmoment : centeredSixthMoment s h ≤
      A * s * ((h : ℝ) * density s) ^ 3 *
        Real.log (2 * (h : ℝ)) ^ 1432) :
    (((Finset.range s).filter fun u ↦
        (unitCount s h u : ℝ) < (h : ℝ) * density s / 2).card : ℝ) *
          ((h : ℝ) * density s) ^ 3 ≤
      64 * A * s * Real.log (2 * (h : ℝ)) ^ 1432 := by
  let μ : ℝ := (h : ℝ) * density s
  have hμ : 0 < μ := mul_pos (Nat.cast_pos.mpr hh) (density_pos hs)
  have hmarkov := sixth_moment_lower_tail (Finset.range s)
    (fun u ↦ (unitCount s h u : ℝ)) hμ.le
  have htotal :
      ((((Finset.range s).filter fun u ↦
          (unitCount s h u : ℝ) < μ / 2).card : ℝ) * μ ^ 6) ≤
        64 * (A * s * μ ^ 3 * Real.log (2 * (h : ℝ)) ^ 1432) :=
    hmarkov.trans (mul_le_mul_of_nonneg_left hmoment (by norm_num))
  change ((((Finset.range s).filter fun u ↦
      (unitCount s h u : ℝ) < μ / 2).card : ℝ) * μ ^ 3) ≤
    64 * A * s * Real.log (2 * (h : ℝ)) ^ 1432
  rw [← mul_le_mul_iff_right₀ (pow_pos hμ 3)]
  calc
    μ ^ 3 * ((((Finset.range s).filter fun u ↦
        (unitCount s h u : ℝ) < μ / 2).card : ℝ) * μ ^ 3) =
        (((Finset.range s).filter fun u ↦
          (unitCount s h u : ℝ) < μ / 2).card : ℝ) * μ ^ 6 := by ring
    _ ≤ 64 * (A * s * μ ^ 3 * Real.log (2 * (h : ℝ)) ^ 1432) := htotal
    _ = μ ^ 3 * (64 * A * s * Real.log (2 * (h : ℝ)) ^ 1432) := by ring

/-- The sixth centered-moment assertion implies an `s / h²` bound for
the residues at which the smooth count falls below half its mean. -/
theorem smallPrime_lowerTail_of_sixthMomentBound {A : ℝ}
    (hA : SmallPrimeSixthMomentBound A) :
    ∃ B : ℝ, 0 < B ∧ ∀ {s h : ℕ}, 0 < s → Squarefree s → 1 ≤ h →
      (∀ p ∈ s.primeFactors, p ≤ h) →
      (((Finset.range s).filter fun u ↦
        (unitCount s h u : ℝ) < (h : ℝ) * density s / 2).card : ℝ) * h ^ 2 ≤
          B * s := by
  obtain ⟨C, hC, hMertens⟩ := exists_smooth_le_log_mul_totient
  have hApos : 0 < A := hA.1
  let B : ℝ := 128 * A * C ^ 3 * (1435 : ℝ) ^ 1435
  have hB : 0 < B := by
    dsimp [B]
    positivity
  refine ⟨B, hB, ?_⟩
  intro s h hs hsquare hh hsmooth
  let bad : ℝ := (((Finset.range s).filter fun u ↦
    (unitCount s h u : ℝ) < (h : ℝ) * density s / 2).card : ℝ)
  let L : ℝ := Real.log (2 * (h : ℝ))
  have hbad : 0 ≤ bad := by dsimp [bad]; positivity
  have hL : 0 ≤ L := by
    dsimp [L]
    exact Real.log_nonneg (by norm_cast; omega)
  have htail : bad * ((h : ℝ) * density s) ^ 3 ≤
      64 * A * s * L ^ 1432 := by
    dsimp [bad, L]
    exact lower_tail_mul_mean_cube_le_of_sixthMoment hs (by omega)
      (hA.2 hs hsquare hh hsmooth)
  have hM := hMertens hs hh hsmooth
  have hsR : (0 : ℝ) < s := Nat.cast_pos.mpr hs
  have hscale₁ : 1 ≤ C * L * density s := by
    rw [density]
    rw [show C * L * ((s.totient : ℝ) / s) =
      (C * L * (s.totient : ℝ)) / s by ring]
    rw [le_div_iff₀ hsR]
    dsimp [L]
    simpa [mul_assoc] using hM
  have hscale : 1 ≤ C ^ 3 * L ^ 3 * density s ^ 3 := by
    have := pow_le_pow_left₀ zero_le_one hscale₁ 3
    nlinarith
  have hlog := log_two_mul_pow_le 1435 h (by norm_num) (by omega)
  have hpre : bad * (h : ℝ) ^ 3 ≤ B * s * h := by
    calc
      bad * (h : ℝ) ^ 3 ≤
          (bad * (h : ℝ) ^ 3) *
            (C ^ 3 * L ^ 3 * density s ^ 3) := by
              exact le_mul_of_one_le_right (mul_nonneg hbad (by positivity)) hscale
      _ = C ^ 3 * L ^ 3 *
          (bad * ((h : ℝ) * density s) ^ 3) := by ring
      _ ≤ C ^ 3 * L ^ 3 * (64 * A * s * L ^ 1432) := by
          exact mul_le_mul_of_nonneg_left htail
            (mul_nonneg (pow_nonneg hC.le 3) (pow_nonneg hL 3))
      _ = 64 * A * C ^ 3 * s * L ^ 1435 := by ring
      _ ≤ 128 * A * C ^ 3 * (1435 : ℝ) ^ 1435 * s * h := by
          have hnonneg : 0 ≤ 64 * A * C ^ 3 * s := by
            positivity
          calc
            64 * A * C ^ 3 * s * L ^ 1435 ≤
                (64 * A * C ^ 3 * s) *
                  (2 * (1435 : ℝ) ^ 1435 * h) :=
              mul_le_mul_of_nonneg_left hlog hnonneg
            _ = 128 * A * C ^ 3 * (1435 : ℝ) ^ 1435 * s * h := by
              rw [show (128 : ℝ) = 64 * 2 by norm_num]
              ac_rfl
      _ = B * s * h := by rfl
  rw [← mul_le_mul_iff_right₀ (Nat.cast_pos.mpr (by omega : 0 < h))]
  change (h : ℝ) * (bad * (h : ℝ) ^ 2) ≤ (h : ℝ) * (B * s)
  calc
    (h : ℝ) * (bad * (h : ℝ) ^ 2) = bad * (h : ℝ) ^ 3 := by ring
    _ ≤ B * s * h := hpre
    _ = (h : ℝ) * (B * s) := by ring

end Erdos220
